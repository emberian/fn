; fn: the exec open of the paged checkpoint (lane s-pck-host, 2026-10-07;
; STORAGE-PROGRAM-20261006.md section 3.3, phase 2c-1).
;
; The model.  `fn-pck-capture-of-pages' (paged-checkpoint.lisp) decodes a page
; list into a capture C: the records (wire trees) from the events tape, the
; four fold roots (cpr, identity, consumer, topic) from the root region, the
; event index rebuilt from the records.  The host does not hold trees: it holds
; ROWS interned in the payload arena (books/store-intern.lisp, `fn-row-wire-of'
; reads a row's wire back) and the four roots.
;
; The exec.  `fn-pck-x-open NPG pgs-mem fn-arena fn-octets' reads the NPG-page
; image in `pgs-mem' word by word through `pcko-w' (the only reader; every call
; site counts its read): the root row from words 0 .. 8*2048, then the events
; tape from word 8*2048 to NPG*2048, one record at a time -- the tag word 1, the
; octet count, the packed octets into the buffer `fn-octets' (`pcko-copy', a
; record that crosses a page boundary is read through the contiguous word
; array), the tree decoded from the buffer, and interned with `fn-ssr-intern-step'
; (:resident) into `fn-arena', until a word that is not the tag.  No whole-tape
; word list, no page list.  The intern fold starts from `fn-stxk-initial-context
; 0', the seed of the host's full recovery (books/statement-recover-stream.lisp,
; fn-ssr-recovery-rows-are-the-raw-rows-without-snapshots), so the rows are the
; ones a replay of the same records makes.
; Answer: (mv VERDICT ROWS ROOTS INDEX READS fn-arena fn-octets), VERDICT :ok or
; a refusal by name (:root, :record, :intern, :truncated).
;
; THE KEYSTONES.
;   fn-pck-x-open-is-the-capture    for the writer's pages of (configs recs), the
;       open answers :ok, the arena rows read back as the capture's records, the
;       roots and the index are the capture's.
;   fn-pck-x-open-reads-bound       the words read are at most 8*2048 + the tape's
;       own words + 1 (the root row, the tape once, the one word that is not a
;       tag): no term in the store, the arena, the prefix or the page count.
; Scope, named.  (1) The last premise (the records intern from the initial
; identity context without a refusal) is owed PCK-OPEN-INTERN-NOT-BAD: it is a
; property of the history, not of the encoding.  (2) The image is given by its
; words (`pgs-x-words' equals the flattened pages); that the host filled and
; verified the pages is the driver's (2c-2).  (3) The tree is decoded from the
; buffer through `fn-octets-list' (one transient octet list per record, the
; residual PCK-OPEN-DECODE-LIST).  (4) Equations over the logic of the stobjs.

(in-package "ACL2")
(include-book "pagestore-exec")
(include-book "paged-checkpoint")
(include-book "store-checkpoint-buffer")
(include-book "statement-recover-stream")
(include-book "payload-extent")
(include-book "checkpoint-payloads-extent")
(include-book "consumer-event-index")
(local (include-book "arithmetic/top" :dir :system))

;; Certified inside the owner image (owner@books:books/owner), store-records-field's
;; export theory leaves the proto ADT libraries' rules and executable counterparts
;; disabled (history-records-disk loads them between its theory labels), so ground
;; terms such as (adt-octets-kind-p '(:octets)) never evaluate here.  Executable
;; counterparts are enabled for this book as in the plain world; the root is lane
;; theory-order's (C), which removes this event.
(local (in-theory (union-theories (current-theory :here) (executable-counterpart-theory :here))))

; Inherited rules that loop on a symbolic length.

; -----------------------------------------------------------------------------
; The exec.  Every word of the image is read by `pcko-w' at the call site that
; also counts it (the READS threaded through), so the returned count is the
; number of words the open read.

(defun pcko-w (i pgs-mem)
  (declare (xargs :stobjs pgs-mem :guard (and (natp i) (< i (pgs-x-len 0 pgs-mem)))))
  (pgs-x-word 0 i pgs-mem))

(defun pcko-copy (pos n reads pgs-mem fn-octets)
  ; The N octets of the payload words from POS on into the buffer, eight to a
  ; word, the last word's low octets (`adt-tp-unpack').
  (declare (xargs :stobjs (pgs-mem fn-octets)
                  :measure (nfix n)
                  :guard (and (natp pos) (natp n) (natp reads)
                              (<= (+ pos (floor (+ n 7) 8)) (pgs-x-len 0 pgs-mem))
                              (fn-octets-p fn-octets))
                  :verify-guards nil))
  (if (and (natp n) (< 0 n))
      (let ((fn-octets (fn-octets-append-word (pcko-w pos pgs-mem) (min n 8) fn-octets)))
        (pcko-copy (1+ pos) (nfix (- n 8)) (1+ reads) pgs-mem fn-octets))
    (mv reads fn-octets)))

(defun pcko-nw (n)
  ; The words N octets take.
  (declare (xargs :guard (natp n)))
  (floor (+ n 7) 8))

(defun pcko-nth (i x)
  ; Field I of the root tree (a list of the four fold roots).
  (declare (xargs :guard (natp i)))
  (if (true-listp x) (nth i x) nil))

(defun pcko-tree (fn-octets)
  ; The tree the buffer's program decodes to, or :refused.
  (declare (xargs :stobjs fn-octets :guard (fn-octets-p fn-octets) :verify-guards nil))
  (let ((d (fn-scc-decode-tree (fn-octets-list fn-octets))))
    (if (and (consp d) (eq (car d) :ok) (consp (cdr d))) (list :ok (cadr d)) :refused)))

(defun pcko-recp (tree)
  ; The row's metadata tree is a record's: tagged :r around the held row (handle 0).
  (declare (xargs :guard t))
  (and (consp tree) (eq (car tree) :r) (consp (cdr tree)) (fn-held-p (cadr tree))))

(defun pcko-ev (tree)
  ; The event the metadata names with no payload to join (fn-pck-join's other arm).
  (declare (xargs :guard t))
  (if (and (consp tree) (consp (cdr tree))) (cadr tree) nil))

(defun pcko-reseat (row h)
  ; The held row ROW with handle H.
  (declare (xargs :guard (fn-held-p row)))
  (fn-held-make (fn-record-sequence row) (fn-record-txid row) (fn-record-generation row)
                (fn-record-msgid row) h (fn-record-groups row) (fn-record-obligation-id row)
                (fn-record-content-subject row) (fn-record-release-evidence row)
                (fn-record-charge row) (fn-record-stamp row) (fn-held-facts row)
                (fn-held-context row) (fn-held-numbers row) (fn-held-withdrawn row)))

(defun pcko-ref-step (acc tree off len d0 d1 d2 d3 fid fn-arena)
  ; One tape row interned.  A record row is sealed BY REF: its arena entry is the
  ; extent of the payload file FID at the row's ref (the frame starts 37 octets
  ; before the payload, the protected prefix is header and payload, the trailer
  ; the row's four words) and its held row is the one the tape carries (facts and
  ; context decided at the writer), with the handle the seal returns; no payload
  ; octet is read.  Any other row interns its event as before.  (mv acc fn-arena).
  (declare (xargs :stobjs fn-arena :verify-guards nil
                  :guard (and (fn-ssr-statep acc) (natp fid) (natp off) (natp len)
                              (natp d0) (natp d1) (natp d2) (natp d3))
                  :guard-hints (("Goal" :in-theory (e/d (fn-arn-extent-guardp) (fn-arx-trailer-nat fn-cpl-unpack-words))))))
  (if (pcko-recp tree)
      (if (<= 37 off)
          (let* ((h (fn-arena-count fn-arena))
                 (row (pcko-reseat (cadr tree) h))
                 (fn-arena (fn-arena-seal-extent fid (- off 37) (+ len 37) off len
                                                 (fn-arx-trailer-nat (fn-cpl-unpack-words (list d0 d1 d2 d3))) fn-arena))
                 (identity (fn-replay-identity-step (fn-ssr-at 3 acc) row)))
            (if (equal (fn-stxk-context-kind identity) :ok)
                (mv (fn-ssr-publish acc row row identity) fn-arena)
              (mv :bad fn-arena)))
        (mv :bad fn-arena))
    (fn-ssr-intern-step acc (list (pcko-ev tree)) nil nil :resident nil fn-arena)))

(verify-guards pcko-ref-step)

(defthm pcko-intern-bad-is-absorbing
  (equal (fn-ssr-intern-step :bad ws rs ps mode dicts fn-arena) (mv :bad fn-arena))
  :hints (("Goal" :in-theory (enable fn-ssr-intern-step))))

(defthm pcko-intern-nil
  (equal (fn-ssr-intern-step acc nil rs ps mode dicts fn-arena) (mv acc fn-arena))
  :hints (("Goal" :in-theory (enable fn-ssr-intern-step))))

(defthm pcko-intern-cons
  (implies (syntaxp (not (equal ts ''nil)))
   (equal (fn-ssr-intern-step acc (cons x ts) nil nil :resident nil fn-arena)
         (mv-let (mid fn-arena)
           (fn-ssr-intern-step acc (list x) nil nil :resident nil fn-arena)
           (fn-ssr-intern-step mid ts nil nil :resident nil fn-arena))))
  :hints (("Goal" :use ((:instance fn-ssr-resident-step-of-append (a (list x)) (b ts) (dicts nil)))
           :in-theory (disable fn-ssr-resident-step-of-append))))

(defthm pcko-intern-statep
  (implies (and (fn-ssr-statep acc)
                (not (eq (car (fn-ssr-intern-step acc ws rs ps mode dicts fn-arena)) :bad)))
           (fn-ssr-statep (car (fn-ssr-intern-step acc ws rs ps mode dicts fn-arena))))
  :hints (("Goal" :use fn-ssr-intern-step-preserves-statep
           :in-theory (disable fn-ssr-intern-step-preserves-statep))))

(defthm pcko-ref-step-statep
  (implies (and (fn-ssr-statep acc)
                (not (eq (mv-nth 0 (pcko-ref-step acc tree off len d0 d1 d2 d3 fid fn-arena)) :bad)))
           (fn-ssr-statep (mv-nth 0 (pcko-ref-step acc tree off len d0 d1 d2 d3 fid fn-arena))))
  :hints (("Goal" :in-theory (e/d (pcko-ref-step) (fn-ssr-intern-step fn-ssr-publish fn-replay-identity-step))
           :use ((:instance fn-ssr-publish-preserves-statep (row (pcko-reseat (cadr tree) (fn-arena-count fn-arena)))
                            (wire (pcko-reseat (cadr tree) (fn-arena-count fn-arena)))
                            (identity (fn-replay-identity-step (fn-ssr-at 3 acc) (pcko-reseat (cadr tree) (fn-arena-count fn-arena)))))
                 (:instance pcko-intern-statep (ws (list (pcko-ev tree))) (rs nil) (ps nil) (mode :resident) (dicts nil))))))

(defthm pcko-ref-step-statep-car
  (implies (and (fn-ssr-statep acc)
                (not (eq (car (pcko-ref-step acc tree off len d0 d1 d2 d3 fid fn-arena)) :bad)))
           (fn-ssr-statep (car (pcko-ref-step acc tree off len d0 d1 d2 d3 fid fn-arena))))
  :hints (("Goal" :use pcko-ref-step-statep :in-theory (disable pcko-ref-step-statep pcko-ref-step))))

(defun pcko-tape (pos lim acc reads fid pgs-mem fn-arena fn-octets)
  ; The events tape from word POS to LIM: tag, octet count, packed metadata
  ; octets, then the ref (offset, length) and the trailer words, one row at a
  ; time, until a word that is not the tag.
  ; (mv verdict acc reads fn-arena fn-octets).  No event index is built: the
  ; Store's index is retired (books/store-node.lisp, field 13), and nothing on the
  ; served path reads it.
  (declare (xargs :stobjs (pgs-mem fn-arena fn-octets)
                  :measure (nfix (- (nfix lim) (nfix pos)))
                  :guard (and (natp pos) (natp lim) (natp reads) (natp fid)
                              (<= lim (pgs-x-len 0 pgs-mem))
                              (fn-ssr-statep acc)
                              (fn-octets-p fn-octets))
                  :verify-guards nil))
  (if (and (natp pos) (natp lim) (< pos lim))
      (if (eql (pcko-w pos pgs-mem) 1)
          (if (< (+ pos 1) lim)
              (let* ((n (nfix (pcko-w (+ pos 1) pgs-mem)))
                     (nw (pcko-nw n))
                     (tl (+ pos 2 nw))
                     (npos (+ tl 6)))
                (if (<= npos lim)
                    (let ((fn-octets (fn-octets-clear fn-octets)))
                      (mv-let (reads fn-octets)
                        (pcko-copy (+ pos 2) n (+ reads 2) pgs-mem fn-octets)
                        (let ((d (pcko-tree fn-octets)))
                          (if (eq d :refused)
                              (mv :record acc reads fn-arena fn-octets)
                            (mv-let (acc2 fn-arena)
                              (pcko-ref-step acc (cadr d) (pcko-w tl pgs-mem) (pcko-w (+ tl 1) pgs-mem)
                                             (pcko-w (+ tl 2) pgs-mem) (pcko-w (+ tl 3) pgs-mem)
                                             (pcko-w (+ tl 4) pgs-mem) (pcko-w (+ tl 5) pgs-mem)
                                             fid fn-arena)
                              (if (eq acc2 :bad)
                                  (mv :intern acc2 (+ reads 6) fn-arena fn-octets)
                                (pcko-tape npos lim acc2
                                           (+ reads 6) fid
                                           pgs-mem fn-arena fn-octets)))))))
                  (mv :truncated acc (+ reads 2) fn-arena fn-octets)))
            (mv :truncated acc (+ reads 1) fn-arena fn-octets))
        (mv :ok acc (+ reads 1) fn-arena fn-octets))
    (mv :ok acc reads fn-arena fn-octets)))

(defun fn-pck-x-open (npg pgs-mem fid fn-arena fn-octets)
  ; The open of the NPG-page image in PGS-MEM against the payload file FID: the
  ; root row from words 0 .. 8*2048, then the events tape from word 8*2048 to
  ; NPG*2048, row by row.
  ; (mv VERDICT ROWS ROOTS READS fn-arena fn-octets): VERDICT :ok or a
  ; refusal by name; ROWS the arena rows, ROOTS the four fold roots, READS the
  ; words read.
  (declare (xargs :stobjs (pgs-mem fn-arena fn-octets) :verify-guards nil))
  (if (and (natp npg) (<= 8 npg) (<= (* 2048 npg) (pgs-x-len 0 pgs-mem)) (natp fid)
           (eql (pcko-w 0 pgs-mem) 1))
      (let* ((n (nfix (pcko-w 1 pgs-mem)))
             (nw (pcko-nw n)))
        (if (<= (+ 2 nw) 16384)
            (let ((fn-octets (fn-octets-clear fn-octets)))
              (mv-let (reads fn-octets)
                (pcko-copy 2 n 2 pgs-mem fn-octets)
                (let ((d (pcko-tree fn-octets)))
                  (if (eq d :refused)
                      (mv :root nil nil reads fn-arena fn-octets)
                    (let ((root (cadr d)))
                      (mv-let (verdict acc reads fn-arena fn-octets)
                        (pcko-tape 16384 (* 2048 npg) (fn-ssr-seed (fn-stxk-initial-context 0)) reads fid
                                   pgs-mem fn-arena fn-octets)
                        (mv verdict (fn-ssr-rows acc)
                            (list (pcko-nth 0 root) (pcko-nth 1 root) (pcko-nth 2 root) (pcko-nth 3 root))
                            reads fn-arena fn-octets)))))))
          (mv :root nil nil 2 fn-arena fn-octets)))
    (mv :root nil nil (if (and (natp npg) (<= 8 npg) (<= (* 2048 npg) (pgs-x-len 0 pgs-mem))) 1 0)
        fn-arena fn-octets)))

; -----------------------------------------------------------------------------
; The image as a list, and the copy.

(defun pcko-img (w pgs-mem)
  (declare (xargs :stobjs pgs-mem :guard t :verify-guards nil))
  (equal (pgs-x-words 0 0 (len w) pgs-mem) w))

(defun pcko-ind (a k i)
  (if (zp i) (list a k) (pcko-ind (1+ a) (1- k) (1- i))))

(defthm pcko-nth-of-words
  (implies (and (natp a) (natp k) (natp i) (< i k))
           (equal (nth i (pgs-x-words 0 a k pgs-mem))
                  (pgs-x-word 0 (+ a i) pgs-mem)))
  :hints (("Goal" :induct (pcko-ind a k i)
           :expand ((pgs-x-words 0 a k pgs-mem)))))

(defthm pcko-w-is-nth
  (implies (and (pcko-img w pgs-mem) (natp i) (< i (len w)))
           (equal (pcko-w i pgs-mem) (nth i w)))
  :hints (("Goal" :use ((:instance pcko-nth-of-words (a 0) (k (len w))))
           :in-theory (e/d (pcko-img pcko-w) (pcko-nth-of-words))))
  :rule-classes ((:rewrite :match-free :all)))

(in-theory (disable pcko-w pcko-img))

(defthm pcko-unw-is-word-octets
  (equal (adt-tp-unw k w) (fn-oct-word-octets w k))
  :hints (("Goal" :in-theory (enable adt-tp-unw fn-oct-word-octets))))

(defthm pcko-npk-natp (natp (adt-tp-npk n))
  :hints (("Goal" :in-theory (enable adt-tp-npk)))
  :rule-classes (:rewrite :type-prescription))

(defthm pcko-unpack-step
  (implies (posp n)
           (equal (adt-tp-unpack n ws)
                  (append (adt-tp-unw (min n 8) (car ws))
                          (adt-tp-unpack (nfix (- n 8)) (cdr ws)))))
  :hints (("Goal" :expand ((adt-tp-unpack n ws)))))

(defthm pcko-npk-step
  (implies (posp n) (equal (adt-tp-npk n) (+ 1 (adt-tp-npk (nfix (- n 8))))))
  :hints (("Goal" :expand ((adt-tp-npk n)))))

(defthm pcko-car-nthcdr (equal (car (nthcdr i w)) (nth i w)))

(defthm pcko-unpack-zero (equal (adt-tp-unpack 0 ws) nil)
  :hints (("Goal" :expand ((adt-tp-unpack 0 ws)))))
(defthm pcko-npk-zero (equal (adt-tp-npk 0) 0)
  :hints (("Goal" :expand ((adt-tp-npk 0)))))

(defthm pcko-copy-is-unpack
  (implies (and (pcko-img w pgs-mem) (natp pos) (natp n) (natp reads) (true-listp buf)
                (<= (+ pos (adt-tp-npk n)) (len w)))
           (and (equal (mv-nth 0 (pcko-copy pos n reads pgs-mem buf))
                       (+ reads (adt-tp-npk n)))
                (equal (mv-nth 1 (pcko-copy pos n reads pgs-mem buf))
                       (append buf (adt-tp-unpack n (nthcdr pos w))))))
  :hints (("Goal" :induct (pcko-copy pos n reads pgs-mem buf)
           :in-theory (e/d (pcko-unpack-step pcko-npk-step) (nth nthcdr adt-tp-unpack adt-tp-npk)))))

(defthm pcko-copy-reads-car
  (implies (and (pcko-img w pgs-mem) (natp pos) (natp n) (natp reads) (true-listp buf)
                (<= (+ pos (adt-tp-npk n)) (len w)))
           (equal (car (pcko-copy pos n reads pgs-mem buf)) (+ reads (adt-tp-npk n))))
  :hints (("Goal" :use pcko-copy-is-unpack :in-theory (disable pcko-copy-is-unpack pcko-copy))))

(defthm pcko-copy-buf-cadr
  (implies (and (pcko-img w pgs-mem) (natp pos) (natp n) (natp reads) (true-listp buf)
                (<= (+ pos (adt-tp-npk n)) (len w)))
           (equal (cadr (pcko-copy pos n reads pgs-mem buf))
                  (append buf (adt-tp-unpack n (nthcdr pos w)))))
  :hints (("Goal" :use pcko-copy-is-unpack :in-theory (disable pcko-copy-is-unpack pcko-copy))))

(in-theory (disable pcko-unpack-step pcko-npk-step))

; -----------------------------------------------------------------------------
; The model of the tape.  L is the words from the tape's start; a row starts
; with the tag 1.

(defun pcko-ok-treep (d)
  (and (consp d) (eq (car d) :ok) (consp (cdr d))))

(defthm pcko-nw-is-npk
  (implies (natp n) (equal (pcko-nw n) (adt-tp-npk n)))
  :hints (("Goal" :induct (adt-tp-npk n)
           :in-theory (e/d (adt-tp-npk pcko-nw) ()))))

(in-theory (disable pcko-nw))

; -----------------------------------------------------------------------------
; Guards.

(defthm pcko-w-natp
  (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-x-len 0 pgs-mem)))
           (and (natp (pcko-w i pgs-mem)) (unsigned-byte-p 64 (pcko-w i pgs-mem))))
  :hints (("Goal" :in-theory (enable pcko-w) :use ((:instance pgs-u64-of-x-word (sel 0))))))

(defthm pcko-w-natp-w
  (implies (and (pgs-memp pgs-mem) (natp i) (< i (pgs-w-length pgs-mem)))
           (and (natp (pcko-w i pgs-mem)) (unsigned-byte-p 64 (pcko-w i pgs-mem))))
  :hints (("Goal" :in-theory (enable pcko-w pgs-x-len) :use ((:instance pgs-u64-of-x-word (sel 0))))))

(defthm pcko-floor-pos (implies (and (natp n) (< 0 n)) (< 0 (floor (+ 7 n) 8))))

(verify-guards pcko-copy)

(defthm pcko-copy-reads-natp
  (implies (natp reads) (natp (mv-nth 0 (pcko-copy pos n reads pgs-mem fn-octets))))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (pcko-copy pos n reads pgs-mem fn-octets))))

(defthm pcko-copy-reads-natp-car
  (implies (natp reads) (natp (car (pcko-copy pos n reads pgs-mem fn-octets))))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (pcko-copy pos n reads pgs-mem fn-octets))))

(defthm pcko-copy-preserves-octets
  (implies (and (fn-octets-p fn-octets) (natp n) (natp pos) (<= (+ pos (floor (+ n 7) 8)) (pgs-x-len 0 pgs-mem)))
           (and (fn-octets-p (mv-nth 1 (pcko-copy pos n reads pgs-mem fn-octets)))
                (fn-octets-p (cadr (pcko-copy pos n reads pgs-mem fn-octets)))))
  :hints (("Goal" :induct (pcko-copy pos n reads pgs-mem fn-octets))))

(defthm pcko-cbor-octets-adt
  (implies (fn-cbor-octet-listp x) (adt-octetsp x))
  :hints (("Goal" :induct (len x)
           :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp adt-octetsp))))

(defthm pcko-octets-p-scc
  (implies (fn-octets-p x) (fn-scc-octet-listp x))
  :hints (("Goal" :in-theory (e/d (fn-oct-octets-p-is-octet-listp pck-octet-listp-is-octetsp)
                                  ())
           :use pcko-cbor-octets-adt)))

(defthm pcko-floor-npk
  (implies (natp n) (equal (floor (+ 7 n) 8) (adt-tp-npk n)))
  :hints (("Goal" :use pcko-nw-is-npk :in-theory (enable pcko-nw))))

(verify-guards pcko-tree)

(defthm pcko-tree-of-list
  (equal (pcko-tree buf)
         (let ((d (fn-scc-decode-tree buf)))
           (if (pcko-ok-treep d) (list :ok (cadr d)) :refused)))
  :hints (("Goal" :in-theory (enable pcko-tree pcko-ok-treep fn-oct-list-is-identity))))

(in-theory (disable pcko-tree))

(verify-guards pcko-tape
  :hints (("Goal" :in-theory (disable pcko-ref-step pcko-w pcko-copy pcko-tree))))
(verify-guards fn-pck-x-open)

; -----------------------------------------------------------------------------
; The shape of the image the writer's pages flatten to.

(defthm pcko-pad-arith
  (implies (natp n) (equal (+ n (adt-tp-pad n)) (* 2048 (adt-tp-npages n))))
  :hints (("Goal" :induct (adt-tp-npages n)
           :in-theory (enable adt-tp-npages adt-tp-pad))))

(defun pcko-rw0 (tree)
  ; The root row's words: the root tree's program, and six zero columns.
  (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-root tree)))

(defthm pcko-rw0-true-listp (true-listp (pcko-rw0 tree)))

(in-theory (disable pcko-rw0))

(defthm pcko-flat-fit
  (implies (and (true-listp w) (<= (len (adt-tp-pages w)) 8))
           (and (<= (len w) 16384)
                (equal (adt-tp-flat (fn-pck-fit (adt-tp-pages w)))
                       (append w (adt-tp-zeros (- 16384 (len w)))))))
  :hints (("Goal" :do-not-induct t :do-not '(preprocess)
           :in-theory (e/d (fn-pck-fit adt-tp-len-pages)
                           (adt-tp-pages adt-tp-flat adt-tp-flat-of-pages pcko-pad-arith))
           :use ((:instance adt-tp-flat-of-pages)
                 (:instance pck-append-zeros (a (adt-tp-pad (len w)))
                            (b (* 2048 (- 8 (adt-tp-npages (len w))))))
                 (:instance pck-flat-zero-pages (n (- 8 (adt-tp-npages (len w)))))
                 (:instance pck-flat-append (p (adt-tp-pages w))
                            (q (fn-pck-zero-pages (- 8 (adt-tp-npages (len w))))))
                 (:instance pcko-pad-arith (n (len w)))))))

(defthm pcko-root-flat
  (implies (fn-pck-root-fitsp configs recs)
           (let ((rw0 (pcko-rw0 (fn-pck-root-tree configs recs))))
             (and (<= (len rw0) 16384)
                  (equal (adt-tp-flat (fn-pck-root-pages-of configs recs))
                         (append rw0 (adt-tp-zeros (- 16384 (len rw0))))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-root-pages-of fn-pck-root-pages-of-tree
                            fn-pck-root-fitsp fn-pck-root-fitsp-tree
                            fn-pck-row-pages-of adt-tp-pages-of adt-tp-seq-words pcko-rw0)
                           (adt-tp-pages adt-tp-flat adt-tp-flat-of-pages pcko-flat-fit))
           :use ((:instance pcko-flat-fit (w (adt-tp-rw *fn-pck-row-schema*
                                                        (fn-pck-enc-root (fn-pck-root-tree configs recs)))))))))


(defun pcko-tws (recs) (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows recs)))
(defthm pcko-tws-true-listp (true-listp (pcko-tws recs)))

(defthm pcko-flat-pages
  (implies (fn-pck-root-fitsp configs recs)
           (let* ((rw0 (pcko-rw0 (fn-pck-root-tree configs recs)))
                  (tw (pcko-tws recs)))
             (equal (adt-tp-flat (fn-pck-pages configs recs))
                    (append rw0 (adt-tp-zeros (- 16384 (len rw0)))
                            tw (adt-tp-zeros (adt-tp-pad (len tw)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-pages fn-pck-row-pages-of adt-tp-pages-of pcko-tws)
                           (adt-tp-pages adt-tp-flat adt-tp-flat-of-pages pcko-root-flat fn-pck-root-pages-of))
           :use ((:instance pcko-root-flat)
                 (:instance pck-flat-append (p (fn-pck-root-pages-of configs recs))
                            (q (adt-tp-pages (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows recs)))))
                 (:instance adt-tp-flat-of-pages (w (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows recs))))))))

(defthm pcko-len-pages
  (implies (fn-pck-root-fitsp configs recs)
           (equal (len (fn-pck-pages configs recs))
                  (+ 8 (adt-tp-npages (len (pcko-tws recs))))))
  :hints (("Goal" :in-theory (e/d (fn-pck-pages fn-pck-row-pages-of adt-tp-pages-of pcko-tws adt-tp-len-pages)
                                  (adt-tp-pages)))))

(defthm pcko-nthcdr-16384
  (implies (and (true-listp rw0) (<= (len rw0) 16384))
           (equal (nthcdr 16384 (append rw0 (adt-tp-zeros (- 16384 (len rw0))) rest)) rest))
  :hints (("Goal" :use ((:instance pck-nthcdr-root (r (append rw0 (adt-tp-zeros (- 16384 (len rw0))))) (c rest)))
           :in-theory (disable pck-nthcdr-root nthcdr (:executable-counterpart nthcdr) adt-tp-zeros (:executable-counterpart adt-tp-zeros)))))

(defthm pcko-len-w-gen
  (implies (and (true-listp rw0) (<= (len rw0) 16384) (true-listp tw))
           (equal (len (append rw0 (adt-tp-zeros (- 16384 (len rw0))) tw (adt-tp-zeros (adt-tp-pad (len tw)))))
                  (+ 16384 (* 2048 (adt-tp-npages (len tw))))))
  :hints (("Goal" :use ((:instance pcko-pad-arith (n (len tw)))))))

(defthm pcko-len-w
  (implies (fn-pck-root-fitsp configs recs)
           (equal (len (adt-tp-flat (fn-pck-pages configs recs)))
                  (* 2048 (len (fn-pck-pages configs recs)))))
  :hints (("Goal" :in-theory (disable pcko-flat-pages pcko-len-w-gen pcko-len-pages pcko-root-flat
                                      pcko-rw0 pcko-tws adt-tp-rw fn-pck-pages)
           :use ((:instance pcko-flat-pages) (:instance pcko-len-pages)
                 (:instance pcko-root-flat)
                 (:instance pcko-len-w-gen (rw0 (pcko-rw0 (fn-pck-root-tree configs recs)))
                            (tw (pcko-tws recs)))))))

(defthm pcko-w-tape
  (implies (fn-pck-root-fitsp configs recs)
           (equal (nthcdr 16384 (adt-tp-flat (fn-pck-pages configs recs)))
                  (append (pcko-tws recs) (adt-tp-zeros (adt-tp-pad (len (pcko-tws recs)))))))
  :hints (("Goal" :in-theory (e/d () (pcko-flat-pages pcko-nthcdr-16384 fn-pck-pages pcko-rw0 pcko-tws))
           :use ((:instance pcko-flat-pages)
                 (:instance pcko-root-flat)
                 (:instance pcko-nthcdr-16384 (rw0 (pcko-rw0 (fn-pck-root-tree configs recs)))
                            (rest (append (pcko-tws recs) (adt-tp-zeros (adt-tp-pad (len (pcko-tws recs)))))))))))


; =============================================================================
; THE PROOFS.  The tape's rows are the model's rows (fn-pck-rows-from); each
; interned by `pcko-ref-step' leaves the state full recovery's intern leaves.

; -----------------------------------------------------------------------------
; The held row the tape carries, reseated at the arena's count, is the row full
; recovery interns there.

(defthm pcko-reseat-held-p
  (implies (and (fn-held-p row) (natp h)) (fn-held-p (pcko-reseat row h)))
  :hints (("Goal" :in-theory (enable pcko-reseat fn-held-p fn-held-internals fn-record-internals fn-record-uint64p)
           :use ((:instance fn-held-p-fields (h row))))))

(defthm pcko-intern-row-at-reseat
  (implies (and (fn-record-p w) (natp h))
           (equal (fn-intern-row-at w k g h)
                  (pcko-reseat (fn-intern-row-at w k g 0) h)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (pcko-reseat fn-intern-row-at) ()))))

(defthm pcko-held-not-hstxa
  (implies (fn-held-p e) (not (fn-hstxa-p e)))
  :hints (("Goal" :use (fn-hstxa-p-forward-shape fn-held-p-forward-natural-head)
           :in-theory (disable fn-hstxa-p-forward-shape fn-held-p-forward-natural-head))))

(defthm pcko-identity-wire-of-held
  (implies (fn-held-p e) (equal (fn-replay-identity-wire e) e))
  :hints (("Goal" :in-theory (enable fn-replay-identity-wire))))

(defthm pcko-identity-step-of-held
  (implies (fn-held-p e)
           (equal (fn-replay-identity-step ctx e)
                  (if (not (equal (fn-stxk-context-kind ctx) :ok)) ctx
                    (if (not (equal (fn-record-sequence e) (fn-stxk-context-next ctx)))
                        (fn-stxk-fault ctx :sequence)
                      (fn-replay-identity-advance ctx)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-replay-identity-step fn-store-event-sequence)
                           (fn-held-p fn-hsig-article-event-carried-bindsp
                            fn-hsig-article-event-revoked-bindsp fn-stxk-fault fn-replay-identity-advance))
           :use ((:instance fn-held-is-no-wire-event (x e))))))

(defthm pcko-reseat-sequence
  (equal (fn-record-sequence (pcko-reseat row h)) (fn-record-sequence row))
  :hints (("Goal" :in-theory (enable pcko-reseat))))

(defthm pcko-identity-of-reseat
  (implies (and (fn-held-p row) (natp h))
           (equal (fn-replay-identity-step ctx (pcko-reseat row h))
                  (fn-replay-identity-step ctx row)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable pcko-reseat pcko-identity-step-of-held fn-held-p)
           :use (pcko-reseat-held-p
                 (:instance pcko-identity-step-of-held (e row))
                 (:instance pcko-identity-step-of-held (e (pcko-reseat row h)))
                 pcko-reseat-sequence))))

; -----------------------------------------------------------------------------
; One row of the tape.  The words from POS on are the row's words, then REST.

(defun pcko-rowwords (prog off len d0 d1 d2 d3)
  (cons 1 (cons (len prog) (append (adt-tp-pack prog) (list off len d0 d1 d2 d3)))))

(defthm pcko-nth-nthcdr
  (implies (and (natp i) (natp j)) (equal (nth i (nthcdr j w)) (nth (+ i j) w)))
  :hints (("Goal" :induct (nthcdr j w))))

(defthm pcko-nfix-len (equal (nfix (len x)) (len x)))

(defthm pcko-len-rowwords
  (implies (adt-octetsp prog)
           (equal (len (pcko-rowwords prog off len d0 d1 d2 d3)) (+ 8 (adt-tp-npk (len prog)))))
  :hints (("Goal" :use (:instance adt-tp-len-pack (o prog)) :in-theory (enable pcko-rowwords))))

(defthm pcko-rowwords-is-the-row
  (equal (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row w off st))
         (pcko-rowwords (fn-scc-program (fn-pck-meta w st)) (+ *fn-cpl-header-octets* off) (len (fn-pck-payload w))
                        (car (fn-cpl-trailer-words-impl (fn-pck-payload w))) (cadr (fn-cpl-trailer-words-impl (fn-pck-payload w)))
                        (caddr (fn-cpl-trailer-words-impl (fn-pck-payload w))) (cadddr (fn-cpl-trailer-words-impl (fn-pck-payload w)))))
  :hints (("Goal" :in-theory (e/d (fn-pck-enc-row adt-tp-rw adt-tp-fw adt-enc pcko-rowwords) (fn-pck-meta fn-pck-payload)))))

(defthm pcko-rw0-is
  (equal (pcko-rw0 x) (pcko-rowwords (fn-scc-program x) 0 0 0 0 0 0))
  :hints (("Goal" :in-theory (e/d (pcko-rw0 fn-pck-enc-root pcko-rowwords adt-tp-rw adt-tp-fw adt-enc) ()))))

(defthm pcko-nthcdr-rowwords-nth
  ; Field I of the words from POS on, when they are a row's words then REST.
  (implies (and (natp pos) (natp i)
                (equal (nthcdr pos w) (append (pcko-rowwords prog off len d0 d1 d2 d3) rest)))
           (equal (nth (+ pos i) w) (nth i (append (pcko-rowwords prog off len d0 d1 d2 d3) rest))))
  :rule-classes nil
  :hints (("Goal" :use (:instance pcko-nth-nthcdr (j pos)))))

(defthm pcko-len-append (equal (len (append x y)) (+ (len x) (len y))))

(defthm pcko-len-nthcdr-in
  (implies (and (natp pos) (<= pos (len w)))
           (equal (len (nthcdr pos w)) (- (len w) pos)))
  :hints (("Goal" :use (:instance adt-tp-len-nthcdr (n pos) (x w))
           :in-theory (e/d (nfix) (adt-tp-len-nthcdr)))))

(defthm pcko-nthcdr-room
  (implies (and (natp pos) (<= pos (len w)) (equal (nthcdr pos w) (append x rest)))
           (<= (+ pos (len x)) (len w)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance pcko-len-nthcdr-in) (:instance pcko-len-append (y rest)))
           :in-theory (disable pcko-len-nthcdr-in pcko-len-append)
           :do-not '(preprocess))))

(defthm pcko-nth-rowwords-head
  (and (equal (nth 0 (append (pcko-rowwords prog off len d0 d1 d2 d3) rest)) 1)
       (equal (nth 1 (append (pcko-rowwords prog off len d0 d1 d2 d3) rest)) (len prog)))
  :hints (("Goal" :in-theory (enable pcko-rowwords))))

(defthm pcko-nth-after
  (implies (and (true-listp a) (natp k))
           (equal (nth (+ (len a) k) (append a b)) (nth k b)))
  :hints (("Goal" :induct (len a))))

(defthm pcko-nth-two
  (implies (natp m) (equal (nth (+ 2 m) (cons x (cons y z))) (nth m z)))
  :hints (("Goal" :expand ((nth (+ 2 m) (cons x (cons y z))) (nth (+ 1 m) (cons y z))))))

(defthm pcko-true-listp-pack (true-listp (adt-tp-pack o))
  :hints (("Goal" :in-theory (enable adt-tp-pack))))

(defthm pcko-nth-rowwords-tail
  (implies (and (adt-octetsp prog) (natp k) (< k 6))
           (equal (nth (+ 2 (adt-tp-npk (len prog)) k) (append (pcko-rowwords prog off len d0 d1 d2 d3) rest))
                  (nth k (list off len d0 d1 d2 d3))))
  :hints (("Goal" :do-not-induct t
           :cases ((equal k 0) (equal k 1) (equal k 2) (equal k 3) (equal k 4) (equal k 5))
           :in-theory (e/d (pcko-rowwords) (pcko-nth-after pcko-nth-two))
           :use ((:instance adt-tp-len-pack (o prog))
                 (:instance pcko-nth-after (a (adt-tp-pack prog)) (b (list* off len d0 d1 d2 d3 rest)))
                 (:instance pcko-nth-two (m (+ (adt-tp-npk (len prog)) k)) (x 1) (y (len prog))
                            (z (append (adt-tp-pack prog) (list* off len d0 d1 d2 d3 rest))))))))

(defthm pcko-nthcdr-plus2
  (implies (natp pos) (equal (nthcdr (+ 2 pos) w) (cdr (cdr (nthcdr pos w)))))
  :rule-classes nil
  :hints (("Goal" :use (:instance pck-nthcdr-nthcdr (a 2) (b pos) (x w))
           :in-theory (disable pck-nthcdr-nthcdr))))

(defthm pcko-unpack-of-row
  (implies (and (adt-octetsp prog) (natp pos)
                (equal (nthcdr pos w) (append (pcko-rowwords prog off len d0 d1 d2 d3) rest)))
           (equal (adt-tp-unpack (len prog) (nthcdr (+ 2 pos) w)) prog))
  :hints (("Goal" :do-not-induct t
           :use ((:instance adt-tp-unpack-of-pack (o prog) (r (append (list off len d0 d1 d2 d3) rest)))
                 pcko-nthcdr-plus2)
           :in-theory (e/d (pcko-rowwords) (adt-tp-unpack-of-pack pgs-nthcdr-nthcdr pgs-cdr-nthcdr))))
  :rule-classes nil)

(defthm pcko-tape-row
  ; The tape reads a row whose words are at POS as the ref-step of its decoded
  ; metadata and its four ref/trailer fields, and goes on after it.
  (implies (and (pcko-img w pgs-mem) (natp pos) (<= pos (len w)) (natp reads)
                (adt-octetsp prog) (true-listp prog)
                (equal (nthcdr pos w) (append (pcko-rowwords prog off len d0 d1 d2 d3) rest))
                (pcko-ok-treep (fn-scc-decode-tree prog)))
           (equal (pcko-tape pos (len w) acc reads fid pgs-mem fn-arena fn-octets)
                  (mv-let (acc2 fn-arena)
                    (pcko-ref-step acc (cadr (fn-scc-decode-tree prog)) off len d0 d1 d2 d3 fid fn-arena)
                    (if (eq acc2 :bad)
                        (mv :intern acc2 (+ reads 8 (adt-tp-npk (len prog))) fn-arena prog)
                      (pcko-tape (+ pos 8 (adt-tp-npk (len prog))) (len w) acc2
                                 (+ reads 8 (adt-tp-npk (len prog))) fid pgs-mem fn-arena prog)))))
  :hints (("Goal" :do-not-induct t
           :expand ((pcko-tape pos (len w) acc reads fid pgs-mem fn-arena fn-octets))
           :in-theory (e/d () (pcko-tape pcko-ref-step nth nthcdr adt-tp-npk adt-tp-unpack fn-scc-decode-tree
                               pcko-rowwords pcko-copy pcko-tree pcko-w nfix pcko-nw))
           :use ((:instance pcko-len-rowwords)
                 (:instance pcko-nthcdr-room (x (pcko-rowwords prog off len d0 d1 d2 d3)))
                 (:instance pcko-nthcdr-rowwords-nth (i 0)) (:instance pcko-nthcdr-rowwords-nth (i 1))
                 (:instance pcko-nthcdr-rowwords-nth (i (+ 2 (adt-tp-npk (len prog)))))
                 (:instance pcko-nthcdr-rowwords-nth (i (+ 3 (adt-tp-npk (len prog)))))
                 (:instance pcko-nthcdr-rowwords-nth (i (+ 4 (adt-tp-npk (len prog)))))
                 (:instance pcko-nthcdr-rowwords-nth (i (+ 5 (adt-tp-npk (len prog)))))
                 (:instance pcko-nthcdr-rowwords-nth (i (+ 6 (adt-tp-npk (len prog)))))
                 (:instance pcko-nthcdr-rowwords-nth (i (+ 7 (adt-tp-npk (len prog)))))
                 (:instance pcko-nth-rowwords-tail (k 0)) (:instance pcko-nth-rowwords-tail (k 1))
                 (:instance pcko-nth-rowwords-tail (k 2)) (:instance pcko-nth-rowwords-tail (k 3))
                 (:instance pcko-nth-rowwords-tail (k 4)) (:instance pcko-nth-rowwords-tail (k 5))
                 pcko-nth-rowwords-head pcko-unpack-of-row)))
  :rule-classes nil)

;; -----------------------------------------------------------------------------
; The tape over the model's rows.  PCKO-SIM is what the tape does, row by row,
; read off the records: the ref-step of each record's metadata and ref fields.

(defun pcko-prog (w st) (declare (xargs :guard t :verify-guards nil)) (fn-scc-program (fn-pck-meta w st)))
(defun pcko-tw (w) (declare (xargs :guard t :verify-guards nil)) (fn-cpl-trailer-words-impl (fn-pck-payload w)))
(defun pcko-next-base (w base) (declare (xargs :guard t :verify-guards nil))
  (+ base (fn-cpl-frame-octets (len (fn-pck-payload w)))))

(defun pcko-ref (acc w base st fid fn-arena)
  ; The ref-step of the event W's row: its metadata, the ref (offset, length)
  ; of its payload frame at BASE, and the frame's four trailer words.
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (pcko-ref-step acc (fn-pck-meta w st) (+ *fn-cpl-header-octets* base) (len (fn-pck-payload w))
                 (car (pcko-tw w)) (cadr (pcko-tw w)) (caddr (pcko-tw w)) (cadddr (pcko-tw w))
                 fid fn-arena))

(defun pcko-sim (recs base st acc fid fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (atom recs)
      (mv acc fn-arena)
    (mv-let (acc2 fn-arena)
      (pcko-ref acc (car recs) base st fid fn-arena)
      (if (eq acc2 :bad)
          (mv :bad fn-arena)
        (pcko-sim (cdr recs) (pcko-next-base (car recs) base) (pck-ssr1 st (car recs)) acc2 fid fn-arena)))))

(in-theory (disable pcko-prog pcko-tw pcko-next-base pcko-ref))

(defthm pcko-decode-of-program
  (implies (fn-sccb-treep x)
           (equal (fn-scc-decode-tree (fn-scc-program x)) (list :ok x)))
  :hints (("Goal" :use ((:instance fn-scc-decode-tree-of-encode)
                        (:instance fn-sccb-treep-is-treep))
           :in-theory (disable fn-scc-decode-tree-of-encode fn-sccb-treep-is-treep))))

(defthm pcko-decode-of-prog
  (implies (fn-sccb-treep (fn-pck-meta w st))
           (equal (fn-scc-decode-tree (pcko-prog w st)) (list :ok (fn-pck-meta w st))))
  :hints (("Goal" :in-theory (enable pcko-prog) :use (:instance pcko-decode-of-program (x (fn-pck-meta w st))))))

(defthm pcko-seq-words-cons
  (equal (adt-tp-seq-words s (cons r rows)) (append (adt-tp-rw s r) (adt-tp-seq-words s rows)))
  :hints (("Goal" :in-theory (enable adt-tp-seq-words))))

(defthm pcko-seq-words-nil (equal (adt-tp-seq-words s nil) nil)
  :hints (("Goal" :in-theory (enable adt-tp-seq-words))))

(defthm pcko-row-is-rowwords
  (equal (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row w base st))
         (pcko-rowwords (pcko-prog w st) (+ *fn-cpl-header-octets* base) (len (fn-pck-payload w))
                        (car (pcko-tw w)) (cadr (pcko-tw w)) (caddr (pcko-tw w)) (cadddr (pcko-tw w))))
  :hints (("Goal" :in-theory (e/d (pcko-prog pcko-tw) (fn-pck-meta fn-pck-payload fn-pck-enc-row pcko-rowwords-is-the-row))
           :use (:instance pcko-rowwords-is-the-row (off base)))))

(defthm pcko-program-octetsp
  (implies (fn-sccb-treep (fn-pck-meta w st)) (adt-octetsp (pcko-prog w st)))
  :hints (("Goal" :in-theory (enable pcko-prog) :use (:instance pck-program-octetsp (x (fn-pck-meta w st))))))

(defthm pcko-nthcdr-len-append
  (implies (true-listp x) (equal (nthcdr (len x) (append x rest)) rest)))

(defthm pcko-nthcdr-after-row
  (implies (and (natp pos) (true-listp x) (equal (nthcdr pos w) (append x rest)))
           (equal (nthcdr (+ pos (len x)) w) rest))
  :hints (("Goal" :use ((:instance pck-nthcdr-nthcdr (a (len x)) (b pos) (x w))
                        (:instance pcko-nthcdr-len-append))
           :in-theory (disable pck-nthcdr-nthcdr pcko-nthcdr-len-append pgs-nthcdr-nthcdr pgs-cdr-nthcdr))))

(defun pcko-t-ind (recs base st pos acc reads fid fn-arena fn-octets)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (atom recs)
      (mv (list pos acc reads fn-octets) fn-arena)
    (mv-let (acc2 fn-arena)
      (pcko-ref acc (car recs) base st fid fn-arena)
      (if (eq acc2 :bad)
          (mv (list pos acc reads fn-octets) fn-arena)
        (pcko-t-ind (cdr recs) (pcko-next-base (car recs) base) (pck-ssr1 st (car recs))
                    (+ pos 8 (adt-tp-npk (len (pcko-prog (car recs) st)))) acc2
                    (+ reads 8 (adt-tp-npk (len (pcko-prog (car recs) st)))) fid fn-arena
                    (pcko-prog (car recs) st))))))

(defthm pcko-next-base-natp
  (implies (natp base) (natp (pcko-next-base w base)))
  :hints (("Goal" :in-theory (enable pcko-next-base fn-cpl-frame-octets))))

(defthm pcko-words-of-rows-from-cons
  (implies (consp recs)
           (equal (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from recs base st))
                  (append (pcko-rowwords (pcko-prog (car recs) st) (+ *fn-cpl-header-octets* base)
                                         (len (fn-pck-payload (car recs)))
                                         (car (pcko-tw (car recs))) (cadr (pcko-tw (car recs)))
                                         (caddr (pcko-tw (car recs))) (cadddr (pcko-tw (car recs))))
                          (adt-tp-seq-words *fn-pck-row-schema*
                                            (fn-pck-rows-from (cdr recs) (pcko-next-base (car recs) base)
                                                              (pck-ssr1 st (car recs)))))))
  :hints (("Goal" :expand ((fn-pck-rows-from recs base st))
           :in-theory (e/d (pcko-next-base) (fn-pck-enc-row fn-pck-meta fn-pck-payload pck-ssr1)))))

(defthm pcko-consp-nthcdr (implies (natp i) (equal (consp (nthcdr i l)) (< i (len l)))))

(defthm pcko-tape-nil
  (implies (and (pcko-img w pgs-mem) (natp pos) (<= pos (len w))
                (equal (nthcdr pos w) post) (or (atom post) (not (equal (car post) 1))))
           (equal (pcko-tape pos (len w) acc reads fid pgs-mem fn-arena fn-octets)
                  (mv :ok acc (if (consp post) (+ reads 1) reads) fn-arena fn-octets)))
  :hints (("Goal" :do-not-induct t
           :expand ((pcko-tape pos (len w) acc reads fid pgs-mem fn-arena fn-octets))
           :use ((:instance pcko-consp-nthcdr (i pos) (l w))
                 (:instance pcko-car-nthcdr (i pos) (w w))
                 (:instance pcko-w-is-nth (i pos)))
           :in-theory (disable pcko-tape pcko-consp-nthcdr pcko-car-nthcdr pcko-w-is-nth nth nthcdr))))

(defthm pcko-tape-cons-step
  (let* ((w1 (car recs))
         (prog (pcko-prog w1 st))
         (n (+ 8 (adt-tp-npk (len prog))))
         (base1 (pcko-next-base w1 base))
         (st1 (pck-ssr1 st w1))
         (ref (pcko-ref acc w1 base st fid fn-arena))
         (acc2 (mv-nth 0 ref))
         (ar2 (mv-nth 1 ref)))
    (implies (and (consp recs)
                  (pcko-img w pgs-mem) (true-listp w) (natp pos) (<= pos (len w)) (natp reads)
                  (fn-pck-sccb-listp recs st) (natp base)
                  (equal (nthcdr pos w)
                         (append (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from recs base st)) post))
                  (or (atom post) (not (equal (car post) 1)))
                  (not (eq (car (pcko-sim recs base st acc fid fn-arena)) :bad))
                  ; the induction hypothesis, at the tail
                  (implies (and (natp (+ pos n)) (<= (+ pos n) (len w)) (natp (+ reads n))
                                (fn-pck-sccb-listp (cdr recs) st1) (natp base1)
                                (equal (nthcdr (+ pos n) w)
                                       (append (adt-tp-seq-words *fn-pck-row-schema*
                                                                 (fn-pck-rows-from (cdr recs) base1 st1))
                                               post))
                                (not (eq (car (pcko-sim (cdr recs) base1 st1 acc2 fid ar2)) :bad)))
                           (let ((r (pcko-tape (+ pos n) (len w) acc2 (+ reads n) fid pgs-mem ar2 prog))
                                 (s (pcko-sim (cdr recs) base1 st1 acc2 fid ar2)))
                             (and (equal (mv-nth 0 r) :ok)
                                  (equal (mv-nth 1 r) (car s))
                                  (equal (mv-nth 2 r)
                                         (+ reads n (len (adt-tp-seq-words *fn-pck-row-schema*
                                                                           (fn-pck-rows-from (cdr recs) base1 st1)))
                                            (if (consp post) 1 0)))
                                  (equal (mv-nth 3 r) (cadr s))))))
             (let ((r (pcko-tape pos (len w) acc reads fid pgs-mem fn-arena fn-octets))
                   (s (pcko-sim recs base st acc fid fn-arena)))
               (and (equal (mv-nth 0 r) :ok)
                    (equal (mv-nth 1 r) (car s))
                    (equal (mv-nth 2 r)
                           (+ reads (len (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from recs base st)))
                              (if (consp post) 1 0)))
                    (equal (mv-nth 3 r) (cadr s))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable pcko-tape pcko-sim pcko-ref-step nth nthcdr pcko-w fn-pck-meta fn-pck-payload
                               fn-pck-enc-row fn-scc-program pck-ssr1
                               pcko-row-is-rowwords fn-pck-rows-from fn-arx-trailer-nat fn-cpl-unpack-words
                               adt-tp-seq-words adt-tp-rw adt-tp-fw pck-ssr1-is-the-step)
           :expand ((pcko-sim recs base st acc fid fn-arena) (pcko-ref acc (car recs) base st fid fn-arena)
                    (fn-pck-sccb-listp recs st))
           :use ((:instance pcko-tape-row (prog (pcko-prog (car recs) st))
                            (pos pos) (off (+ *fn-cpl-header-octets* base)) (len (len (fn-pck-payload (car recs))))
                            (d0 (car (pcko-tw (car recs)))) (d1 (cadr (pcko-tw (car recs))))
                            (d2 (caddr (pcko-tw (car recs)))) (d3 (cadddr (pcko-tw (car recs))))
                            (rest (append (adt-tp-seq-words *fn-pck-row-schema*
                                                            (fn-pck-rows-from (cdr recs) (pcko-next-base (car recs) base)
                                                                              (pck-ssr1 st (car recs))))
                                          post)))
                 (:instance pcko-decode-of-prog (w (car recs)))
                 (:instance pcko-nthcdr-after-row
                            (x (pcko-rowwords (pcko-prog (car recs) st) (+ *fn-cpl-header-octets* base)
                                              (len (fn-pck-payload (car recs)))
                                              (car (pcko-tw (car recs))) (cadr (pcko-tw (car recs)))
                                              (caddr (pcko-tw (car recs))) (cadddr (pcko-tw (car recs)))))
                            (rest (append (adt-tp-seq-words *fn-pck-row-schema*
                                                            (fn-pck-rows-from (cdr recs) (pcko-next-base (car recs) base)
                                                                              (pck-ssr1 st (car recs))))
                                          post)))
                 (:instance pcko-len-rowwords (prog (pcko-prog (car recs) st)) (off (+ *fn-cpl-header-octets* base))
                            (len (len (fn-pck-payload (car recs))))
                            (d0 (car (pcko-tw (car recs)))) (d1 (cadr (pcko-tw (car recs))))
                            (d2 (caddr (pcko-tw (car recs)))) (d3 (cadddr (pcko-tw (car recs)))))
                 (:instance pcko-nthcdr-room
                            (x (pcko-rowwords (pcko-prog (car recs) st) (+ *fn-cpl-header-octets* base)
                                              (len (fn-pck-payload (car recs)))
                                              (car (pcko-tw (car recs))) (cadr (pcko-tw (car recs)))
                                              (caddr (pcko-tw (car recs))) (cadddr (pcko-tw (car recs)))))
                            (rest (append (adt-tp-seq-words *fn-pck-row-schema*
                                                            (fn-pck-rows-from (cdr recs) (pcko-next-base (car recs) base)
                                                                              (pck-ssr1 st (car recs))))
                                          post)))
                 (:instance pcko-program-octetsp (w (car recs)))))))

(defthm pcko-tape-of-recs
  (implies (and (pcko-img w pgs-mem) (true-listp w) (natp pos) (<= pos (len w)) (natp reads)
                (fn-pck-sccb-listp recs st) (natp base)
                (equal (nthcdr pos w)
                       (append (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from recs base st)) post))
                (or (atom post) (not (equal (car post) 1)))
                (not (eq (car (pcko-sim recs base st acc fid fn-arena)) :bad)))
           (let ((r (pcko-tape pos (len w) acc reads fid pgs-mem fn-arena fn-octets))
                 (s (pcko-sim recs base st acc fid fn-arena)))
             (and (equal (mv-nth 0 r) :ok)
                  (equal (mv-nth 1 r) (car s))
                  (equal (mv-nth 2 r)
                         (+ reads (len (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from recs base st)))
                            (if (consp post) 1 0)))
                  (equal (mv-nth 3 r) (cadr s)))))
  :hints (("Goal" :induct (pcko-t-ind recs base st pos acc reads fid fn-arena fn-octets)
           :do-not-induct t
           :in-theory (disable pcko-tape pcko-sim pcko-ref pcko-ref-step
                               fn-pck-rows-from adt-tp-seq-words pcko-prog pcko-next-base))
          ("Subgoal *1/3" :use pcko-tape-cons-step)
          ("Subgoal *1/2" :expand ((pcko-sim recs base st acc fid fn-arena)))
          ("Subgoal *1/1" :use pcko-tape-nil
           :in-theory (e/d (fn-pck-rows-from adt-tp-seq-words pcko-sim) (pcko-tape pcko-tape-nil)))))

; -----------------------------------------------------------------------------
; The tape's fold is full recovery's.  AGREE: the open's accumulator and the
; model's fold state share keyring, generation and identity context (they differ
; in the rows' handles only).

; The arena is read through its interface, never through the opened list view.
(in-theory (disable fn-arena-payload-is-nth fn-arena-count-is-len fn-arena-seal-list-is-append
                    fn-arena-p-is-payload-listp fn-arena-get-is-nth fn-arena-payload-len-is-len-nth))

(defun pcko-agree (acc st)
  (and (fn-ssr-statep acc) (fn-ssr-statep st)
       (equal (fn-ssr-at 1 acc) (fn-ssr-at 1 st))
       (equal (fn-ssr-at 2 acc) (fn-ssr-at 2 st))
       (equal (fn-ssr-at 3 acc) (fn-ssr-at 3 st))))

(defthm pcko-count-seal-list
  (equal (fn-arena-count (fn-arena-seal-list xs fn-arena)) (1+ (fn-arena-count fn-arena)))
  :hints (("Goal" :in-theory (enable fn-arena-seal-list fn-arena-count))))

(defthm pcko-count-seal-extent
  (equal (fn-arena-count (fn-arena-seal-extent file eoff elen poff plen trailer fn-arena))
         (1+ (fn-arena-count fn-arena)))
  :hints (("Goal" :use fn-arena-seal-extent-payload :in-theory (disable fn-arena-seal-extent-payload))))

(defun pcko-ie-delta (w)
  (declare (xargs :guard t))
  (cond ((fn-record-p w) 1)
        ((and (fn-stxa-p w) (fn-record-p (fn-replay-composite-record w))) 1)
        (t 0)))

(defthm pcko-ie-count
  (equal (fn-arena-count (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))
         (+ (fn-arena-count fn-arena) (pcko-ie-delta w)))
  :hints (("Goal" :in-theory (e/d (pcko-ie-delta) (fn-intern-event fn-record-p fn-stxa-p fn-replay-composite-record
                                                   pcko-count-seal-list))
           :use (fn-intern-event-arena pcko-count-seal-list))))

(defthm pcko-ie-row-of-count
  ; The row an event interns depends on the arena only through its count.
  (implies (equal (fn-arena-count a) (fn-arena-count b))
           (equal (mv-nth 0 (fn-intern-event w keyring generation a))
                  (mv-nth 0 (fn-intern-event w keyring generation b))))
  :hints (("Goal" :in-theory (e/d (fn-intern-event) (fn-cat-intern-list fn-cat-intern-list-is-row-at-count fn-replay-composite-record))
           :use ((:instance fn-cat-intern-list-is-row-at-count (fn-arena a))
                 (:instance fn-cat-intern-list-is-row-at-count (fn-arena b))
                 (:instance fn-cat-intern-list-is-row-at-count (w (fn-replay-composite-record w)) (fn-arena a))
                 (:instance fn-cat-intern-list-is-row-at-count (w (fn-replay-composite-record w)) (fn-arena b))))))

(defthm pcko-f1
  ; One event of full recovery's resident fold.
  (implies (fn-ssr-statep acc)
           (let* ((row (mv-nth 0 (fn-intern-event w (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) a)))
                  (ar (mv-nth 1 (fn-intern-event w (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) a)))
                  (identity (fn-replay-identity-step (fn-ssr-at 3 acc) row)))
             (and (equal (mv-nth 0 (fn-ssr-intern-step acc (list w) nil nil :resident nil a))
                         (if (or (eq row :bad) (not (equal (fn-stxk-context-kind identity) :ok)))
                             :bad
                           (fn-ssr-publish acc row w identity)))
                  (equal (mv-nth 1 (fn-ssr-intern-step acc (list w) nil nil :resident nil a)) ar))))
  :hints (("Goal" :expand ((fn-ssr-intern-step acc (list w) nil nil :resident nil a)
                           (fn-ssr-intern-step (fn-ssr-publish acc (mv-nth 0 (fn-intern-event w (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) a))
                                                               w (fn-replay-identity-step (fn-ssr-at 3 acc)
                                                                                         (mv-nth 0 (fn-intern-event w (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) a))))
                                               nil nil nil :resident nil
                                               (mv-nth 1 (fn-intern-event w (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) a))))
           :in-theory (disable fn-intern-event fn-ssr-publish fn-replay-identity-step fn-ssr-at fn-stxk-context-kind))))

(defthm pcko-ie-row-of-record
  (implies (fn-record-p w)
           (equal (mv-nth 0 (fn-intern-event w keyring generation a))
                  (fn-intern-row-at w keyring generation (fn-arena-count a))))
  :hints (("Goal" :in-theory (e/d (fn-intern-event) (fn-cat-intern-list fn-cat-intern-list-is-row-at-count fn-replay-composite-record))
           :use ((:instance fn-cat-intern-list-is-row-at-count (fn-arena a))))))

(defthm pcko-count-natp (natp (fn-arena-count a))
  :hints (("Goal" :in-theory (enable fn-arena-count)))
  :rule-classes :type-prescription)

(defthm pcko-row-f-of-record
  ; The row full recovery interns for a record is the tape's held row reseated
  ; at the arena's count.
  (implies (and (fn-record-p w) (pcko-agree acc st) (not (equal (pck-ssr1 st w) :bad)))
           (equal (mv-nth 0 (fn-intern-event w (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) b))
                  (pcko-reseat (fn-pck-row0 st w) (fn-arena-count b))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(pcko-agree (:type-prescription pcko-count-natp)) (theory 'minimal-theory))
           :use ((:instance pcko-ie-row-of-record (keyring (fn-ssr-at 1 acc)) (generation (fn-ssr-at 2 acc)) (a b))
                 (:instance pcko-intern-row-at-reseat (k (fn-ssr-at 1 acc)) (g (fn-ssr-at 2 acc)) (h (fn-arena-count b)))
                 (:instance pck-row0-is-the-row)
                 (:instance pcko-count-natp (a b))))))

(defthm pcko-publish-wire
  (implies (and (not (fn-stxk-p w1)) (not (fn-stxk-p w2)))
           (equal (fn-ssr-publish acc row w1 id) (fn-ssr-publish acc row w2 id)))
  :hints (("Goal" :in-theory (enable fn-ssr-publish))))

(defthm pcko-ref-step-held
  ; The ref-step of a record row: the held row reseated at the arena's count,
  ; the extent sealed.
  (implies (and (fn-held-p r) (<= 37 off))
           (and (equal (mv-nth 0 (pcko-ref-step acc (list :r r) off len d0 d1 d2 d3 fid a))
                       (let* ((row (pcko-reseat r (fn-arena-count a)))
                              (identity (fn-replay-identity-step (fn-ssr-at 3 acc) row)))
                         (if (equal (fn-stxk-context-kind identity) :ok)
                             (fn-ssr-publish acc row row identity)
                           :bad)))
                (equal (mv-nth 1 (pcko-ref-step acc (list :r r) off len d0 d1 d2 d3 fid a))
                       (fn-arena-seal-extent fid (- off 37) (+ len 37) off len
                                             (fn-arx-trailer-nat (fn-cpl-unpack-words (list d0 d1 d2 d3))) a))))
  :hints (("Goal" :in-theory (e/d (pcko-ref-step pcko-recp) (fn-replay-identity-step fn-ssr-publish pcko-reseat fn-ssr-at
                                                             fn-stxk-context-kind fn-arena-seal-extent fn-held-p fn-arx-trailer-nat fn-cpl-unpack-words)))))

(defthm pcko-ie-delta-of-record
  (implies (fn-record-p w) (equal (pcko-ie-delta w) 1))
  :hints (("Goal" :in-theory (enable pcko-ie-delta))))

(defthm pcko-count-snoc
  (equal (fn-arena-count (fn-oct-snoc a x)) (+ 1 (fn-arena-count a)))
  :hints (("Goal" :in-theory (enable fn-arena-count))))

(defthm pcko-ref-of-held
  ; The ref-step of a record row against full recovery's step, with the held
  ; row abstract: full recovery's row is the row reseated at the count.
  (implies (and (fn-held-p r) (<= 37 off) (fn-ssr-statep acc) (fn-record-p w)
                (equal (fn-arena-count a) (fn-arena-count b))
                (equal (mv-nth 0 (fn-intern-event w (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) b))
                       (pcko-reseat r (fn-arena-count b))))
           (and (equal (mv-nth 0 (pcko-ref-step acc (list :r r) off len d0 d1 d2 d3 fid a))
                       (mv-nth 0 (fn-ssr-intern-step acc (list w) nil nil :resident nil b)))
                (equal (fn-arena-count (mv-nth 1 (pcko-ref-step acc (list :r r) off len d0 d1 d2 d3 fid a)))
                       (fn-arena-count (mv-nth 1 (fn-ssr-intern-step acc (list w) nil nil :resident nil b))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable pcko-ref-step fn-intern-event fn-ssr-publish fn-replay-identity-step fn-ssr-at
                               fn-stxk-context-kind pcko-reseat fn-record-p fn-ssr-intern-step pcko-ref-step-held
                               pcko-f1 pcko-ie-count pcko-publish-wire fn-held-p fn-stxk-p)
           :use ((:instance pcko-f1 (a b))
                 (:instance pcko-ref-step-held)
                 (:instance pcko-ie-count (keyring (fn-ssr-at 1 acc)) (generation (fn-ssr-at 2 acc)) (fn-arena b))
                 (:instance pcko-ie-delta-of-record)
                 (:instance pcko-publish-wire (w1 w) (w2 (pcko-reseat r (fn-arena-count a))) (row (pcko-reseat r (fn-arena-count a)))
                            (id (fn-replay-identity-step (fn-ssr-at 3 acc) (pcko-reseat r (fn-arena-count a)))))
                 (:instance fn-record-is-no-other-wire-event (x w))
                 (:instance fn-held-is-no-wire-event (x (pcko-reseat r (fn-arena-count a))))
                 (:instance pcko-reseat-held-p (row r) (h (fn-arena-count a)))
                 (:instance pcko-count-natp)
                 (:instance pcko-count-snoc (x (fn-durable-octets fid off len)))))))

(defthm pcko-meta-of-record
  (implies (fn-record-p w) (equal (fn-pck-meta w st) (list :r (fn-pck-row0 st w))))
  :hints (("Goal" :in-theory (enable fn-pck-meta))))

(defthm pcko-ref-of-record
  (implies (and (fn-record-p w) (pcko-agree acc st) (natp base)
                (not (equal (pck-ssr1 st w) :bad))
                (equal (fn-arena-count a) (fn-arena-count b)))
           (and (equal (mv-nth 0 (pcko-ref acc w base st fid a))
                       (mv-nth 0 (fn-ssr-intern-step acc (list w) nil nil :resident nil b)))
                (equal (fn-arena-count (mv-nth 1 (pcko-ref acc w base st fid a)))
                       (fn-arena-count (mv-nth 1 (fn-ssr-intern-step acc (list w) nil nil :resident nil b))))))
  :hints (("Goal" :do-not-induct t
           :expand ((pcko-ref acc w base st fid a))
           :in-theory (disable pcko-ref-step fn-pck-row0 fn-pck-payload pcko-tw fn-intern-event fn-ssr-publish
                               fn-replay-identity-step fn-ssr-at fn-stxk-context-kind pck-ssr1 pcko-reseat
                               fn-record-p fn-ssr-intern-step pcko-ref-of-held pcko-row-f-of-record
                               pck-row0-wire pck-row0-is-the-row fn-held-p fn-pck-meta)
           :use ((:instance pck-row0-wire)
                 (:instance pcko-row-f-of-record (b b))
                 (:instance pcko-ref-of-held (r (fn-pck-row0 st w)) (off (+ 37 base)) (len (len (fn-pck-payload w)))
                            (d0 (car (pcko-tw w))) (d1 (cadr (pcko-tw w))) (d2 (caddr (pcko-tw w)))
                            (d3 (cadddr (pcko-tw w))))))))

(defthm pcko-ref-step-other
  (implies (not (pcko-recp tree))
           (equal (pcko-ref-step acc tree off len d0 d1 d2 d3 fid a)
                  (fn-ssr-intern-step acc (list (pcko-ev tree)) nil nil :resident nil a)))
  :hints (("Goal" :in-theory (e/d (pcko-ref-step) (fn-ssr-intern-step)))))

(defthm pcko-intern-step-of-count
  ; One event's fold step depends on the arena only through its count.
  (implies (and (fn-ssr-statep acc) (equal (fn-arena-count a) (fn-arena-count b)))
           (and (equal (mv-nth 0 (fn-ssr-intern-step acc (list w) nil nil :resident nil a))
                       (mv-nth 0 (fn-ssr-intern-step acc (list w) nil nil :resident nil b)))
                (equal (fn-arena-count (mv-nth 1 (fn-ssr-intern-step acc (list w) nil nil :resident nil a)))
                       (fn-arena-count (mv-nth 1 (fn-ssr-intern-step acc (list w) nil nil :resident nil b))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-intern-event fn-ssr-publish fn-replay-identity-step fn-ssr-at fn-stxk-context-kind
                               fn-ssr-intern-step pcko-f1 pcko-ie-row-of-count pcko-ie-count)
           :use ((:instance pcko-f1 (a a)) (:instance pcko-f1 (a b))
                 (:instance pcko-ie-row-of-count (keyring (fn-ssr-at 1 acc)) (generation (fn-ssr-at 2 acc)))
                 (:instance pcko-ie-count (keyring (fn-ssr-at 1 acc)) (generation (fn-ssr-at 2 acc)) (fn-arena a))
                 (:instance pcko-ie-count (keyring (fn-ssr-at 1 acc)) (generation (fn-ssr-at 2 acc)) (fn-arena b))))))

(defthm pcko-meta-of-other
  (implies (not (fn-record-p w)) (equal (fn-pck-meta w st) (list :o w)))
  :hints (("Goal" :in-theory (enable fn-pck-meta))))

(defthm pcko-recp-of-o (not (pcko-recp (list :o w)))
  :hints (("Goal" :in-theory (enable pcko-recp))))

(defthm pcko-ev-of-list (equal (pcko-ev (list x w)) w)
  :hints (("Goal" :in-theory (enable pcko-ev))))

(defthm pcko-ref-of-other
  (implies (and (not (fn-record-p w)) (fn-ssr-statep acc)
                (equal (fn-arena-count a) (fn-arena-count b)))
           (and (equal (mv-nth 0 (pcko-ref acc w base st fid a))
                       (mv-nth 0 (fn-ssr-intern-step acc (list w) nil nil :resident nil b)))
                (equal (fn-arena-count (mv-nth 1 (pcko-ref acc w base st fid a)))
                       (fn-arena-count (mv-nth 1 (fn-ssr-intern-step acc (list w) nil nil :resident nil b))))))
  :hints (("Goal" :do-not-induct t
           :expand ((pcko-ref acc w base st fid a))
           :in-theory (union-theories '(pcko-meta-of-other) (theory 'minimal-theory))
           :use ((:instance pcko-ref-step-other (tree (list :o w)) (off (+ 37 base)) (len (len (fn-pck-payload w)))
                            (d0 (car (pcko-tw w))) (d1 (cadr (pcko-tw w))) (d2 (caddr (pcko-tw w)))
                            (d3 (cadddr (pcko-tw w))))
                 pcko-recp-of-o (:instance pcko-ev-of-list (x :o))
                 pcko-intern-step-of-count))))

; -----------------------------------------------------------------------------
; The fold states stay in agreement.

(defthm pcko-identity-of-hstxa
  (implies (and (fn-stxa-p w) (fn-held-p h1) (fn-held-p h2))
           (equal (fn-replay-identity-step ctx (fn-hstxa-make w h1))
                  (fn-replay-identity-step ctx (fn-hstxa-make w h2))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-replay-identity-step fn-store-event-sequence fn-replay-identity-wire)
                           (fn-held-p fn-stxa-p fn-hsig-article-event-carried-bindsp fn-hsig-article-event-revoked-bindsp
                            fn-stxk-fault fn-replay-identity-advance fn-stxk-p fn-stxe-p))
           :use ((:instance fn-hstxa-is-no-wire-event (x (fn-hstxa-make w h1)))
                 (:instance fn-hstxa-is-no-wire-event (x (fn-hstxa-make w h2)))
                 (:instance fn-hstxa-is-not-held (x (fn-hstxa-make w h1)))
                 (:instance fn-hstxa-is-not-held (x (fn-hstxa-make w h2)))
                 (:instance fn-hstxa-p-of-make (stxa w) (held h1))
                 (:instance fn-hstxa-p-of-make (stxa w) (held h2))))))

(defthm pcko-publish-agree
  ; The rows do not enter the keyring, generation or identity slots.
  (implies (and (fn-ssr-statep acc) (fn-ssr-statep st)
                (equal (fn-ssr-at 1 acc) (fn-ssr-at 1 st)) (equal (fn-ssr-at 2 acc) (fn-ssr-at 2 st))
                (equal (fn-ssr-at 3 acc) (fn-ssr-at 3 st)))
           (and (equal (fn-ssr-at 1 (fn-ssr-publish acc r1 w id)) (fn-ssr-at 1 (fn-ssr-publish st r2 w id)))
                (equal (fn-ssr-at 2 (fn-ssr-publish acc r1 w id)) (fn-ssr-at 2 (fn-ssr-publish st r2 w id)))
                (equal (fn-ssr-at 3 (fn-ssr-publish acc r1 w id)) (fn-ssr-at 3 (fn-ssr-publish st r2 w id)))))
  :hints (("Goal" :in-theory (enable fn-ssr-publish fn-ssr-state fn-ssr-at))))

(defthm pcko-held-p-of-row-at
  (implies (and (fn-record-p w) (natp g) (natp h))
           (fn-held-p (fn-intern-row-at w k g h)))
  :hints (("Goal" :in-theory (enable fn-record-p fn-held-p fn-record-internals fn-held-internals fn-hf-p fn-hc-p
                                     fn-hf-startp fn-hc-verdictp fn-intern-row-at))))

(defthm pcko-ie-identity-eq-record
  (implies (and (fn-record-p w) (natp generation))
           (equal (fn-replay-identity-step c (mv-nth 0 (fn-intern-event w k generation a)))
                  (fn-replay-identity-step c (mv-nth 0 (fn-intern-event w k generation b)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-intern-event fn-replay-identity-step fn-intern-row-at pcko-reseat fn-held-p
                               pcko-ie-row-of-record pcko-identity-of-reseat
                               pcko-held-p-of-row-at pcko-count-natp fn-record-p)
           :use ((:instance pcko-ie-row-of-record (keyring k) (a a))
                 (:instance pcko-ie-row-of-record (keyring k) (a b))
                 (:instance pcko-intern-row-at-reseat (g generation) (h (fn-arena-count a)))
                 (:instance pcko-intern-row-at-reseat (g generation) (h (fn-arena-count b)))
                 (:instance pcko-identity-of-reseat (ctx c) (row (fn-intern-row-at w k generation 0)) (h (fn-arena-count a)))
                 (:instance pcko-identity-of-reseat (ctx c) (row (fn-intern-row-at w k generation 0)) (h (fn-arena-count b)))
                 (:instance pcko-held-p-of-row-at (g generation) (h 0))
                 (:instance pcko-count-natp (a a)) (:instance pcko-count-natp (a b))))))

(defthm pcko-ie-identity-eq
  ; The identity fold sees the same row whatever arena the event is interned
  ; into: the rows differ in the handle only.
  (implies (natp generation)
           (and (iff (equal (mv-nth 0 (fn-intern-event w k generation a)) :bad)
                     (equal (mv-nth 0 (fn-intern-event w k generation b)) :bad))
                (equal (fn-replay-identity-step c (mv-nth 0 (fn-intern-event w k generation a)))
                       (fn-replay-identity-step c (mv-nth 0 (fn-intern-event w k generation b))))))
  :hints (("Goal" :do-not-induct t
           :cases ((fn-record-p w) (and (fn-stxa-p w) (fn-record-p (fn-replay-composite-record w))))
           :in-theory (e/d (fn-intern-event) (fn-cat-intern-list fn-cat-intern-list-is-row-at-count
                                              fn-replay-composite-record fn-record-p fn-stxa-p fn-wire-event-p
                                              fn-intern-row-at fn-replay-identity-step fn-held-p
                                              pcko-identity-of-hstxa pcko-held-p-of-row-at))
           :use ((:instance fn-cat-intern-list-is-row-at-count (keyring k) (fn-arena a))
                 (:instance fn-cat-intern-list-is-row-at-count (keyring k) (fn-arena b))
                 (:instance fn-cat-intern-list-is-row-at-count (keyring k) (w (fn-replay-composite-record w)) (fn-arena a))
                 (:instance fn-cat-intern-list-is-row-at-count (keyring k) (w (fn-replay-composite-record w)) (fn-arena b))
                 (:instance pcko-ie-identity-eq-record)
                 (:instance pcko-held-p-of-row-at (w (fn-replay-composite-record w)) (g generation) (h (fn-arena-count a)))
                 (:instance pcko-held-p-of-row-at (w (fn-replay-composite-record w)) (g generation) (h (fn-arena-count b)))
                 (:instance pcko-identity-of-hstxa (ctx c) (h1 (fn-intern-row-at (fn-replay-composite-record w) k generation (fn-arena-count a)))
                            (h2 (fn-intern-row-at (fn-replay-composite-record w) k generation (fn-arena-count b))))
                 (:instance pcko-count-natp (a a)) (:instance pcko-count-natp (a b))))))

(defthm pcko-step-agree
  ; One event of full recovery's fold leaves the open's accumulator in
  ; agreement with the model's next fold state, and does not fault when the
  ; model's step does not.
  (implies (and (pcko-agree acc st) (not (equal (pck-ssr1 st w) :bad)))
           (let ((acc2 (mv-nth 0 (fn-ssr-intern-step acc (list w) nil nil :resident nil b))))
             (and (not (equal acc2 :bad))
                  (pcko-agree acc2 (pck-ssr1 st w)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (pcko-agree) (fn-intern-event fn-ssr-publish fn-replay-identity-step fn-ssr-at
                                         fn-stxk-context-kind fn-ssr-intern-step pcko-f1 pck-ssr1-is-the-step
                                         pcko-ie-identity-eq pcko-publish-agree fn-ssr-publish-preserves-statep
                                         pck-ssr1))
           :use ((:instance pck-ssr1-is-the-step)
                 (:instance pcko-f1 (a b))
                 (:instance pcko-f1 (acc st) (a nil))
                 (:instance pcko-ie-identity-eq (k (fn-ssr-at 1 acc)) (generation (fn-ssr-at 2 acc)) (a b) (b nil)
                            (c (fn-ssr-at 3 acc)))
                 (:instance pck-statep-generation (acc acc))
                 (:instance pck-ssr1-statep)
                 (:instance fn-ssr-publish-preserves-statep (row (mv-nth 0 (fn-intern-event w (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) b)))
                            (wire w)
                            (identity (fn-replay-identity-step (fn-ssr-at 3 acc) (mv-nth 0 (fn-intern-event w (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) b)))))
                 (:instance pcko-publish-agree (r1 (mv-nth 0 (fn-intern-event w (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) b)))
                            (r2 (mv-nth 0 (fn-intern-event w (fn-ssr-at 1 st) (fn-ssr-at 2 st) nil)))
                            (id (fn-replay-identity-step (fn-ssr-at 3 acc) (mv-nth 0 (fn-intern-event w (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) b)))))))))

(defun-nx pcko-s-ind (recs base st acc fid a b)
  (if (atom recs)
      (list a b)
    (let ((acc2 (mv-nth 0 (pcko-ref acc (car recs) base st fid a)))
          (a2 (mv-nth 1 (pcko-ref acc (car recs) base st fid a)))
          (b2 (mv-nth 1 (fn-ssr-intern-step acc (list (car recs)) nil nil :resident nil b))))
      (if (eq acc2 :bad)
          (list a2 b2)
        (pcko-s-ind (cdr recs) (pcko-next-base (car recs) base) (pck-ssr1 st (car recs)) acc2 fid a2 b2)))))

; The step lemmas are used by name.
(in-theory (disable pcko-ref-of-held pcko-ref-of-record pcko-ref-of-other pcko-intern-step-of-count
                    pcko-ie-row-of-count pcko-ref-step-held pcko-ref-step-other pcko-f1 pcko-ie-count
                    pcko-ie-row-of-record pcko-row-f-of-record pcko-step-agree pcko-ie-identity-eq
                    pcko-ie-identity-eq-record pcko-publish-agree))

(defthm pcko-ref-is-the-step
  ; The ref-step of any event is full recovery's step on that event.
  (implies (and (pcko-agree acc st) (natp base) (not (equal (pck-ssr1 st w) :bad))
                (equal (fn-arena-count a) (fn-arena-count b)))
           (and (equal (mv-nth 0 (pcko-ref acc w base st fid a))
                       (mv-nth 0 (fn-ssr-intern-step acc (list w) nil nil :resident nil b)))
                (equal (fn-arena-count (mv-nth 1 (pcko-ref acc w base st fid a)))
                       (fn-arena-count (mv-nth 1 (fn-ssr-intern-step acc (list w) nil nil :resident nil b))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (pcko-agree) (pcko-ref fn-ssr-intern-step fn-record-p))
           :use (pcko-ref-of-record pcko-ref-of-other)))
  :rule-classes nil)

(defthm pcko-sim-cons-step
  (let* ((w1 (car recs))
         (ref (pcko-ref acc w1 base st fid a))
         (acc2 (mv-nth 0 ref))
         (a2 (mv-nth 1 ref))
         (b2 (mv-nth 1 (fn-ssr-intern-step acc (list w1) nil nil :resident nil b)))
         (st1 (pck-ssr1 st w1))
         (base1 (pcko-next-base w1 base)))
    (implies (and (consp recs) (true-listp recs) (pcko-agree acc st) (natp base)
                  (not (equal (fn-pck-st-of st recs) :bad))
                  (equal (fn-arena-count a) (fn-arena-count b))
                  (implies (and (true-listp (cdr recs)) (pcko-agree acc2 st1) (natp base1)
                                (not (equal (fn-pck-st-of st1 (cdr recs)) :bad))
                                (equal (fn-arena-count a2) (fn-arena-count b2)))
                           (let ((s (pcko-sim (cdr recs) base1 st1 acc2 fid a2))
                                 (f (fn-ssr-intern-step acc2 (cdr recs) nil nil :resident nil b2)))
                             (and (not (equal (mv-nth 0 s) :bad))
                                  (equal (mv-nth 0 s) (mv-nth 0 f))
                                  (equal (fn-arena-count (mv-nth 1 s)) (fn-arena-count (mv-nth 1 f)))))))
             (let ((s (pcko-sim recs base st acc fid a))
                   (f (fn-ssr-intern-step acc recs nil nil :resident nil b)))
               (and (not (equal (mv-nth 0 s) :bad))
                    (equal (mv-nth 0 s) (mv-nth 0 f))
                    (equal (fn-arena-count (mv-nth 1 s)) (fn-arena-count (mv-nth 1 f)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable pcko-ref fn-ssr-intern-step pck-ssr1 pcko-agree pcko-next-base fn-pck-st-of pcko-sim
                               pcko-step-agree)
           :expand ((pcko-sim recs base st acc fid a) (fn-pck-st-of st recs))
           :use ((:instance pcko-intern-cons (x (car recs)) (ts (cdr recs)) (fn-arena b))
                 (:instance pcko-ref-is-the-step (w (car recs)))
                 (:instance pcko-step-agree (w (car recs)))))))

(defthm pcko-sim-is-the-fold
  ; The tape's fold is full recovery's fold over the records, row for row.
  (implies (and (true-listp recs) (pcko-agree acc st) (natp base)
                (not (equal (fn-pck-st-of st recs) :bad))
                (equal (fn-arena-count a) (fn-arena-count b)))
           (let ((s (pcko-sim recs base st acc fid a))
                 (f (fn-ssr-intern-step acc recs nil nil :resident nil b)))
             (and (not (equal (mv-nth 0 s) :bad))
                  (equal (mv-nth 0 s) (mv-nth 0 f))
                  (equal (fn-arena-count (mv-nth 1 s)) (fn-arena-count (mv-nth 1 f))))))
  :hints (("Goal" :induct (pcko-s-ind recs base st acc fid a b) :do-not-induct t
           :in-theory (disable pcko-ref fn-ssr-intern-step pck-ssr1 pcko-agree pcko-next-base fn-pck-st-of pcko-sim))
          ("Subgoal *1/3" :use pcko-sim-cons-step)
          ("Subgoal *1/2" :expand ((fn-pck-st-of st recs))
           :use ((:instance pcko-ref-is-the-step (w (car recs))) (:instance pcko-step-agree (w (car recs)))))
          ("Subgoal *1/1" :in-theory (e/d (pcko-sim fn-ssr-intern-step pcko-agree fn-ssr-statep) (pcko-ref pck-ssr1)))))


; -----------------------------------------------------------------------------
; The open, over the image.

(defthm pcko-open-form
  ; The open of an image whose first row is the root row: the tape, from the
  ; first word past the root region, with the root tree decoded.
  (implies (and (pcko-img w pgs-mem) (true-listp w) (natp npg) (<= 8 npg) (equal (len w) (* 2048 npg))
                (<= (* 2048 npg) (pgs-x-len 0 pgs-mem)) (natp fid)
                (adt-octetsp prog)
                (equal w (append (pcko-rowwords prog 0 0 0 0 0 0) rest))
                (<= (+ 2 (adt-tp-npk (len prog))) 16384)
                (pcko-ok-treep (fn-scc-decode-tree prog)))
           (equal (fn-pck-x-open npg pgs-mem fid a octets)
                  (mv-let (verdict acc reads a2 oct2)
                    (pcko-tape 16384 (* 2048 npg) (fn-ssr-seed (fn-stxk-initial-context 0))
                               (+ 2 (adt-tp-npk (len prog))) fid pgs-mem a prog)
                    (mv verdict (fn-ssr-rows acc)
                        (let ((root (cadr (fn-scc-decode-tree prog))))
                          (list (pcko-nth 0 root) (pcko-nth 1 root) (pcko-nth 2 root) (pcko-nth 3 root)))
                        reads a2 oct2))))
  :hints (("Goal" :do-not-induct t
           :expand ((fn-pck-x-open npg pgs-mem fid a octets))
           :in-theory (e/d (pcko-nw-is-npk) (pcko-tape pcko-w nth fn-scc-decode-tree adt-tp-npk adt-tp-unpack
                                             pcko-copy pcko-tree nfix pcko-rowwords))
           :use ((:instance pcko-nthcdr-room (pos 0) (x (pcko-rowwords prog 0 0 0 0 0 0)))
                 (:instance pcko-len-rowwords (off 0) (len 0) (d0 0) (d1 0) (d2 0) (d3 0))
                 (:instance pcko-nth-rowwords-head (off 0) (len 0) (d0 0) (d1 0) (d2 0) (d3 0))
                 (:instance pcko-unpack-of-row (pos 0) (off 0) (len 0) (d0 0) (d1 0) (d2 0) (d3 0))
                 (:instance pcko-w-is-nth (i 0)) (:instance pcko-w-is-nth (i 1))))))

(defthm pcko-sccb-listp-true-listp
  (implies (fn-pck-sccb-listp recs st) (true-listp recs))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-pck-sccb-listp))))

(defthm pcko-root-tree-true-listp
  (true-listp (fn-pck-root-tree configs recs))
  :hints (("Goal" :in-theory (enable fn-pck-root-tree fn-pck-root-tree-of-capture))))

(defthm pcko-nth-is-nth
  (implies (true-listp x) (equal (pcko-nth i x) (nth i x))))

(defthm pcko-append-assoc3 (equal (append (append a b) c) (append a (append b c))))

(defthm pcko-w-shape
  (implies (fn-pck-root-fitsp configs recs)
           (let ((x (fn-pck-root-tree configs recs)))
             (equal (adt-tp-flat (fn-pck-pages configs recs))
                    (append (pcko-rowwords (fn-scc-program x) 0 0 0 0 0 0)
                            (append (adt-tp-zeros (- 16384 (len (pcko-rw0 x))))
                                    (append (pcko-tws recs) (adt-tp-zeros (adt-tp-pad (len (pcko-tws recs))))))))))
  :hints (("Goal" :in-theory (e/d () (pcko-flat-pages pcko-rw0 pcko-tws fn-pck-pages adt-tp-zeros pcko-rw0-is))
           :use ((:instance pcko-flat-pages) (:instance pcko-rw0-is (x (fn-pck-root-tree configs recs)))))))

(defthm pcko-root-fits-in-region
  (implies (fn-pck-root-fitsp configs recs)
           (<= (+ 2 (adt-tp-npk (len (fn-scc-program (fn-pck-root-tree configs recs))))) 16384))
  :hints (("Goal" :in-theory (disable pcko-root-flat pcko-rw0 pcko-rw0-is)
           :use ((:instance pcko-root-flat) (:instance pcko-rw0-is (x (fn-pck-root-tree configs recs)))
                 (:instance pcko-len-rowwords (prog (fn-scc-program (fn-pck-root-tree configs recs)))
                            (off 0) (len 0) (d0 0) (d1 0) (d2 0) (d3 0))
                 (:instance pck-program-octetsp (x (fn-pck-root-tree configs recs)))))))

(defthm pcko-rowwords-true-listp (true-listp (pcko-rowwords prog off len d0 d1 d2 d3))
  :hints (("Goal" :in-theory (enable pcko-rowwords))))

(defthm pcko-zeros-true-listp (true-listp (adt-tp-zeros n))
  :hints (("Goal" :in-theory (enable adt-tp-zeros))))

(defthm pcko-flat-true-listp
  (implies (fn-pck-root-fitsp configs recs) (true-listp (adt-tp-flat (fn-pck-pages configs recs))))
  :hints (("Goal" :in-theory (disable pcko-w-shape fn-pck-pages pcko-rw0 pcko-tws adt-tp-zeros)
           :use (pcko-w-shape))))

(defthm pcko-tws-is-rows-from
  (equal (pcko-tws recs) (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from recs 0 (fn-pck-seed))))
  :hints (("Goal" :in-theory (enable pcko-tws fn-pck-rows))))

(defthm pcko-npg-ok
  (implies (fn-pck-root-fitsp configs recs)
           (and (natp (len (fn-pck-pages configs recs))) (<= 8 (len (fn-pck-pages configs recs)))))
  :hints (("Goal" :in-theory (disable fn-pck-pages pcko-tws) :use pcko-len-pages)))

(defthm pcko-recordsp-root
  (implies (fn-pck-recordsp configs recs) (fn-sccb-treep (fn-pck-root-tree configs recs)))
  :hints (("Goal" :in-theory (enable fn-pck-recordsp))))

(defthm pcko-image-facts
  ; What the open reads off the flattened pages of a root-fitting history.
  (implies (and (fn-pck-recordsp configs recs) (fn-pck-root-fitsp configs recs)
                (equal npg (len (fn-pck-pages configs recs))))
           (let ((w (adt-tp-flat (fn-pck-pages configs recs)))
                 (prog (fn-scc-program (fn-pck-root-tree configs recs))))
             (and (true-listp w) (natp npg) (<= 8 npg) (equal (len w) (* 2048 npg))
                  (adt-octetsp prog)
                  (equal w (append (pcko-rowwords prog 0 0 0 0 0 0)
                                   (append (adt-tp-zeros (- 16384 (len (pcko-rw0 (fn-pck-root-tree configs recs)))))
                                           (append (pcko-tws recs) (adt-tp-zeros (adt-tp-pad (len (pcko-tws recs))))))))
                  (<= (+ 2 (adt-tp-npk (len prog))) 16384)
                  (pcko-ok-treep (fn-scc-decode-tree prog))
                  (equal (cadr (fn-scc-decode-tree prog)) (fn-pck-root-tree configs recs))
                  (equal (nthcdr 16384 w) (append (pcko-tws recs) (adt-tp-zeros (adt-tp-pad (len (pcko-tws recs))))))
                  (fn-pck-sccb-listp recs (fn-pck-seed)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(car-cons cdr-cons pcko-ok-treep (:executable-counterpart consp) (:executable-counterpart equal)) (theory 'minimal-theory))
           :use (pcko-w-shape pcko-w-tape pcko-len-w pcko-flat-true-listp pcko-npg-ok pcko-root-fits-in-region
                 (:instance pcko-decode-of-program (x (fn-pck-root-tree configs recs)))
                 (:instance pck-program-octetsp (x (fn-pck-root-tree configs recs)))
                 pck-recordsp-parts pcko-recordsp-root))))

(defthm pcko-sim-not-bad
  (implies (and (fn-pck-sccb-listp recs (fn-pck-seed)) (not (equal (fn-pck-st-of (fn-pck-seed) recs) :bad)))
           (not (equal (car (pcko-sim recs 0 (fn-pck-seed) (fn-pck-seed) fid a)) :bad)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable pcko-sim pcko-agree fn-pck-st-of fn-pck-seed)
           :use ((:instance pcko-sim-is-the-fold (st (fn-pck-seed)) (acc (fn-pck-seed)) (base 0) (b a)
                            (recs recs))
                 (:instance fn-ssr-seed-establishes-statep (identity (fn-stxk-initial-context 0)))
                 pcko-sccb-listp-true-listp))))

(defthm pcko-tape-top
  ; The tape from the first word past the root region, over the whole image.
  (implies (and (pcko-img w pgs-mem) (true-listp w) (natp npg) (equal (len w) (* 2048 npg))
                (<= 16384 (* 2048 npg)) (natp reads)
                (equal tws (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from recs 0 (fn-pck-seed))))
                (equal (nthcdr 16384 w) (append tws zp)) (or (atom zp) (not (equal (car zp) 1)))
                (fn-pck-sccb-listp recs (fn-pck-seed))
                (not (equal (car (pcko-sim recs 0 (fn-pck-seed) (fn-pck-seed) fid a)) :bad)))
           (let ((r (pcko-tape 16384 (* 2048 npg) (fn-pck-seed) reads fid pgs-mem a oct))
                 (s (pcko-sim recs 0 (fn-pck-seed) (fn-pck-seed) fid a)))
             (and (equal (mv-nth 0 r) :ok)
                  (equal (mv-nth 1 r) (car s))
                  (equal (mv-nth 2 r) (+ reads (len tws) (if (consp zp) 1 0)))
                  (equal (mv-nth 3 r) (cadr s)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable pcko-tape pcko-sim pcko-img adt-tp-zeros nthcdr (:executable-counterpart nthcdr) fn-pck-seed
                               fn-pck-rows-from adt-tp-seq-words pcko-tape-of-recs)
           :use ((:instance pcko-tape-of-recs (pos 16384) (st (fn-pck-seed)) (base 0) (acc (fn-pck-seed)) (post zp)
                            (fn-octets oct) (fn-arena a))))))

(defthm pcko-npk-plus2 (natp (+ 2 (adt-tp-npk n))))

; mv-nth by its positions, for the proofs that run in a minimal theory.
(defthm pcko-mvn0 (equal (mv-nth 0 x) (car x)))
(defthm pcko-mvn1 (equal (mv-nth 1 x) (car (cdr x))))
(defthm pcko-mvn2 (equal (mv-nth 2 x) (car (cdr (cdr x)))))
(defthm pcko-mvn3 (equal (mv-nth 3 x) (car (cdr (cdr (cdr x))))))
(defthm pcko-mvn4 (equal (mv-nth 4 x) (car (cdr (cdr (cdr (cdr x)))))))
(defthm pcko-mvn5 (equal (mv-nth 5 x) (car (cdr (cdr (cdr (cdr (cdr x))))))))
(in-theory (disable pcko-mvn0 pcko-mvn1 pcko-mvn2 pcko-mvn3 pcko-mvn4 pcko-mvn5))

(defthm pcko-open-abstract
  (implies (and (pcko-img w pgs-mem) (true-listp w) (natp npg) (<= 8 npg) (equal (len w) (* 2048 npg))
                (<= (* 2048 npg) (pgs-x-len 0 pgs-mem)) (natp fid)
                (adt-octetsp prog) (equal w (append (pcko-rowwords prog 0 0 0 0 0 0) rest))
                (<= (+ 2 (adt-tp-npk (len prog))) 16384)
                (pcko-ok-treep (fn-scc-decode-tree prog))
                (equal tws (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from recs 0 (fn-pck-seed))))
                (equal (nthcdr 16384 w) (append tws zp)) (or (atom zp) (not (equal (car zp) 1)))
                (fn-pck-sccb-listp recs (fn-pck-seed))
                (not (equal (fn-pck-st-of (fn-pck-seed) recs) :bad)))
           (let ((r (fn-pck-x-open npg pgs-mem fid a octets))
                 (s (pcko-sim recs 0 (fn-pck-seed) (fn-pck-seed) fid a))
                 (root (cadr (fn-scc-decode-tree prog))))
             (and (equal (mv-nth 0 r) :ok)
                  (not (equal (mv-nth 0 s) :bad))
                  (equal (mv-nth 1 r) (fn-ssr-rows (mv-nth 0 s)))
                  (equal (mv-nth 2 r) (list (pcko-nth 0 root) (pcko-nth 1 root) (pcko-nth 2 root) (pcko-nth 3 root)))
                  (equal (mv-nth 3 r) (+ 2 (adt-tp-npk (len prog)) (len tws) (if (consp zp) 1 0)))
                  (equal (mv-nth 4 r) (mv-nth 1 s)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '((:executable-counterpart natp) (:executable-counterpart zp)
                                        (:executable-counterpart binary-+) (:executable-counterpart not)
                                        (:executable-counterpart unary--)
                                        pcko-mvn0 pcko-mvn1 pcko-mvn2 pcko-mvn3 pcko-mvn4 pcko-mvn5
                                        fn-pck-seed car-cons cdr-cons)
                                      (theory 'minimal-theory))
           :use ((:instance pcko-open-form (octets octets))
                 (:instance pcko-tape-top (reads (+ 2 (adt-tp-npk (len prog)))) (oct prog))
                 (:instance pcko-sim-not-bad) (:instance pcko-npk-natp (n (len prog)))
                 (:instance pcko-npk-plus2 (n (len prog)))))))

(defthm pcko-img-intro
  (implies (and (equal (pgs-x-words 0 0 k pgs-mem) w) (equal (len w) k)) (pcko-img w pgs-mem))
  :hints (("Goal" :in-theory (enable pcko-img))))

(defthm pcko-open-model
  ; The exec open of the image the writer's pages flatten to: the rows are the
  ; fold of the ref-step over the records, the roots are the root tree's four
  ; fold roots, the words read are the root row, the tape once and one more.
  (implies (and (fn-pck-recordsp configs recs) (fn-pck-root-fitsp configs recs)
                (equal npg (len (fn-pck-pages configs recs)))
                (pcko-img (adt-tp-flat (fn-pck-pages configs recs)) pgs-mem)
                (<= (* 2048 npg) (pgs-x-len 0 pgs-mem)) (natp fid))
           (let ((x (fn-pck-root-tree configs recs))
                 (r (fn-pck-x-open npg pgs-mem fid a octets))
                 (s (pcko-sim recs 0 (fn-pck-seed) (fn-pck-seed) fid a)))
             (and (equal (mv-nth 0 r) :ok)
                  (not (equal (mv-nth 0 s) :bad))
                  (equal (mv-nth 1 r) (fn-ssr-rows (mv-nth 0 s)))
                  (equal (mv-nth 2 r) (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x)))
                  (equal (mv-nth 3 r)
                         (+ 2 (adt-tp-npk (len (fn-scc-program x))) (len (pcko-tws recs))
                            (if (consp (adt-tp-zeros (adt-tp-pad (len (pcko-tws recs))))) 1 0)))
                  (equal (mv-nth 4 r) (mv-nth 1 s)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(pcko-nth-is-nth car-cons cdr-cons (:executable-counterpart consp))
                                      (theory 'minimal-theory))
           :use ((:instance pcko-image-facts)
                 (:instance pcko-open-abstract (w (adt-tp-flat (fn-pck-pages configs recs)))
                            (prog (fn-scc-program (fn-pck-root-tree configs recs)))
                            (rest (append (adt-tp-zeros (- 16384 (len (pcko-rw0 (fn-pck-root-tree configs recs)))))
                                          (append (pcko-tws recs) (adt-tp-zeros (adt-tp-pad (len (pcko-tws recs)))))))
                            (tws (pcko-tws recs)) (zp (adt-tp-zeros (adt-tp-pad (len (pcko-tws recs)))))
                            (octets octets) (a a))
                 pcko-tws-is-rows-from pck-recordsp-parts pcko-root-tree-true-listp
                 (:instance adt-tp-car-zeros (n (adt-tp-pad (len (pcko-tws recs)))))))))

; -----------------------------------------------------------------------------
; The rows read back as the records.  The seal survival lemmas are store-intern's
; local ones, restated.

(defthm pcko-row-wire-of-survives-seal
  (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp (list row) fn-arena))
           (equal (fn-row-wire-of row (fn-arena-seal-list xs fn-arena))
                  (fn-row-wire-of row fn-arena)))
  :hints (("Goal" :in-theory (enable fn-row-wire-of fn-rows-handles-inp fn-held-wire-of
                                     fn-row-handle-inp fn-row-bytes))))

(defthm pcko-rows-handles-survive-seal
  (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp rows fn-arena))
           (fn-rows-handles-inp rows (fn-arena-seal-list xs fn-arena)))
  :hints (("Goal" :induct (fn-rows-handles-inp rows fn-arena)
           :in-theory (enable fn-rows-handles-inp))))

(defthm pcko-rows-wire-of-survives-seal
  (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp rows fn-arena))
           (equal (fn-rows-wire-of rows (fn-arena-seal-list xs fn-arena))
                  (fn-rows-wire-of rows fn-arena)))
  :hints (("Goal" :induct (fn-rows-handles-inp rows fn-arena)
           :in-theory (enable fn-rows-handles-inp fn-rows-wire-of fn-row-wire-of))))

(defthm pcko-intern-event-wire-p
  (implies (not (eq (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad))
           (fn-wire-event-p w))
  :hints (("Goal" :in-theory (e/d (fn-intern-event fn-wire-event-p)
                                  (fn-cat-intern-list fn-replay-composite-record)))))

(defthm pcko-rows-survive-intern-event
  (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp rows fn-arena))
           (and (fn-rows-handles-inp rows (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))
                (equal (fn-rows-wire-of rows (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))
                       (fn-rows-wire-of rows fn-arena))))
  :hints (("Goal" :use ((:instance fn-intern-event-arena)
                        (:instance pcko-rows-handles-survive-seal
                                   (xs (fn-record-payload w)))
                        (:instance pcko-rows-wire-of-survives-seal
                                   (xs (fn-record-payload w)))
                        (:instance pcko-rows-handles-survive-seal
                                   (xs (fn-record-payload (fn-replay-composite-record w))))
                        (:instance pcko-rows-wire-of-survives-seal
                                   (xs (fn-record-payload (fn-replay-composite-record w)))))
           :in-theory (disable fn-intern-event-arena pcko-rows-handles-survive-seal
                               pcko-rows-wire-of-survives-seal fn-intern-event))))

(defthm pcko-arena-p-of-intern-event
  (implies (and (fn-arena-p fn-arena)
                (not (eq (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad)))
           (fn-arena-p (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
  :hints (("Goal" :use ((:instance pcko-intern-event-wire-p)
                        (:instance fn-intern-events-arena-p (ws (list w))))
           :in-theory (e/d (fn-intern-events fn-wire-event-listp)
                           (pcko-intern-event-wire-p fn-intern-events-arena-p
                            fn-intern-event fn-wire-event-p fn-record-p)))))

(defthm pcko-handles-of-cons
  (implies (syntaxp (not (equal rs ''nil)))
           (equal (fn-rows-handles-inp (cons r rs) fn-arena)
                  (and (fn-rows-handles-inp (list r) fn-arena) (fn-rows-handles-inp rs fn-arena))))
  :hints (("Goal" :in-theory (enable fn-rows-handles-inp))))

(defthm pcko-intern-event-one
  (implies (and (fn-arena-p fn-arena) (natp generation) (fn-rows-handles-inp rows fn-arena)
                (not (eq (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad)))
           (let ((row (mv-nth 0 (fn-intern-event w keyring generation fn-arena)))
                 (ar1 (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
             (and (fn-arena-p ar1)
                  (fn-rows-handles-inp (cons row rows) ar1)
                  (equal (fn-rows-wire-of (cons row rows) ar1)
                         (cons w (fn-rows-wire-of rows fn-arena))))))
  :hints (("Goal" :in-theory (e/d (fn-rows-wire-of)
                                  (fn-intern-event pcko-rows-survive-intern-event
                                   fn-intern-event-handle-in fn-intern-event-materializes
                                   fn-rows-handles-inp fn-row-wire-of))
           :use ((:instance pcko-rows-survive-intern-event)
                 (:instance fn-intern-event-handle-in)
                 (:instance fn-intern-event-materializes)
                 (:instance pcko-arena-p-of-intern-event)
                 (:instance pcko-handles-of-cons (r (mv-nth 0 (fn-intern-event w keyring generation fn-arena)))
                            (rs rows) (fn-arena (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))))))

(defthm pcko-arena-p-of-seal-extent
  (implies (and (fn-arena-p a) (natp fid) (natp off) (natp len) (<= 37 off) (natp trailer))
           (fn-arena-p (fn-arena-seal-extent fid (- off 37) (+ len 37) off len trailer a)))
  :hints (("Goal" :use ((:instance fn-arena-seal-extent{preserved} (file fid) (eoff (- off 37)) (elen (+ len 37))
                                   (poff off) (plen len) (fn-arena a)))
           :in-theory (e/d (fn-arn-extent-guardp fn-arena-p fn-arena-seal-extent) (fn-arena-seal-extent-is-append fn-arena-p-is-payload-listp)))))

(defthm pcko-row-wire-of-survives-extent
  (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp (list row) fn-arena))
           (equal (fn-row-wire-of row (fn-arena-seal-extent file eoff elen poff plen trailer fn-arena))
                  (fn-row-wire-of row fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-row-wire-of fn-rows-handles-inp fn-held-wire-of fn-row-handle-inp fn-row-bytes)
                                  (fn-arena-seal-extent-is-append fn-arena-seal-extent))
           :use ((:instance fn-arena-seal-extent-payload (h (fn-record-payload row)))
                 (:instance fn-arena-seal-extent-payload (h (fn-record-payload (fn-hstxa-held row))))))))

(defthm pcko-rows-handles-survive-extent
  (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp rows fn-arena))
           (fn-rows-handles-inp rows (fn-arena-seal-extent file eoff elen poff plen trailer fn-arena)))
  :hints (("Goal" :induct (fn-rows-handles-inp rows fn-arena)
           :in-theory (e/d (fn-rows-handles-inp fn-row-handle-inp) (fn-arena-seal-extent-is-append fn-arena-seal-extent)))))

(defthm pcko-rows-wire-of-survives-extent
  (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp rows fn-arena))
           (equal (fn-rows-wire-of rows (fn-arena-seal-extent file eoff elen poff plen trailer fn-arena))
                  (fn-rows-wire-of rows fn-arena)))
  :hints (("Goal" :induct (fn-rows-handles-inp rows fn-arena)
           :in-theory (e/d (fn-rows-handles-inp fn-rows-wire-of) (fn-arena-seal-extent-is-append fn-arena-seal-extent)))))

; -----------------------------------------------------------------------------
; The durable payload file holds the model file: a resolved ref reads back the
; payload through `fn-durable-octets' (s-cpl's cpl-holds-gen, restated).

(defun pcko-ind-a (file f off len)
  (if (zp len) (list file f off) (pcko-ind-a file (cdr f) (+ 1 (nfix off)) (1- len))))

(defthm pcko-holds-at
  (implies (and (fn-cpl-holdsp file f off) (natp off) (natp len) (<= len (len f)))
           (equal (fn-durable-octets file off len) (take len f)))
  :hints (("Goal" :induct (pcko-ind-a file f off len)
           :in-theory (enable fn-durable-octets-unfold))))

(defun pcko-ind-s (f i k)
  (if (zp k) (list f i) (pcko-ind-s (cdr f) (+ 1 (nfix i)) (1- k))))

(defthm pcko-holds-shift
  (implies (and (fn-cpl-holdsp file f i) (natp i) (natp k) (<= k (len f)))
           (fn-cpl-holdsp file (nthcdr k f) (+ i k)))
  :hints (("Goal" :induct (pcko-ind-s f i k))))

(defthm pcko-holds-gen
  (implies (and (fn-cpl-holdsp file f 0) (natp off) (natp len) (<= (+ off len) (len f)))
           (equal (fn-durable-octets file off len) (take len (nthcdr off f))))
  :hints (("Goal" :use ((:instance pcko-holds-shift (i 0) (k off))
                        (:instance pcko-holds-at (f (nthcdr off f)))
                        (:instance pcko-len-nthcdr-in (pos off) (w f)))
           :in-theory (disable pcko-holds-shift pcko-holds-at pcko-len-nthcdr-in))))

(defthm pcko-resolve-bound
  (implies (and (natp o) (natp l) (true-listp pay) (true-listp file)
                (equal (fn-cpl-resolve (fn-cpl-ref o l) file) pay))
           (and (<= (+ o l) (len file)) (equal pay (take l (nthcdr o file)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cpl-resolve fn-cpl-ref fn-cpl-refp) ()))))

(defthm pcko-holds-resolves
  (implies (and (fn-cpl-holdsp fid file 0) (true-listp file) (natp o) (natp l) (true-listp pay)
                (equal (fn-cpl-resolve (fn-cpl-ref o l) file) pay))
           (equal (fn-durable-octets fid o l) pay))
  :hints (("Goal" :in-theory (disable pcko-holds-gen fn-cpl-resolve fn-cpl-ref)
           :use (pcko-resolve-bound (:instance pcko-holds-gen (file fid) (off o) (len l) (f file))))))

(defthm pcko-held-wire-of-reseat
  (equal (fn-held-wire (pcko-reseat r h) pay) (fn-held-wire r pay))
  :hints (("Goal" :in-theory (enable pcko-reseat fn-held-wire))))

(defthm pcko-publish-rows
  (implies (fn-ssr-statep acc)
           (equal (fn-ssr-at 0 (fn-ssr-publish acc row wire identity)) (cons row (fn-ssr-at 0 acc))))
  :hints (("Goal" :in-theory (enable fn-ssr-publish fn-ssr-state fn-ssr-at))))

(defthm pcko-reseat-handle
  (equal (fn-record-payload (pcko-reseat r h)) h)
  :hints (("Goal" :in-theory (enable pcko-reseat))))

(defthm pcko-extent-wires
  ; The row sealed at the arena's count reads back the durable octets; the rows
  ; below it read back what they did.
  (implies (and (fn-held-p row) (equal (fn-record-payload row) (fn-arena-count a)) (fn-arena-p a)
                (fn-rows-handles-inp rows a))
           (let ((a2 (fn-arena-seal-extent file eoff elen poff plen trailer a)))
             (and (fn-arena-p a2)
                  (fn-rows-handles-inp (cons row rows) a2)
                  (equal (fn-rows-wire-of (cons row rows) a2)
                         (cons (fn-held-wire row (fn-durable-octets file poff plen))
                               (fn-rows-wire-of rows a))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-rows-wire-of fn-row-wire-of fn-held-wire-of fn-row-handle-inp fn-row-bytes)
                           (fn-arena-seal-extent fn-arena-seal-extent-is-append fn-held-p pcko-handles-of-cons
                            pcko-rows-wire-of-survives-extent pcko-rows-handles-survive-extent))
           :use ((:instance fn-arena-seal-extent-payload (fn-arena a) (h (fn-arena-count a)))
                 (:instance pcko-count-seal-extent (fn-arena a))
                 (:instance pcko-rows-wire-of-survives-extent (fn-arena a))
                 (:instance pcko-rows-handles-survive-extent (fn-arena a))
                 (:instance pcko-handles-of-cons (r row) (rs rows) (fn-arena (fn-arena-seal-extent file eoff elen poff plen trailer a)))
                 (:instance pcko-count-natp (a a))))))
(defthm pcko-ref-wires-held
  (implies (and (fn-held-p r) (<= 37 off) (fn-ssr-statep acc) (fn-arena-p a) (natp fid) (natp len) (natp off)
                (fn-rows-handles-inp (fn-ssr-at 0 acc) a)
                (equal (fn-durable-octets fid off len) pay) (equal (fn-held-wire r pay) w)
                (not (equal (mv-nth 0 (pcko-ref-step acc (list :r r) off len d0 d1 d2 d3 fid a)) :bad)))
           (let ((acc2 (mv-nth 0 (pcko-ref-step acc (list :r r) off len d0 d1 d2 d3 fid a)))
                 (a2 (mv-nth 1 (pcko-ref-step acc (list :r r) off len d0 d1 d2 d3 fid a))))
             (and (fn-arena-p a2)
                  (fn-rows-handles-inp (fn-ssr-at 0 acc2) a2)
                  (equal (fn-rows-wire-of (fn-ssr-at 0 acc2) a2)
                         (cons w (fn-rows-wire-of (fn-ssr-at 0 acc) a))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable pcko-ref-step-held pcko-ref-step fn-arena-seal-extent fn-ssr-publish fn-replay-identity-step
                               fn-ssr-at fn-stxk-context-kind pcko-reseat fn-held-p pcko-extent-wires pcko-publish-rows)
           :use ((:instance pcko-ref-step-held (len len))
                 (:instance pcko-extent-wires (row (pcko-reseat r (fn-arena-count a))) (rows (fn-ssr-at 0 acc))
                            (file fid) (eoff (- off 37)) (elen (+ len 37)) (poff off) (plen len)
                            (trailer (fn-arx-trailer-nat (fn-cpl-unpack-words (list d0 d1 d2 d3)))))
                 (:instance pcko-publish-rows (row (pcko-reseat r (fn-arena-count a))) (wire (pcko-reseat r (fn-arena-count a)))
                            (identity (fn-replay-identity-step (fn-ssr-at 3 acc) (pcko-reseat r (fn-arena-count a)))))
                 (:instance pcko-held-wire-of-reseat (h (fn-arena-count a)) (r r) (pay pay))
                 (:instance pcko-reseat-handle (h (fn-arena-count a)))
                 (:instance pcko-reseat-held-p (row r) (h (fn-arena-count a)))
                 (:instance pcko-count-natp (a a))))))

(defthm pcko-f1-wires
  ; One event of full recovery's fold: the new row reads back the event.
  (implies (and (fn-ssr-statep acc) (fn-arena-p a) (fn-rows-handles-inp (fn-ssr-at 0 acc) a)
                (not (equal (mv-nth 0 (fn-ssr-intern-step acc (list w) nil nil :resident nil a)) :bad)))
           (let ((acc2 (mv-nth 0 (fn-ssr-intern-step acc (list w) nil nil :resident nil a)))
                 (a2 (mv-nth 1 (fn-ssr-intern-step acc (list w) nil nil :resident nil a))))
             (and (fn-arena-p a2)
                  (fn-rows-handles-inp (fn-ssr-at 0 acc2) a2)
                  (equal (fn-rows-wire-of (fn-ssr-at 0 acc2) a2)
                         (cons w (fn-rows-wire-of (fn-ssr-at 0 acc) a))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-intern-event fn-ssr-publish fn-replay-identity-step fn-ssr-at fn-stxk-context-kind
                               fn-ssr-intern-step pcko-f1 pcko-intern-event-one pcko-publish-rows)
           :use ((:instance pcko-f1 (a a))
                 (:instance pck-statep-generation)
                 (:instance pcko-intern-event-one (keyring (fn-ssr-at 1 acc)) (generation (fn-ssr-at 2 acc))
                            (fn-arena a) (rows (fn-ssr-at 0 acc)))
                 (:instance pcko-publish-rows (row (mv-nth 0 (fn-intern-event w (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) a)))
                            (wire w)
                            (identity (fn-replay-identity-step (fn-ssr-at 3 acc)
                                                                (mv-nth 0 (fn-intern-event w (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) a)))))))))

(defthm pcko-ref-is-intern-step-other
  (implies (not (fn-record-p w))
           (equal (pcko-ref acc w base st fid a)
                  (fn-ssr-intern-step acc (list w) nil nil :resident nil a)))
  :hints (("Goal" :in-theory (union-theories '(pcko-meta-of-other pcko-ref-step-other pcko-recp-of-o pcko-ev-of-list pcko-ref)
                                             (theory 'minimal-theory)))))

(defthm pcko-payload-of-record
  (implies (fn-record-p w) (equal (fn-pck-payload w) (fn-record-payload w)))
  :hints (("Goal" :in-theory (enable fn-pck-payload))))

(defthm pcko-ref-wires
  (implies (and (pcko-agree acc st) (natp base) (natp fid) (not (equal (pck-ssr1 st w) :bad)) (fn-arena-p a)
                (fn-rows-handles-inp (fn-ssr-at 0 acc) a)
                (equal (fn-durable-octets fid (+ 37 base) (len (fn-pck-payload w))) (fn-pck-payload w))
                (not (equal (mv-nth 0 (pcko-ref acc w base st fid a)) :bad)))
           (let ((acc2 (mv-nth 0 (pcko-ref acc w base st fid a)))
                 (a2 (mv-nth 1 (pcko-ref acc w base st fid a))))
             (and (fn-arena-p a2)
                  (fn-rows-handles-inp (fn-ssr-at 0 acc2) a2)
                  (equal (fn-rows-wire-of (fn-ssr-at 0 acc2) a2)
                         (cons w (fn-rows-wire-of (fn-ssr-at 0 acc) a))))))
  :hints (("Goal" :do-not-induct t
           :expand ((pcko-ref acc w base st fid a))
           :in-theory (e/d (pcko-agree) (pcko-ref pcko-ref-step pck-row0-wire pck-row0-is-the-row fn-held-p fn-pck-row0
                                         pcko-ref-wires-held pcko-f1-wires pcko-ref-is-intern-step-other pck-ssr1
                                         fn-ssr-intern-step fn-record-p fn-pck-payload))
           :use ((:instance pcko-ref-is-intern-step-other)
                 (:instance pcko-f1-wires)
                 (:instance pcko-meta-of-record)
                 (:instance pck-row0-wire)
                 (:instance pcko-ref-wires-held (r (fn-pck-row0 st w)) (off (+ 37 base)) (len (len (fn-pck-payload w)))
                            (pay (fn-pck-payload w)) (d0 (car (pcko-tw w))) (d1 (cadr (pcko-tw w)))
                            (d2 (caddr (pcko-tw w))) (d3 (cadddr (pcko-tw w))))))))

(defun pcko-durablep (recs base fid)
  ; The durable payload file holds each record's payload at its ref.
  (declare (xargs :guard (natp base) :verify-guards nil))
  (if (atom recs)
      t
    (and (equal (fn-durable-octets fid (+ *fn-cpl-header-octets* base) (len (fn-pck-payload (car recs))))
                (fn-pck-payload (car recs)))
         (pcko-durablep (cdr recs) (pcko-next-base (car recs) base) fid))))

(defthm pcko-durablep-of-resolves
  (implies (and (fn-cpl-holdsp fid file 0) (true-listp file) (natp base) (fn-pck-resolvesp recs base file))
           (pcko-durablep recs base fid))
  :hints (("Goal" :induct (pcko-durablep recs base fid)
           :expand ((fn-pck-resolvesp recs base file))
           :in-theory (e/d (pcko-next-base) (fn-pck-payload fn-cpl-resolve fn-cpl-ref fn-pck-resolvesp)))
          ("Subgoal *1/3" :use ((:instance pcko-holds-resolves (o (+ 37 base)) (l (len (fn-pck-payload (car recs))))
                                           (pay (fn-pck-payload (car recs))))
                                (:instance pck-payload-true-listp (w (car recs)))))))

(defun-nx pcko-w-ind (recs base st acc fid a)
  (if (atom recs)
      a
    (let ((acc2 (mv-nth 0 (pcko-ref acc (car recs) base st fid a)))
          (a2 (mv-nth 1 (pcko-ref acc (car recs) base st fid a))))
      (if (eq acc2 :bad)
          a
        (pcko-w-ind (cdr recs) (pcko-next-base (car recs) base) (pck-ssr1 st (car recs)) acc2 fid a2)))))

(defthm pcko-wires-cons-step
  (let* ((w1 (car recs))
         (ref (pcko-ref acc w1 base st fid a))
         (acc2 (mv-nth 0 ref))
         (a2 (mv-nth 1 ref))
         (st1 (pck-ssr1 st w1))
         (base1 (pcko-next-base w1 base)))
    (implies (and (consp recs) (true-listp recs) (pcko-agree acc st) (natp base) (natp fid)
                  (not (equal (fn-pck-st-of st recs) :bad))
                  (fn-arena-p a) (fn-rows-handles-inp (fn-ssr-at 0 acc) a)
                  (pcko-durablep recs base fid)
                  (implies (and (true-listp (cdr recs)) (pcko-agree acc2 st1) (natp base1) (natp fid)
                                (not (equal (fn-pck-st-of st1 (cdr recs)) :bad))
                                (fn-arena-p a2) (fn-rows-handles-inp (fn-ssr-at 0 acc2) a2)
                                (pcko-durablep (cdr recs) base1 fid))
                           (let ((s (pcko-sim (cdr recs) base1 st1 acc2 fid a2)))
                             (and (fn-arena-p (mv-nth 1 s))
                                  (fn-rows-handles-inp (fn-ssr-at 0 (mv-nth 0 s)) (mv-nth 1 s))
                                  (equal (fn-rows-wire-of (fn-ssr-at 0 (mv-nth 0 s)) (mv-nth 1 s))
                                         (revappend (cdr recs) (fn-rows-wire-of (fn-ssr-at 0 acc2) a2)))))))
             (let ((s (pcko-sim recs base st acc fid a)))
               (and (fn-arena-p (mv-nth 1 s))
                    (fn-rows-handles-inp (fn-ssr-at 0 (mv-nth 0 s)) (mv-nth 1 s))
                    (equal (fn-rows-wire-of (fn-ssr-at 0 (mv-nth 0 s)) (mv-nth 1 s))
                           (revappend recs (fn-rows-wire-of (fn-ssr-at 0 acc) a)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable pcko-ref pck-ssr1 pcko-agree pcko-next-base fn-pck-st-of pcko-sim pcko-durablep
                               pcko-step-agree pcko-ref-wires fn-ssr-intern-step)
           :expand ((pcko-sim recs base st acc fid a) (fn-pck-st-of st recs) (pcko-durablep recs base fid))
           :use ((:instance pcko-ref-is-the-step (w (car recs)) (b a))
                 (:instance pcko-step-agree (w (car recs)) (b a))
                 (:instance pcko-ref-wires (w (car recs)))))))

(defthm pcko-sim-wires
  ; The rows the tape's fold leaves read back as the records, in order.
  (implies (and (true-listp recs) (pcko-agree acc st) (natp base) (natp fid)
                (not (equal (fn-pck-st-of st recs) :bad))
                (fn-arena-p a) (fn-rows-handles-inp (fn-ssr-at 0 acc) a)
                (pcko-durablep recs base fid))
           (let ((s (pcko-sim recs base st acc fid a)))
             (and (fn-arena-p (mv-nth 1 s))
                  (fn-rows-handles-inp (fn-ssr-at 0 (mv-nth 0 s)) (mv-nth 1 s))
                  (equal (fn-rows-wire-of (fn-ssr-at 0 (mv-nth 0 s)) (mv-nth 1 s))
                         (revappend recs (fn-rows-wire-of (fn-ssr-at 0 acc) a))))))
  :hints (("Goal" :induct (pcko-w-ind recs base st acc fid a) :do-not-induct t
           :in-theory (disable pcko-ref pck-ssr1 pcko-agree pcko-next-base fn-pck-st-of pcko-sim pcko-durablep
                               fn-ssr-intern-step))
          ("Subgoal *1/3" :use pcko-wires-cons-step)
          ("Subgoal *1/2" :expand ((fn-pck-st-of st recs))
           :use ((:instance pcko-ref-is-the-step (w (car recs)) (b a)) (:instance pcko-step-agree (w (car recs)) (b a))))
          ("Subgoal *1/1" :in-theory (e/d (pcko-sim) (pcko-ref pck-ssr1 pcko-agree)))))

; -----------------------------------------------------------------------------
; THE KEYSTONES.

(defthm pcko-rows-wire-of-append
  (equal (fn-rows-wire-of (append a b) fn-arena)
         (append (fn-rows-wire-of a fn-arena) (fn-rows-wire-of b fn-arena)))
  :hints (("Goal" :induct (len a) :in-theory (enable fn-rows-wire-of))))

(defthm pcko-rows-wire-of-rev
  (equal (fn-rows-wire-of (rev a) fn-arena) (rev (fn-rows-wire-of a fn-arena)))
  :hints (("Goal" :induct (len a) :in-theory (enable fn-rows-wire-of))))

(defthm pcko-rows-wire-of-nil (equal (fn-rows-wire-of nil fn-arena) nil)
  :hints (("Goal" :in-theory (enable fn-rows-wire-of))))

(defthm pcko-rev-onto-is-revappend
  (equal (fn-ag-rev-onto x acc) (revappend x acc)))

(defthm pcko-wire-of-ssr-rows
  (implies (not (eq acc :bad))
           (equal (fn-rows-wire-of (fn-ssr-rows acc) fn-arena)
                  (revappend (fn-rows-wire-of (fn-ssr-at 0 acc) fn-arena) nil)))
  :hints (("Goal" :in-theory (e/d (fn-ssr-rows) (fn-ssr-at)))))

(defthm pcko-seed-rows
  (equal (fn-ssr-at 0 (fn-ssr-seed identity)) nil)
  :hints (("Goal" :in-theory (enable fn-ssr-seed fn-ssr-state fn-ssr-at))))

(defthm pcko-pck-seed-rows (equal (fn-ssr-at 0 (fn-pck-seed)) nil)
  :hints (("Goal" :in-theory (enable fn-pck-seed))))

(defthm pcko-handles-of-nil (fn-rows-handles-inp nil a)
  :hints (("Goal" :in-theory (enable fn-rows-handles-inp))))

(defthm pcko-seed-agree (pcko-agree (fn-pck-seed) (fn-pck-seed))
  :hints (("Goal" :in-theory (e/d (pcko-agree fn-pck-seed) ())
           :use (:instance fn-ssr-seed-establishes-statep (identity (fn-stxk-initial-context 0))))))

(defthm pcko-revappend-twice (implies (true-listp x) (equal (revappend (revappend x nil) nil) x)))

(defthm pcko-revappend-rev (equal (rev (revappend x nil)) (true-list-fix x))
  :hints (("Goal" :in-theory (enable rev revappend))))

(defthm pcko-capture-fields
  (implies (and (fn-pck-recordsp configs recs) (fn-pck-root-fitsp configs recs) (fn-pck-resolvesp recs 0 file))
           (let ((c (fn-pck-capture-of-pages (fn-pck-pages configs recs) file))
                 (x (fn-pck-root-tree configs recs)))
             (and (equal (fn-sco-records c) recs)
                  (equal (list (fn-sco-cpr c) (fn-sco-identity c) (fn-sco-consumer c) (fn-sco-topic c))
                         (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-root-tree fn-pck-root-tree-of-capture fn-sco-capture)
                           (fn-pck-pages fn-pck-capture-of-pages pck-capture-of-pages))
           :use ((:instance pck-capture-of-pages)
                 (:instance pck-recordsp-parts)
                 pcko-sccb-listp-true-listp))))

(defun pcko-wind (a k) (if (zp k) a (pcko-wind (1+ a) (1- k))))

(defthm pcko-len-words
  (implies (natp k) (equal (len (pgs-x-words 0 a k pgs-mem)) k))
  :hints (("Goal" :induct (pcko-wind a k) :expand ((pgs-x-words 0 a k pgs-mem))
           :in-theory (enable pgs-x-words))))

(defthm fn-pck-x-open-is-the-capture
  ; KEYSTONE.  The exec open of the image the writer's pages flatten to
  ; answers the capture `fn-pck-capture-of-pages' makes of those pages, against
  ; the durable payload file FID that holds the model file FILE: the verdict is
  ; :ok; the rows are the rows full recovery interns for the same records (the
  ; held rows the tape carries, reseated; no payload read); read back through
  ; the arena the open leaves (the payloads sealed BY REF to the durable file)
  ; they are the capture's records; the four fold roots are the capture's.
  ; Scope.  The image is given by its words: that every page was filled and
  ; verified before this open (the resident open) is the driver's premise; the
  ; lazy open (fill and verify per page) is owed (PCK-OPEN-SQUARE,
  ; PCK-STAGE-NEED-PAGE).  The event index is not rebuilt: the Store's index is
  ; retired (books/store-node.lisp, field 13) and nothing on the served path
  ; reads it.  The records intern from the initial identity context without a
  ; refusal by fn-pck-recordsp (PCK-OPEN-INTERN-NOT-BAD).
  (implies (and (fn-pck-recordsp configs recs) (fn-pck-root-fitsp configs recs)
                (equal npg (len (fn-pck-pages configs recs)))
                (equal (pgs-x-words 0 0 (* 2048 npg) pgs-mem) (adt-tp-flat (fn-pck-pages configs recs)))
                (<= (* 2048 npg) (pgs-x-len 0 pgs-mem))
                (natp fid) (fn-arena-p fn-arena)
                (true-listp file) (fn-pck-resolvesp recs 0 file) (fn-cpl-holdsp fid file 0))
           (let ((c (fn-pck-capture-of-pages (fn-pck-pages configs recs) file))
                 (r (fn-pck-x-open npg pgs-mem fid fn-arena fn-octets)))
             (and (equal (mv-nth 0 r) :ok)
                  (equal (mv-nth 1 r)
                         (fn-ssr-rows (mv-nth 0 (fn-ssr-intern-step (fn-pck-seed) recs nil nil :resident nil fn-arena))))
                  (equal (fn-rows-wire-of (mv-nth 1 r) (mv-nth 4 r)) (fn-sco-records c))
                  (equal (mv-nth 2 r)
                         (list (fn-sco-cpr c) (fn-sco-identity c) (fn-sco-consumer c) (fn-sco-topic c))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(pcko-pck-seed-rows pcko-handles-of-nil pcko-rows-wire-of-nil pcko-revappend-twice (:executable-counterpart natp)) (theory 'minimal-theory))
           :use ((:instance pcko-img-intro (k (* 2048 npg)) (w (adt-tp-flat (fn-pck-pages configs recs))))
                 pcko-len-w
                 (:instance pcko-open-model (a fn-arena) (octets fn-octets))
                 (:instance pcko-sim-is-the-fold (st (fn-pck-seed)) (acc (fn-pck-seed)) (base 0) (b fn-arena) (a fn-arena))
                 (:instance pcko-sim-wires (st (fn-pck-seed)) (acc (fn-pck-seed)) (base 0) (a fn-arena))
                 (:instance pcko-durablep-of-resolves (base 0))
                 pcko-capture-fields pck-recordsp-parts (:instance pcko-sccb-listp-true-listp (st (fn-pck-seed))) pcko-seed-agree
                 (:instance pcko-wire-of-ssr-rows (acc (mv-nth 0 (pcko-sim recs 0 (fn-pck-seed) (fn-pck-seed) fid fn-arena)))
                            (fn-arena (mv-nth 1 (pcko-sim recs 0 (fn-pck-seed) (fn-pck-seed) fid fn-arena))))))))

(defthm fn-pck-x-open-reads-bound
  ; KEYSTONE.  The words the open reads: the root row (under 8 pages) and the
  ; tape's own words once each, and the one word that is not a tag.  No term in
  ; the store, the arena, the prefix, the page count or the payloads: a row's
  ; payload is not read.
  (implies (and (fn-pck-recordsp configs recs) (fn-pck-root-fitsp configs recs)
                (equal npg (len (fn-pck-pages configs recs)))
                (equal (pgs-x-words 0 0 (* 2048 npg) pgs-mem) (adt-tp-flat (fn-pck-pages configs recs)))
                (<= (* 2048 npg) (pgs-x-len 0 pgs-mem)) (natp fid))
           (<= (mv-nth 3 (fn-pck-x-open npg pgs-mem fid fn-arena fn-octets))
               (+ (* 8 2048) (len (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows recs))) 1)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(pcko-tws) (theory 'minimal-theory))
           :cases ((consp (adt-tp-zeros (adt-tp-pad (len (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows recs)))))))
           :use ((:instance pcko-img-intro (k (* 2048 npg)) (w (adt-tp-flat (fn-pck-pages configs recs))))
                 pcko-len-w
                 (:instance pcko-open-model (a fn-arena) (octets fn-octets))
                 pcko-root-fits-in-region))))
