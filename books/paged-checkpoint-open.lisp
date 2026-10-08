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

(defun pcko-wellp (l)
  ; Every row of L lies within L and its metadata decodes.
  (declare (xargs :measure (len l) :verify-guards nil))
  (if (and (consp l) (equal (car l) 1))
      (and (consp (cdr l))
           (<= (+ 8 (adt-tp-npk (cadr l))) (len l))
           (pcko-ok-treep (fn-scc-decode-tree (adt-tp-unpack (cadr l) (cddr l))))
           (pcko-wellp (adt-tp-restf *fn-pck-row-schema* (cdr l))))
    t))

(defun pcko-cost (l)
  ; The words the open reads over L: each row's words, then the one word that
  ; is not a tag.
  (declare (xargs :measure (len l) :verify-guards nil))
  (cond ((atom l) 0)
        ((equal (car l) 1)
         (+ 8 (adt-tp-npk (cadr l)) (pcko-cost (adt-tp-restf *fn-pck-row-schema* (cdr l)))))
        (t 1)))

(defthm pcko-nthcdr-six
  (implies (natp n)
           (equal (nthcdr (+ 6 n) x) (nthcdr n (cdr (cdr (cdr (cdr (cdr (cdr x)))))))))
  :hints (("Goal" :in-theory (disable pck-nthcdr-nthcdr pgs-nthcdr-nthcdr pgs-cdr-nthcdr pgs-nthcdr-too-far)
           :expand ((nthcdr (+ 6 n) x) (nthcdr (+ 5 n) (cdr x)) (nthcdr (+ 4 n) (cdr (cdr x)))
                    (nthcdr (+ 3 n) (cdr (cdr (cdr x)))) (nthcdr (+ 2 n) (cdr (cdr (cdr (cdr x)))))
                    (nthcdr (+ 1 n) (cdr (cdr (cdr (cdr (cdr x))))))))))

(defthm pcko-restf-is-nthcdr
  (equal (adt-tp-restf *fn-pck-row-schema* w)
         (nthcdr (+ 6 (adt-tp-npk (car w))) (cdr w)))
  :hints (("Goal" :expand ((adt-tp-restf *fn-pck-row-schema* w))
           :in-theory (disable pcko-nthcdr-six)
           :use ((:instance pcko-nthcdr-six (n (adt-tp-npk (car w))) (x (cdr w)))))))

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
