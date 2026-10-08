; fn: checkpoint = dirty pages, open = root + log tail (lane s-pck, 2026-10-07;
; Phase 2a of build/coordinator/STORAGE-PROGRAM-20261006.md; owed items
; PCK-DELTA, PCK-BOUND, PCK-OPEN, PCK-CRASH).  Model level over the
; copy-on-write page store of books/pagestore.lisp; no host wiring.
;
; The page image of the recovered state after a record prefix is one page-store
; root: a ROOT region (the capture's four fold roots as one tree, zero padded to
; *fn-pck-root-pages* pages, rewritten whole by each checkpoint) followed by an
; EVENTS tape (one row per record, the record's tree program as the row's
; octets, appended by each checkpoint).  Both are `fn-pck-row', one
; (def-representation ... :pages t) instance (books/def-representation-pages.lisp):
; no codec or dirty-set function here is hand written.
;
;   fn-pck-dirty-is-the-delta   the dirty pages applied to the old image give the new image
;   fn-pck-dirty-bound          K plus the delta's own pages plus one; no term in the prefix
;   fn-pck-open-after-commit-is-full-recover
;                               commit, open the pages, resume over a suffix = the full open
;   fn-pck-crash-recovers-from-old-or-new
;                               a crash at any cut of the commit, any log kept from the old S on
;
; Scope, named.  (1) The events tape holds whole records, payload octets
; included; "payload written once to byte-pool pages and referenced" is
; D41-STAGE5-ONE-ROW-IMAGE.  (2) The catalog (fn-crow rows, msgid table, dense
; map) is NOT in this image: it is derived data and will live in its own page-
; store root, adopted only when its S matches (PCK-ADOPT, PCK-ADOPT-TAG), because
; two growing regions cannot share one root (pgs-apply-dirty drops a dirty page
; above the length reached).  (3) Premises, each inhabited in
; tests/acl2/paged-checkpoint-tests.lisp: every record and the fold roots are
; encodable trees (fn-pck-recordsp); the root fits K pages (fn-pck-root-fitsp),
; which is the host's named refusal to checkpoint (the log is kept); the
; accounted A-CRYPTO hypothesis pgs-writes-faithful.  PCK-ROOT-BOUND owes
; deriving K from the profile so that fitsp holds by construction.  (4) The
; delta and bound statements need no fitsp: the root region is cut or padded to
; exactly K pages.  (5) The log model is (START . TAIL), the records from index
; START on; recovery replays the tail from the checkpoint's S.

(in-package "ACL2")
(include-book "def-representation-pages")
(include-book "checkpoint-payload-ref")
(include-book "pagestore-keystones")
(include-book "owner-checkpoint-open")
(include-book "store-checkpoint-buffer")
(include-book "def-representation")
(include-book "def-representation-tree")
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "std/lists/append" :dir :system))

; -----------------------------------------------------------------------------
; 1. Dirty sets over a store whose first pages are another region.

(defthm pck-apply-dirty-append
  (equal (pgs-apply-dirty c (append d1 d2))
         (pgs-apply-dirty (pgs-apply-dirty c d1) d2))
  :hints (("Goal" :in-theory (enable pgs-apply-dirty)
           :induct (pgs-apply-dirty c d1))))

(defun pck-shift (k d)
  ; The dirty alist D with every page number moved K pages up.
  (declare (xargs :guard (and (natp k) (alistp d))))
  (if (atom d) nil (cons (cons (+ k (nfix (caar d))) (cdar d)) (pck-shift k (cdr d)))))

(defthm pck-len-shift
  (equal (len (pck-shift k d)) (len d)))

(defthm pck-shift-of-number
  (implies (and (natp k) (natp j))
           (equal (pck-shift k (adt-tp-number j ps)) (adt-tp-number (+ k j) ps))))

(defthm pck-update-nth-append
  (implies (and (true-listp r) (natp i))
           (equal (update-nth (+ (len r) i) x (append r c))
                  (append r (update-nth i x c))))
  :hints (("Goal" :in-theory (enable update-nth) :induct (len r))))

(defthm pck-apply-dirty-shift
  ; A region of K pages in front: a dirty set moved up K pages is applied behind it.
  (implies (and (true-listp r) (true-listp c))
           (equal (pgs-apply-dirty (append r c) (pck-shift (len r) d))
                  (append r (pgs-apply-dirty c d))))
  :hints (("Goal" :in-theory (enable pgs-apply-dirty)
           :induct (pgs-apply-dirty c d))))

(defun pck-region-ind (a b ps)
  (if (atom ps) (list a b) (pck-region-ind (append a (list (car ps))) (cdr b) (cdr ps))))

(defthm pck-apply-dirty-region
  ; The dirty pages numbered from the end of A, as many as B has, replace B and leave C.
  (implies (and (true-listp a) (true-listp b) (true-listp c) (true-listp ps)
                (equal (len b) (len ps)))
           (equal (pgs-apply-dirty (append a b c) (adt-tp-number (len a) ps))
                  (append a ps c)))
  :hints (("Goal" :in-theory (enable pgs-apply-dirty)
           :induct (pck-region-ind a b ps))))

(defthm pck-dirty-lpages-append
  (equal (pgs-dirty-lpages (append d1 d2))
         (append (pgs-dirty-lpages d1) (pgs-dirty-lpages d2)))
  :hints (("Goal" :in-theory (enable pgs-dirty-lpages))))

(defthm pck-lpages-ok-number-then
  ; Pages numbered from LO, within the N pages there are: what follows is judged from LO + their count.
  (implies (and (natp lo) (natp n) (<= (+ lo (len ps)) n))
           (equal (pgs-lpages-ok (append (pgs-dirty-lpages (adt-tp-number lo ps)) l2) n lo)
                  (pgs-lpages-ok l2 n (+ lo (len ps)))))
  :hints (("Goal" :in-theory (enable pgs-lpages-ok pgs-dirty-lpages)
           :induct (adt-tp-number lo ps))))

(defun pck-number-ind (k ps n lo)
  (if (atom ps) (list k n lo) (pck-number-ind (1+ k) (cdr ps) (if (equal k n) (1+ n) n) (1+ k))))

(defthm pck-lpages-ok-number
  ; Pages numbered from K at most N: strictly ascending from LO, each at most the length reached.
  (implies (and (natp k) (natp lo) (<= lo k) (natp n) (<= k n))
           (pgs-lpages-ok (pgs-dirty-lpages (adt-tp-number k ps)) n lo))
  :hints (("Goal" :in-theory (enable pgs-lpages-ok pgs-dirty-lpages)
           :induct (pck-number-ind k ps n lo))))

; -----------------------------------------------------------------------------
; 2. The page image of the recovered state after a record prefix.
;
; One page-store root holds, in logical pages,
;   [0, K)   the ROOT region: the capture's four fold roots (cpr, identity,
;            consumer, topic) as one tree, as one row of `fn-pck-row', zero
;            padded to exactly K pages, rewritten whole by every checkpoint;
;   [K, ...) the EVENTS tape: one `fn-pck-row' per record, the record's tree
;            program as the row's octets, appended by every checkpoint.
; The record sequence is the capture's RECORDS; the event index is rebuilt
; from it at open, as the checkpoint file's reader does.

; The schema facts the generator proves by evaluation: some books of this
; closure disable executable counterparts, so enable the two for the instance.
(local (in-theory (enable (:executable-counterpart adt-schemap)
                          (:executable-counterpart adt-ncols))))
;; D41-STAGE5-ONE-ROW-IMAGE: a tape row is the record's METADATA tree and a ref
;; (offset, length) to its payload in the append-only payload file
;; (books/checkpoint-payload-ref.lisp), not the payload octets.
(def-representation fn-pck-row (meta :tree) (off :u64) (len :u64) :pages t)

(defconst *fn-pck-root-pages* 8)

; Split a wire event into its metadata tree and its payload octets.  A record
; (fn-record-p) carries a payload; any other event has none.  The metadata of a
; record is the record with an empty payload, tagged :r; any other event is
; tagged :o.
(defun fn-pck-record-with-payload (w payload)
  (declare (xargs :guard (fn-record-p w) :verify-guards nil))
  (fn-record-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                  (fn-record-msgid w) payload (fn-record-groups w)
                  (fn-record-obligation-id w) (fn-record-content-subject w)
                  (fn-record-release-evidence w) (fn-record-charge w) (fn-record-stamp w)))

(defun fn-pck-meta (w)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-record-p w)
      (list :r (fn-pck-record-with-payload w nil))
    (list :o w)))

(defun fn-pck-payload (w)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-record-p w) (fn-record-payload w) nil))

(defun fn-pck-join (meta payload)
  ; The event METADATA and PAYLOAD denote.
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp meta) (eq (car meta) :r) (consp (cdr meta)) (fn-record-p (cadr meta)))
      (fn-pck-record-with-payload (cadr meta) payload)
    (if (and (consp meta) (consp (cdr meta))) (cadr meta) nil)))

(defun fn-pck-enc-row (w off)
  ; The row of event W whose payload frame starts at file offset OFF.
  (declare (xargs :guard t :verify-guards nil))
  (list (fn-scc-program (fn-pck-meta w)) off (len (fn-pck-payload w))))

(defun fn-pck-plen (recs base)
  ; The payload-file length after the frames of RECS laid end to end from BASE.
  (declare (xargs :guard (natp base) :verify-guards nil))
  (if (atom recs)
      base
    (fn-pck-plen (cdr recs) (+ base (fn-cpl-frame-octets (len (fn-pck-payload (car recs))))))))

(defun fn-pck-rows-from (recs base)
  (declare (xargs :guard (natp base) :verify-guards nil))
  (if (atom recs)
      nil
    (cons (fn-pck-enc-row (car recs) base)
          (fn-pck-rows-from (cdr recs)
                            (+ base (fn-cpl-frame-octets (len (fn-pck-payload (car recs)))))))))

(defun fn-pck-rows (recs) (declare (xargs :guard t :verify-guards nil)) (fn-pck-rows-from recs 0))

(defun fn-pck-enc-root (tree)
  ; The root row: the root tree as metadata, no payload.
  (declare (xargs :guard t :verify-guards nil))
  (list (fn-scc-program tree) 0 0))

; F: the log position at S.  The root row carries, besides the capture's four
; fold roots, the position of the record log at the checkpoint's S (the first
; suffix segment, its lineage genesis, the frontier at S and the txid bound:
; the schema-3 F row's open data), so the open locates the log suffix from the
; same atomic commit that names S.  The model keeps it opaque: FN-PCK-F is
; the value the host recorded at the capture of the first S records of CONFIGS
; and RECS (constrained, any tree the codec encodes: fn-pck-recordsp requires
; the whole root encodable).  That the recorded value is the log's position at
; S is the host's obligation PCK-ROOT-F-LOGPOS, discharged where the host takes
; the capture (the log is rotated at the capture point, so the first suffix
; segment starts at record S).
(encapsulate (((fn-pck-f * *) => *))
  (local (defun fn-pck-f (configs recs) (declare (ignore configs recs)) nil)))

(defun fn-pck-root-tree-of-capture (c f plen)
  ; The four fold roots, F, and PLEN, the committed length of the payload file.
  (declare (xargs :guard t :verify-guards nil))
  (list (fn-sco-cpr c) (fn-sco-identity c) (fn-sco-consumer c) (fn-sco-topic c) f plen))

(defun fn-pck-root-tree (configs recs)
  (declare (xargs :guard t :verify-guards nil))
  (fn-pck-root-tree-of-capture (fn-sco-capture configs recs) (fn-pck-f configs recs)
                               (fn-pck-plen recs 0)))

(defthm fn-pck-root-tree-of-extend
  ; The host's root, taken from the live fold state (the capture extended by
  ; the delta) and the log position recorded at the new S, is the model's root
  ; over the whole history.
  (implies (and (true-listp delta) (equal c (fn-sco-capture configs prefix)))
           (equal (fn-pck-root-tree-of-capture (fn-sco-extend c configs delta)
                                               (fn-pck-f configs (append prefix delta))
                                               (fn-pck-plen (append prefix delta) 0))
                  (fn-pck-root-tree configs (append prefix delta))))
  :hints (("Goal" :in-theory (disable fn-sco-extend fn-sco-capture)
           :use fn-sco-extend-of-capture)))

(defun fn-pck-sccb-listp (recs)
  (declare (xargs :guard t))
  (if (atom recs) (null recs) (and (fn-sccb-treep (car recs)) (fn-pck-sccb-listp (cdr recs)))))

(defun fn-pck-recordsp (configs recs)
  ; Every record and the four fold roots are encodable trees: the premise of
  ; fn-sct-decode-file-of-file-is-the-capture (fn-sct-tables-treep), made
  ; the stronger fn-sccb-treep the catalog's row codec uses.
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-pck-sccb-listp recs) (fn-sccb-treep (fn-pck-root-tree configs recs))))

(defun fn-pck-zero-pages (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons (adt-tp-zeros *pgs-page-words*) (fn-pck-zero-pages (1- n)))))

(defun fn-pck-fit (ps)
  ; Exactly K pages: PS padded with zero pages (or cut, when it does not fit).
  (declare (xargs :guard t :verify-guards nil))
  (if (<= (len ps) *fn-pck-root-pages*)
      (append ps (fn-pck-zero-pages (- *fn-pck-root-pages* (len ps))))
    (adt-tp-take *fn-pck-root-pages* ps)))

(defun fn-pck-root-pages-of-tree (tree)
  (declare (xargs :guard t :verify-guards nil))
  (fn-pck-fit (fn-pck-row-pages-of (list (fn-pck-enc-root tree)))))

(defun fn-pck-root-pages-of (configs recs)
  (declare (xargs :guard t :verify-guards nil))
  (fn-pck-root-pages-of-tree (fn-pck-root-tree configs recs)))

(defun fn-pck-root-fitsp-tree (tree)
  (declare (xargs :guard t :verify-guards nil))
  (<= (len (fn-pck-row-pages-of (list (fn-pck-enc-root tree)))) *fn-pck-root-pages*))

(defun fn-pck-root-fitsp (configs recs)
  ; The host's refusal: a root of more than K pages is not checkpointed.
  (declare (xargs :guard t :verify-guards nil))
  (fn-pck-root-fitsp-tree (fn-pck-root-tree configs recs)))

(defun fn-pck-pages (configs prefix)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-pck-root-pages-of configs prefix)
          (fn-pck-row-pages-of (fn-pck-rows prefix))))

(defun fn-pck-dirty (configs prefix delta)
  (declare (xargs :guard t :verify-guards nil))
  (append (adt-tp-number 0 (fn-pck-root-pages-of configs (append prefix delta)))
          (pck-shift *fn-pck-root-pages*
                     (fn-pck-row-extend-dirty (fn-pck-rows prefix) (fn-pck-rows-from delta (fn-pck-plen prefix 0))))))

(defun fn-pck-dirty-at (cnt tail root-pages delta base)
  ; fn-pck-dirty from the tape's summary (CNT words, TAIL its last partial
  ; page) and the root pages; no prefix list.
  (declare (xargs :guard t :verify-guards nil))
  (append (adt-tp-number 0 root-pages)
          (pck-shift *fn-pck-root-pages*
                     (fn-pck-row-extend-dirty-at cnt tail (fn-pck-rows-from delta base)))))

(defthm fn-pck-dirty-at-is-fn-pck-dirty
  (let ((w (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows prefix))))
    (implies (and (equal cnt (len w))
                  (equal tail (nthcdr (* *pgs-page-words* (floor (len w) *pgs-page-words*)) w))
                  (equal base (fn-pck-plen prefix 0))
                  (equal root-pages (fn-pck-root-pages-of configs (append prefix delta))))
             (equal (fn-pck-dirty-at cnt tail root-pages delta base)
                    (fn-pck-dirty configs prefix delta))))
  :hints (("Goal" :in-theory (e/d (fn-pck-dirty-at fn-pck-dirty)
                                  (fn-pck-row-extend-dirty-at fn-pck-row-extend-dirty
                                   fn-pck-root-pages-of))
           :use ((:instance fn-pck-row-extend-dirty-at-is-extend-dirty
                            (a (fn-pck-rows prefix)) (xs (fn-pck-rows-from delta (fn-pck-plen prefix 0))))))))

(defun fn-pck-delta-page-bound (delta base)
  ; The pages the delta's own words take, and the one page it shares with the tape before it.
  (declare (xargs :guard t :verify-guards nil))
  (+ 1 (fn-pck-row-pool-pages-of-rows (fn-pck-rows-from delta base))))

; --- the rows are a well-formed sequence

(defthm pck-octet-listp-is-octetsp
  (equal (fn-scc-octet-listp x) (adt-octetsp x))
  :hints (("Goal" :in-theory (enable fn-scc-octet-listp fn-scc-octetp adt-octetsp))))

(defthm pck-program-octetsp
  (implies (fn-sccb-treep x) (adt-octetsp (fn-scc-program x)))
  :hints (("Goal" :use fn-sccb-treep-encodes-octets
           :in-theory (disable fn-sccb-treep-encodes-octets))))

(defthm pck-rows-of-append
  (equal (fn-pck-rows (append a b)) (append (fn-pck-rows a) (fn-pck-rows b))))

(defthm pck-rows-ap
  (implies (fn-pck-sccb-listp recs) (fn-pck-row$ap (fn-pck-rows recs)))
  :hints (("Goal" :in-theory (enable fn-pck-row$ap adt-seq-p adt-rec-p adt-val-okp fn-pck-enc-row))))

(defthm pck-len-zero-pages
  (equal (len (fn-pck-zero-pages n)) (nfix n)))

(defthm pck-len-fit
  (equal (len (fn-pck-fit ps)) *fn-pck-root-pages*)
  :hints (("Goal" :in-theory (enable fn-pck-fit))))

(defthm pck-len-root-pages-of
  (equal (len (fn-pck-root-pages-of configs recs)) *fn-pck-root-pages*))

(defthm pck-true-listp-zero-pages
  (true-listp (fn-pck-zero-pages n)))

(defthm pck-true-listp-fit
  (implies (true-listp ps) (true-listp (fn-pck-fit ps)))
  :hints (("Goal" :in-theory (enable fn-pck-fit))))

(in-theory (disable fn-pck-row-pages-of fn-pck-row-of-pages fn-pck-row-extend-dirty
                    fn-pck-row-append-dirty fn-pck-row-pool-pages-of-rows fn-pck-row-pool-pages-of-row
                    fn-pck-fit fn-pck-root-pages-of fn-pck-rows))

(defthm pck-sccb-listp-of-append
  (implies (true-listp a)
           (equal (fn-pck-sccb-listp (append a b))
                  (and (fn-pck-sccb-listp a) (fn-pck-sccb-listp b)))))

(defthm pck-true-listp-pages
  (true-listp (adt-tp-pages w))
  :hints (("Goal" :in-theory (enable adt-tp-pages))))

(defthm pck-true-listp-row-pages-of
  (true-listp (fn-pck-row-pages-of a))
  :hints (("Goal" :in-theory (enable fn-pck-row-pages-of adt-tp-pages-of))))

; -----------------------------------------------------------------------------
; 3. PCK-DELTA

(defthm pck-delta-core
  (implies (and (true-listp r0) (true-listp r1) (true-listp t0)
                (equal (len r0) *fn-pck-root-pages*) (equal (len r1) *fn-pck-root-pages*))
           (equal (pgs-apply-dirty (append r0 t0)
                                   (append (adt-tp-number 0 r1) (pck-shift *fn-pck-root-pages* e)))
                  (append r1 (pgs-apply-dirty t0 e))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable pck-apply-dirty-region pck-apply-dirty-shift pck-apply-dirty-append)
           :use ((:instance pck-apply-dirty-append (c (append r0 t0))
                            (d1 (adt-tp-number 0 r1)) (d2 (pck-shift *fn-pck-root-pages* e)))
                 (:instance pck-apply-dirty-region (a nil) (b r0) (c t0) (ps r1))
                 (:instance pck-apply-dirty-shift (r r1) (c t0) (d e))))))

(defthm fn-pck-dirty-is-the-delta
  (implies (and (true-listp prefix) (true-listp delta)
                (fn-pck-sccb-listp (append prefix delta)))
           (equal (pgs-apply-dirty (fn-pck-pages configs prefix) (fn-pck-dirty configs prefix delta))
                  (fn-pck-pages configs (append prefix delta))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-pages fn-pck-dirty) (pck-delta-core fn-pck-row-pages-of-extend-is-apply-dirty))
           :use ((:instance pck-delta-core
                            (r0 (fn-pck-root-pages-of configs prefix))
                            (r1 (fn-pck-root-pages-of configs (append prefix delta)))
                            (t0 (fn-pck-row-pages-of (fn-pck-rows prefix)))
                            (e (fn-pck-row-extend-dirty (fn-pck-rows prefix) (fn-pck-rows-from delta (fn-pck-plen prefix 0)))))
                 (:instance fn-pck-row-pages-of-extend-is-apply-dirty
                            (a (fn-pck-rows prefix)) (xs (fn-pck-rows-from delta (fn-pck-plen prefix 0))))
                 (:instance pck-rows-ap (recs prefix))
                 (:instance pck-rows-ap (recs delta))))))

; -----------------------------------------------------------------------------
; 4. PCK-BOUND

(defthm fn-pck-dirty-bound
  ; No term in (len prefix): the K root pages and the delta's own.
  (<= (len (fn-pck-dirty configs prefix delta))
      (+ *fn-pck-root-pages* (fn-pck-delta-page-bound delta (fn-pck-plen prefix 0))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-dirty fn-pck-delta-page-bound)
                           (fn-pck-row-extend-dirty-bound))
           :use ((:instance fn-pck-row-extend-dirty-bound
                            (a (fn-pck-rows prefix)) (xs (fn-pck-rows-from delta (fn-pck-plen prefix 0))))))))

; -----------------------------------------------------------------------------
; 5. Reading the image back.

(defun fn-pck-dec-tree (row)
  ; The tree the row's :tree column holds (the root tree, or an event's metadata).
  (declare (xargs :guard t :verify-guards nil))
  (let ((d (fn-scc-decode-tree (car row))))
    (if (and (consp d) (eq (car d) :ok) (consp (cdr d))) (cadr d) nil)))

(defun fn-pck-dec-row (row file)
  ; The event a tape row denotes: its metadata joined with the payload its ref
  ; resolves to in the payload file FILE.
  (declare (xargs :guard t :verify-guards nil))
  (fn-pck-join (fn-pck-dec-tree row)
               (fn-cpl-resolve (fn-cpl-ref (nfix (cadr row)) (nfix (caddr row))) file)))

(defun fn-pck-dec-rows (rows file)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom rows) nil (cons (fn-pck-dec-row (car rows) file) (fn-pck-dec-rows (cdr rows) file))))

(in-theory (disable fn-pck-dec-row fn-pck-dec-tree fn-pck-enc-row))

(defthm pck-dec-row-of-enc-row
  (implies (fn-sccb-treep x) (equal (fn-pck-dec-row (fn-pck-enc-row x)) x))
  :hints (("Goal" :in-theory (enable fn-pck-dec-row fn-pck-enc-row)
           :use ((:instance fn-scc-decode-tree-of-encode)
                 (:instance fn-sccb-treep-is-treep)))))

(defthm pck-dec-rows-of-rows
  (implies (fn-pck-sccb-listp recs) (equal (fn-pck-dec-rows (fn-pck-rows recs)) recs))
  :hints (("Goal" :in-theory (e/d (fn-pck-rows fn-pck-dec-rows fn-pck-sccb-listp)
                                  (fn-pck-dec-row fn-pck-enc-row)))))

(defun fn-pck-capture-of-pages (pages file)
  ; The capture the pages hold: the records from the events tape, the four
  ; fold roots from the root region, the event index rebuilt from the records.
  (declare (xargs :guard t :verify-guards nil))
  (let* ((root (fn-pck-dec-tree (car (fn-pck-row-of-pages (adt-tp-take *fn-pck-root-pages* pages)))))
         (recs (fn-pck-dec-rows (fn-pck-row-of-pages (nthcdr *fn-pck-root-pages* pages)) file)))
    (fn-sco-make recs (nth 0 root) (nth 1 root) (nth 2 root) (nth 3 root)
                 (fn-cei-build-aux recs 0 nil))))

(defun fn-pck-open (disk r mode file configs frontier suffix max-conns)
  (declare (xargs :guard t :verify-guards nil))
  (let ((v (pgs-view (pgs-open disk r mode))))
    (if v
        (fn-ock-recover-extended
         (fn-sco-extend (fn-pck-capture-of-pages (second v) file) configs suffix)
         configs frontier max-conns)
      :fault)))

(defun fn-pck-disk-holds (disk r mode configs prefix)
  (declare (xargs :guard t :verify-guards nil))
  (let ((o (pgs-open disk r mode)))
    (and (equal (car o) :ok)
         (equal (fourth o) (fn-pck-pages configs prefix)))))

; --- the zero padding of the root region reads as nothing

(defthm pck-append-zeros
  (implies (and (natp a) (natp b))
           (equal (append (adt-tp-zeros a) (adt-tp-zeros b)) (adt-tp-zeros (+ a b))))
  :hints (("Goal" :in-theory (enable adt-tp-zeros) :induct (adt-tp-zeros a))))

(defthm pck-flat-zero-pages
  (equal (adt-tp-flat (fn-pck-zero-pages n)) (adt-tp-zeros (* (nfix n) *pgs-page-words*)))
  :hints (("Goal" :in-theory (e/d (adt-tp-flat fn-pck-zero-pages)
                                  ((:executable-counterpart adt-tp-zeros) pck-append-zeros))
           :induct (fn-pck-zero-pages n))
          ("Subgoal *1/2" :use ((:instance pck-append-zeros (a *pgs-page-words*)
                                           (b (* *pgs-page-words* (+ -1 n))))))))

(defthm pck-flat-append
  (equal (adt-tp-flat (append p q)) (append (adt-tp-flat p) (adt-tp-flat q)))
  :hints (("Goal" :in-theory (enable adt-tp-flat))))

(defthm pck-natp-pad
  (natp (adt-tp-pad n))
  :hints (("Goal" :in-theory (enable adt-tp-pad))))

(defthm pck-of-pages-zero-padded
  ; The pages of a sequence followed by zero pages read back as the sequence.
  (implies (and (adt-tp-schema-ok s) (adt-seq-p s a))
           (equal (adt-tp-of-pages s (append (adt-tp-pages-of s a) (fn-pck-zero-pages m))) a))
  :hints (("Goal" :in-theory (e/d (adt-tp-of-pages adt-tp-pages-of)
                                  (adt-tp-seq-roundtrip adt-tp-car-zeros adt-tp-flat-of-pages
                                   pck-append-zeros))
           :use ((:instance adt-tp-flat-of-pages (w (adt-tp-seq-words s a)))
                 (:instance pck-append-zeros (a (adt-tp-pad (len (adt-tp-seq-words s a))))
                            (b (* (nfix m) *pgs-page-words*)))
                 (:instance adt-tp-seq-roundtrip
                            (tail (adt-tp-zeros (+ (adt-tp-pad (len (adt-tp-seq-words s a)))
                                                   (* (nfix m) *pgs-page-words*)))))
                 (:instance adt-tp-car-zeros
                            (n (+ (adt-tp-pad (len (adt-tp-seq-words s a)))
                                  (* (nfix m) *pgs-page-words*))))))))

(defthm pck-of-pages-zero-padded-inst
  (implies (fn-pck-row$ap a)
           (equal (fn-pck-row-of-pages (append (fn-pck-row-pages-of a) (fn-pck-zero-pages m))) a))
  :hints (("Goal" :use ((:instance pck-of-pages-zero-padded (s *fn-pck-row-schema*))
                        fn-pck-row-pages-schema-ok)
           :in-theory (e/d (fn-pck-row-of-pages fn-pck-row-pages-of fn-pck-row$ap)
                           (pck-of-pages-zero-padded)))))

(defthm pck-of-pages-of-inst
  (implies (fn-pck-row$ap a) (equal (fn-pck-row-of-pages (fn-pck-row-pages-of a)) a))
  :hints (("Goal" :use fn-pck-row-of-pages-of-pages-of)))

(defthm pck-take-root
  (implies (true-listp r)
           (equal (adt-tp-take (len r) (append r c)) r))
  :hints (("Goal" :use ((:instance adt-tp-take-of-append (n (len r)) (a r) (b c))
                        (:instance adt-tp-take-all (n (len r)) (w r))))))

(defthm pck-nthcdr-root
  (equal (nthcdr (len r) (append r c)) c))

(defthm pck-ap-enc-row
  (implies (fn-sccb-treep x) (fn-pck-row$ap (list (fn-pck-enc-row x))))
  :hints (("Goal" :use ((:instance pck-rows-ap (recs (list x))))
           :in-theory (e/d (fn-pck-rows fn-pck-sccb-listp) (pck-rows-ap)))))

(in-theory (disable fn-pck-root-tree))

(defthm pck-root-decodes
  (implies (and (fn-pck-recordsp configs recs) (fn-pck-root-fitsp configs recs) (true-listp t0))
           (equal (fn-pck-dec-row (car (fn-pck-row-of-pages
                                        (adt-tp-take *fn-pck-root-pages*
                                                     (append (fn-pck-root-pages-of configs recs) t0)))))
                  (fn-pck-root-tree configs recs)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-root-fitsp fn-pck-recordsp fn-pck-root-pages-of fn-pck-fit)
                           (pck-of-pages-zero-padded-inst pck-take-root fn-pck-row-of-pages
                            fn-pck-row-pages-of))
           :use ((:instance pck-take-root (r (fn-pck-root-pages-of configs recs)) (c t0))
                 (:instance pck-of-pages-zero-padded-inst
                            (a (list (fn-pck-enc-root (fn-pck-root-tree configs recs))))
                            (m (- *fn-pck-root-pages*
                                  (len (fn-pck-row-pages-of
                                        (list (fn-pck-enc-root (fn-pck-root-tree configs recs))))))))
                 (:instance pck-ap-enc-row (x (fn-pck-root-tree configs recs)))
                 (:instance pck-dec-row-of-enc-row (x (fn-pck-root-tree configs recs)))))))

(defthm pck-capture-of-pages
  (implies (and (true-listp recs) (fn-pck-recordsp configs recs) (fn-pck-root-fitsp configs recs))
           (equal (fn-pck-capture-of-pages (fn-pck-pages configs recs))
                  (fn-sco-capture configs recs)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-capture-of-pages fn-pck-pages fn-pck-root-tree fn-sco-capture)
                           (pck-root-decodes pck-of-pages-of-inst pck-nthcdr-root
                            fn-pck-root-pages-of fn-pck-row-of-pages fn-pck-row-pages-of
                            fn-pck-rows fn-pck-dec-rows))
           :use ((:instance pck-root-decodes (t0 (fn-pck-row-pages-of (fn-pck-rows recs))))
                 (:instance pck-nthcdr-root (r (fn-pck-root-pages-of configs recs))
                            (c (fn-pck-row-pages-of (fn-pck-rows recs))))
                 (:instance pck-of-pages-of-inst (a (fn-pck-rows recs)))
                 (:instance pck-rows-ap (recs recs))
                 (:instance pck-dec-rows-of-rows)
                 (:instance pck-len-root-pages-of (recs recs))))))

(defun fn-pck-f-of-pages (pages)
  ; The log position the root region holds (the root row's fifth field).
  (declare (xargs :guard t :verify-guards nil))
  (let ((root (fn-pck-dec-tree (car (fn-pck-row-of-pages (adt-tp-take *fn-pck-root-pages* pages))))))
    (if (true-listp root) (nth 4 root) nil)))

(defthm pck-f-of-pages
  ; The pages of RECS hold the log position recorded at S = (len RECS).
  (implies (and (true-listp recs) (fn-pck-recordsp configs recs) (fn-pck-root-fitsp configs recs))
           (equal (fn-pck-f-of-pages (fn-pck-pages configs recs))
                  (fn-pck-f configs recs)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-f-of-pages fn-pck-pages fn-pck-root-tree fn-sco-capture)
                           (pck-root-decodes pck-of-pages-of-inst pck-nthcdr-root
                            fn-pck-root-pages-of fn-pck-row-of-pages fn-pck-row-pages-of
                            fn-pck-rows fn-pck-dec-rows))
           :use ((:instance pck-root-decodes (t0 (fn-pck-row-pages-of (fn-pck-rows recs))))))))

; -----------------------------------------------------------------------------
; 6. PCK-OPEN

(defun pck-ind-k (k x)
  (if (zp k) x (pck-ind-k (1- k) (- x *pgs-page-words*))))

(defthm pck-k-le-npages
  (implies (and (natp k) (natp x) (<= (* *pgs-page-words* k) x))
           (<= k (adt-tp-npages x)))
  :hints (("Goal" :induct (pck-ind-k k x))
          ("Subgoal *1/2" :use ((:instance adt-tp-npages-open (n x))))))

(defthm pck-floor-le-npages
  (implies (natp x) (<= (floor x *pgs-page-words*) (adt-tp-npages x)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance adt-tp-floor-bounds)
                        (:instance pck-k-le-npages (k (floor x *pgs-page-words*))))
           :in-theory (disable adt-tp-floor-bounds pck-k-le-npages))))

(defthm pck-lp-shift-number
  (implies (and (natp k) (natp k0) (natp l) (<= k0 l))
           (pgs-lpages-ok (pgs-dirty-lpages (pck-shift k (adt-tp-number k0 ps))) (+ k l) k))
  :hints (("Goal" :do-not-induct t :in-theory (disable pck-lpages-ok-number)
           :use ((:instance pck-lpages-ok-number (k (+ k k0)) (lo k) (n (+ k l)))))))

(defthm pck-floor-le-len-pages
  (<= (floor (len w) *pgs-page-words*) (len (adt-tp-pages w)))
  :hints (("Goal" :use ((:instance pck-floor-le-npages (x (len w)))
                        (:instance adt-tp-len-pages))
           :in-theory (disable pck-floor-le-npages adt-tp-len-pages adt-tp-pages-long))))

(defthm pck-lpages-ok-shifted-dirty
  ; The tape's dirty pages, behind K pages in front, are numbered in order and
  ; each at most the length reached.
  (implies (and (true-listp w) (natp k))
           (pgs-lpages-ok (pgs-dirty-lpages (pck-shift k (adt-tp-dirty w n)))
                          (+ k (len (adt-tp-pages w))) k))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (adt-tp-dirty) (pck-lp-shift-number pck-floor-le-len-pages adt-tp-pages-long))
           :use ((:instance pck-lp-shift-number
                            (k0 (floor (len w) *pgs-page-words*)) (l (len (adt-tp-pages w)))
                            (ps (adt-tp-pages (append (nthcdr (* *pgs-page-words* (floor (len w) *pgs-page-words*)) w) n))))
                 (:instance pck-floor-le-len-pages)
                 (:instance adt-tp-floor-bounds (x (len w)))))))

(defthm pck-dirty-lpages-ok
  (pgs-lpages-ok (pgs-dirty-lpages (fn-pck-dirty configs prefix delta))
                 (len (fn-pck-pages configs prefix)) 0)
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-dirty fn-pck-pages fn-pck-row-pages-of fn-pck-row-extend-dirty
                            adt-tp-pages-of adt-tp-extend-dirty)
                           (pck-lpages-ok-shifted-dirty pck-lpages-ok-number-then adt-tp-pages-long
                            fn-pck-root-pages-of fn-pck-rows adt-tp-dirty pck-shift))
           :use ((:instance pck-lpages-ok-shifted-dirty (k *fn-pck-root-pages*)
                            (w (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows prefix)))
                            (n (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from delta (fn-pck-plen prefix 0)))))
                 (:instance pck-lpages-ok-number-then (lo 0)
                            (n (len (fn-pck-pages configs prefix)))
                            (ps (fn-pck-root-pages-of configs (append prefix delta)))
                            (l2 (pgs-dirty-lpages
                                 (pck-shift *fn-pck-root-pages*
                                            (adt-tp-dirty (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows prefix))
                                                          (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows-from delta (fn-pck-plen prefix 0))))))))
                 (:instance pck-len-root-pages-of (recs (append prefix delta)))))))

(defthm pck-disk-holds-facts
  (implies (fn-pck-disk-holds disk r mode configs prefix)
           (and (equal (car (pgs-open disk r mode)) :ok)
                (equal (fourth (pgs-open disk r mode)) (fn-pck-pages configs prefix))))
  :hints (("Goal" :in-theory (e/d (fn-pck-disk-holds) (pgs-open fn-pck-pages)))))

(defthm pck-open-view-after-commit
  (implies (and (true-listp prefix) (true-listp delta)
                (fn-pck-sccb-listp (append prefix delta))
                (fn-pck-disk-holds disk r mode configs prefix)
                (pgs-alloc-inv alloc disk))
           (equal (pgs-view (pgs-open (pgs-commit disk r mode (fn-pck-dirty configs prefix delta) alloc) r mode))
                  (list (pgs-next-txid (pgs-root-slots r disk))
                        (fn-pck-pages configs (append prefix delta)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory) '(pck-disk-holds-facts))
           :use ((:instance pgs-open-after-commit (dirty (fn-pck-dirty configs prefix delta)))
                 (:instance fn-pck-dirty-is-the-delta)
                 (:instance pck-disk-holds-facts)
                 (:instance pck-dirty-lpages-ok)))))

(defthm pck-recordsp-sccb
  (implies (fn-pck-recordsp configs recs) (fn-pck-sccb-listp recs))
  :hints (("Goal" :in-theory (enable fn-pck-recordsp))))

(defthm pck-true-listp-append
  (implies (and (true-listp a) (true-listp b)) (true-listp (append a b)))
  :rule-classes nil)

; PCK-OPEN
(defthm fn-pck-open-after-commit-is-full-recover
  (implies (and (true-listp prefix) (true-listp delta) (true-listp suffix)
                (fn-pck-recordsp configs (append prefix delta))
                (fn-pck-root-fitsp configs (append prefix delta))
                (fn-pck-disk-holds disk r mode configs prefix)
                (pgs-alloc-inv alloc disk))
           (equal (fn-pck-open (pgs-commit disk r mode (fn-pck-dirty configs prefix delta) alloc)
                               r mode configs frontier suffix max-conns)
                  (fn-ock-recover-full configs frontier (append prefix delta suffix) max-conns)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-pck-open (:executable-counterpart consp) associativity-of-append
                                        (:rewrite car-cons) (:rewrite cdr-cons)))
           :use ((:instance pck-open-view-after-commit)
                 (:instance pck-capture-of-pages (recs (append prefix delta)))
                 (:instance fn-owner-recover-from-checkpoint-equals-full-recover
                            (prefix (append prefix delta)))
                 (:instance pck-sccb-listp-of-append (a prefix) (b delta))
                 (:instance pck-recordsp-sccb (recs (append prefix delta)))
                 (:instance pck-true-listp-append (a prefix) (b delta))))))

; -----------------------------------------------------------------------------
; 7. PCK-CRASH
;
; The log is (START . TAIL): the records from index START on; segments
; wholly below START have been compacted away.  The open reads the checkpoint
; (the capture of S records) from the pages, and replays the log tail from S.

(defun fn-pck-log-retains (log n)
  ; The log still holds every record from index N on.
  (declare (xargs :guard (natp n)))
  (and (consp log) (natp (car log)) (<= (car log) n)))

(defun fn-pck-recover-view (v file log configs frontier max-conns)
  ; V is the view of the opened image: (TXID CONTENTS), or nil when the open refused.
  (declare (xargs :guard t :verify-guards nil))
  (if (and v (consp log))
      (let ((c (fn-pck-capture-of-pages (cadr v) file)))
        ; A log that starts past the checkpoint's S has lost records the replay
        ; needs: refuse, never replay a wrong suffix.
        (if (fn-pck-log-retains log (len (fn-sco-records c)))
            (fn-ock-recover-extended
             (fn-sco-extend c configs (nthcdr (- (len (fn-sco-records c)) (nfix (car log))) (cdr log)))
             configs frontier max-conns)
          :fault))
    :fault))

(defun fn-pck-recover (image r mode file log configs frontier max-conns)
  (declare (xargs :guard t :verify-guards nil))
  (fn-pck-recover-view (pgs-view (pgs-open image r mode)) file log configs frontier max-conns))

(defthm pck-nthcdr-nthcdr
  (implies (and (natp a) (natp b))
           (equal (nthcdr a (nthcdr b x)) (nthcdr (+ a b) x))))

(defthm pck-records-of-capture
  (implies (true-listp recs)
           (equal (fn-sco-records (fn-sco-capture configs recs)) recs))
  :hints (("Goal" :in-theory (e/d (fn-sco-records fn-sco-capture fn-sco-make fn-sco-at)
                                  (fn-sco-cpr-prefix fn-replay-identity-loop
                                   fn-cpe-projection-replay fn-th-prefix-loop fn-cei-build-aux)))))

(defthm pck-log-tail
  (implies (and (true-listp recs) (natp s) (<= s (len recs)))
           (equal (nthcdr (- (len recs) s) (nthcdr s (append recs rest))) rest))
  :hints (("Goal" :use ((:instance pck-nthcdr-nthcdr (a (- (len recs) s)) (b s) (x (append recs rest))))
           :in-theory (disable pck-nthcdr-nthcdr))))

(defthm pck-recover-of-view
  ; Recovery from a view of the pages of RECS: the log tail from the
  ; checkpoint's S on is REST.
  (implies (and (true-listp recs)
                (fn-pck-recordsp configs recs) (fn-pck-root-fitsp configs recs)
                (fn-pck-log-retains log (len recs))
                (equal (nthcdr (car log) (append recs rest)) (cdr log))
                (equal v (list tx (fn-pck-pages configs recs))))
           (equal (fn-pck-recover-view v log configs frontier max-conns)
                  (fn-ock-recover-extended (fn-sco-extend (fn-sco-capture configs recs) configs rest)
                                           configs frontier max-conns)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-pck-recover-view fn-pck-log-retains nfix natp (:executable-counterpart consp)
                                        (:rewrite car-cons) (:rewrite cdr-cons)))
           :use ((:instance pck-capture-of-pages)
                 (:instance pck-records-of-capture)
                 (:instance pck-log-tail (s (car log)))))))

(defthm pck-open-true-listp
  (implies (equal (car (pgs-open disk r mode)) :ok)
           (true-listp (pgs-open disk r mode)))
  :hints (("Goal" :use ((:instance pgs-open-slots-ok (slots (pgs-root-slots r disk))
                                   (pages (pgs-pages disk))))
           :in-theory (enable pgs-open))))

(defthm pck-view-of-old
  (implies (fn-pck-disk-holds disk r mode configs prefix)
           (equal (pgs-view (pgs-open disk r mode))
                  (list (third (pgs-open disk r mode)) (fn-pck-pages configs prefix))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(pck-disk-holds-facts pck-open-true-listp pgs-view-of-ok))
           :use ((:instance pck-disk-holds-facts) (:instance pck-open-true-listp)
                 (:instance pgs-view-of-ok (o (pgs-open disk r mode)))))))

(defthm pck-crash-cases
  ; The view is that of the new image or of the old one: either way, the
  ; recovery over the log tail is the full recovery.
  (implies (and (true-listp prefix) (true-listp delta) (true-listp suffix)
                (fn-pck-recordsp configs (append prefix delta))
                (fn-pck-recordsp configs prefix)
                (fn-pck-root-fitsp configs (append prefix delta))
                (fn-pck-root-fitsp configs prefix)
                (fn-pck-log-retains log (len prefix))
                (equal (nthcdr (car log) (append prefix delta suffix)) (cdr log))
                (member-equal v (list (list t1 (fn-pck-pages configs (append prefix delta)))
                                      (list t0 (fn-pck-pages configs prefix)))))
           (equal (fn-pck-recover-view v log configs frontier max-conns)
                  (fn-ock-recover-full configs frontier (append prefix delta suffix) max-conns)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (member-equal fn-pck-log-retains)
                           (pck-recover-of-view fn-owner-recover-from-checkpoint-equals-full-recover
                            fn-pck-recover-view fn-pck-recordsp fn-pck-root-fitsp fn-sco-capture
                            fn-sco-extend fn-ock-recover-extended fn-ock-recover-full))
           :cases ((equal v (list t1 (fn-pck-pages configs (append prefix delta)))))
           :use ((:instance pck-recover-of-view (recs (append prefix delta)) (rest suffix) (tx t1))
                 (:instance pck-recover-of-view (recs prefix) (rest (append delta suffix)) (tx t0))
                 (:instance fn-owner-recover-from-checkpoint-equals-full-recover
                            (prefix (append prefix delta)))
                 (:instance fn-owner-recover-from-checkpoint-equals-full-recover
                            (suffix (append delta suffix)))
                 (:instance pck-true-listp-append (a prefix) (b delta))
                 (:instance len-of-append (x prefix) (y delta))))))

; PCK-CRASH
(defthm fn-pck-crash-recovers-from-old-or-new
  (let ((p (pgs-plan-commit disk r mode (fn-pck-dirty configs prefix delta) alloc)))
    (implies (and (true-listp prefix) (true-listp delta) (true-listp suffix)
                  (fn-pck-recordsp configs (append prefix delta))
                  (fn-pck-recordsp configs prefix)
                  (fn-pck-root-fitsp configs (append prefix delta))
                  (fn-pck-root-fitsp configs prefix)
                  (fn-pck-disk-holds disk r mode configs prefix)
                  (pgs-alloc-inv alloc disk)
                  (pgs-writes-faithful (second p) (pgs-pages disk))
                  (or (equal sv (pgs-slot (third p) (pgs-root-slots r disk)))
                      (equal sv (fourth p))
                      (not (pgs-rec-valid sv)))
                  (fn-pck-log-retains log (len prefix))
                  (equal (nthcdr (car log) (append prefix delta suffix)) (cdr log)))
             (equal (fn-pck-recover (pgs-crash disk r (second p) keep (third p) sv)
                                    r mode log configs frontier max-conns)
                    (fn-ock-recover-full configs frontier (append prefix delta suffix) max-conns))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-pck-recover pck-open-view-after-commit pck-view-of-old
                                        pck-recordsp-sccb pck-sccb-listp-of-append
                                        (:executable-counterpart consp)))
           :use ((:instance pgs-open-after-crash (dirty (fn-pck-dirty configs prefix delta)))
                 (:instance pck-disk-holds-facts)
                 (:instance pck-dirty-lpages-ok)
                 (:instance pck-open-view-after-commit)
                 (:instance pck-view-of-old)
                 (:instance pck-crash-cases
                            (v (pgs-view (pgs-open (pgs-crash disk r
                                                              (second (pgs-plan-commit disk r mode (fn-pck-dirty configs prefix delta) alloc))
                                                              keep
                                                              (third (pgs-plan-commit disk r mode (fn-pck-dirty configs prefix delta) alloc))
                                                              sv)
                                                   r mode)))
                            (t1 (pgs-next-txid (pgs-root-slots r disk)))
                            (t0 (third (pgs-open disk r mode))))))))
