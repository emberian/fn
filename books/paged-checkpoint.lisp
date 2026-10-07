(in-package "ACL2")
(include-book "def-representation-pages")
(include-book "pagestore")
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
(def-representation fn-pck-row (prog :tree) :pages t)

(defconst *fn-pck-root-pages* 8)

(defun fn-pck-enc-row (x)
  (declare (xargs :guard t :verify-guards nil))
  (list (fn-scc-program x)))

(defun fn-pck-rows (recs)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom recs) nil (cons (fn-pck-enc-row (car recs)) (fn-pck-rows (cdr recs)))))

(defun fn-pck-root-tree (configs recs)
  (declare (xargs :guard t :verify-guards nil))
  (let ((c (fn-sco-capture configs recs)))
    (list (fn-sco-cpr c) (fn-sco-identity c) (fn-sco-consumer c) (fn-sco-topic c))))

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
  (adt-tp-take *fn-pck-root-pages* (append ps (fn-pck-zero-pages *fn-pck-root-pages*))))

(defun fn-pck-root-pages-of (configs recs)
  (declare (xargs :guard t :verify-guards nil))
  (fn-pck-fit (fn-pck-row-pages-of (list (fn-pck-enc-row (fn-pck-root-tree configs recs))))))

(defun fn-pck-root-fitsp (configs recs)
  ; The host's refusal: a root of more than K pages is not checkpointed.
  (declare (xargs :guard t :verify-guards nil))
  (<= (len (fn-pck-row-pages-of (list (fn-pck-enc-row (fn-pck-root-tree configs recs)))))
      *fn-pck-root-pages*))

(defun fn-pck-pages (configs prefix)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-pck-root-pages-of configs prefix)
          (fn-pck-row-pages-of (fn-pck-rows prefix))))

(defun fn-pck-dirty (configs prefix delta)
  (declare (xargs :guard t :verify-guards nil))
  (append (adt-tp-number 0 (fn-pck-root-pages-of configs (append prefix delta)))
          (pck-shift *fn-pck-root-pages*
                     (fn-pck-row-extend-dirty (fn-pck-rows prefix) (fn-pck-rows delta)))))

(defun fn-pck-delta-page-bound (delta)
  ; The pages the delta's own words take, and the one page it shares with the tape before it.
  (declare (xargs :guard t :verify-guards nil))
  (+ 1 (fn-pck-row-pool-pages-of-rows (fn-pck-rows delta))))

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

(defthm pck-len-fit
  (equal (len (fn-pck-fit ps)) *fn-pck-root-pages*)
  :hints (("Goal" :in-theory (enable fn-pck-fit))))

(defthm pck-len-root-pages-of
  (equal (len (fn-pck-root-pages-of configs recs)) *fn-pck-root-pages*))

(defthm pck-true-listp-fit
  (true-listp (fn-pck-fit ps))
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
                            (e (fn-pck-row-extend-dirty (fn-pck-rows prefix) (fn-pck-rows delta))))
                 (:instance fn-pck-row-pages-of-extend-is-apply-dirty
                            (a (fn-pck-rows prefix)) (xs (fn-pck-rows delta)))
                 (:instance pck-rows-ap (recs prefix))
                 (:instance pck-rows-ap (recs delta))))))

; -----------------------------------------------------------------------------
; 4. PCK-BOUND

(defthm fn-pck-dirty-bound
  ; No term in (len prefix): the K root pages and the delta's own.
  (<= (len (fn-pck-dirty configs prefix delta))
      (+ *fn-pck-root-pages* (fn-pck-delta-page-bound delta)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-dirty fn-pck-delta-page-bound)
                           (fn-pck-row-extend-dirty-bound))
           :use ((:instance fn-pck-row-extend-dirty-bound
                            (a (fn-pck-rows prefix)) (xs (fn-pck-rows delta)))))))
