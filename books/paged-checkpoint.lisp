(in-package "ACL2")
(include-book "def-representation-pages")
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
  (if (<= (len ps) *fn-pck-root-pages*)
      (append ps (fn-pck-zero-pages (- *fn-pck-root-pages* (len ps))))
    (adt-tp-take *fn-pck-root-pages* ps)))

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

; -----------------------------------------------------------------------------
; 5. Reading the image back.

(defun fn-pck-dec-row (row)
  (declare (xargs :guard t :verify-guards nil))
  (let ((d (fn-scc-decode-tree (car row))))
    (if (and (consp d) (eq (car d) :ok) (consp (cdr d))) (cadr d) nil)))

(defun fn-pck-dec-rows (rows)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom rows) nil (cons (fn-pck-dec-row (car rows)) (fn-pck-dec-rows (cdr rows)))))

(in-theory (disable fn-pck-dec-row fn-pck-enc-row))

(defthm pck-dec-row-of-enc-row
  (implies (fn-sccb-treep x) (equal (fn-pck-dec-row (fn-pck-enc-row x)) x))
  :hints (("Goal" :in-theory (enable fn-pck-dec-row fn-pck-enc-row)
           :use ((:instance fn-scc-decode-tree-of-encode)
                 (:instance fn-sccb-treep-is-treep)))))

(defthm pck-dec-rows-of-rows
  (implies (fn-pck-sccb-listp recs) (equal (fn-pck-dec-rows (fn-pck-rows recs)) recs))
  :hints (("Goal" :in-theory (e/d (fn-pck-rows fn-pck-dec-rows fn-pck-sccb-listp)
                                  (fn-pck-dec-row fn-pck-enc-row)))))

(defun fn-pck-capture-of-pages (pages)
  ; The capture the pages hold: the records from the events tape, the four
  ; fold roots from the root region, the event index rebuilt from the records.
  (declare (xargs :guard t :verify-guards nil))
  (let* ((root (fn-pck-dec-row (car (fn-pck-row-of-pages (adt-tp-take *fn-pck-root-pages* pages)))))
         (recs (fn-pck-dec-rows (fn-pck-row-of-pages (nthcdr *fn-pck-root-pages* pages)))))
    (fn-sco-make recs (nth 0 root) (nth 1 root) (nth 2 root) (nth 3 root)
                 (fn-cei-build-aux recs 0 nil))))

(defun fn-pck-open (disk r mode configs frontier suffix max-conns)
  (declare (xargs :guard t :verify-guards nil))
  (let ((v (pgs-view (pgs-open disk r mode))))
    (if v
        (fn-ock-recover-extended
         (fn-sco-extend (fn-pck-capture-of-pages (second v)) configs suffix)
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
                            (a (list (fn-pck-enc-row (fn-pck-root-tree configs recs))))
                            (m (- *fn-pck-root-pages*
                                  (len (fn-pck-row-pages-of
                                        (list (fn-pck-enc-row (fn-pck-root-tree configs recs))))))))
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
                            (n (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows delta))))
                 (:instance pck-lpages-ok-number-then (lo 0)
                            (n (len (fn-pck-pages configs prefix)))
                            (ps (fn-pck-root-pages-of configs (append prefix delta)))
                            (l2 (pgs-dirty-lpages
                                 (pck-shift *fn-pck-root-pages*
                                            (adt-tp-dirty (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows prefix))
                                                          (adt-tp-seq-words *fn-pck-row-schema* (fn-pck-rows delta)))))))
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
