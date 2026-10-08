; A buffered placement row refines an append to the five final regions.
(in-package "ACL2")
(include-book "history-image-content-placement")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-his-put-apart-from-pending (j ys rcs starts)
 (declare (xargs :guard (natp j)))
 (if (or (atom rcs) (atom ys)) t
  (and (consp starts) (fn-his-rcp (car rcs)) (natp (car starts))
       (or (equal (cadr (car rcs)) 0)
           (<= (+ j (len ys)) (* 2048 (+ (car starts) (car (car rcs)))))
           (<= (+ (* 2048 (+ (car starts) (car (car rcs)))) (cadr (car rcs))) j))
       (fn-his-put-apart-from-pending j ys (cdr rcs) (cdr starts)))))

(defthm fn-his-flush-commutes-with-disjoint-put
 (implies (and (natp j) (fn-his-put-apart-from-pending j ys rcs starts))
  (equal (fn-his-rcs-flush-write rcs starts (fn-hp-x-put j ys pgs-mem))
         (fn-hp-x-put j ys (fn-his-rcs-flush-write rcs starts pgs-mem))))
 :hints (("Goal" :induct (fn-his-rcs-flush-write rcs starts pgs-mem)
          :in-theory (e/d (fn-his-rcs-flush-write)
                          (fn-his-rcp fn-hp-x-put fn-his-flush-consp fn-his-flush-cons)))
         ("Subgoal *1/2"
          :use ((:instance fn-his-put-commutes
                  (a j) (xs ys) (b (* 2048 (+ (car starts) (car (car rcs)))))
                  (ys (reverse (caddr (car rcs))))))))
 :rule-classes nil)

(local (defthm fn-his-pending-len-zero-atom
 (implies (equal (len x) 0) (atom x))
 :hints (("Goal" :expand ((len x))))))

(local (defthm fn-his-pending-consp-length
 (implies (consp x) (< 0 (len x))) :rule-classes :linear))

(defthm fn-his-put-apart-from-placed-pending
 (implies
  (and (natp s) (natp cap) (natp j)
       (<= (* 2048 s) j) (<= (+ j (len ys)) (* 2048 (+ s cap)))
       (fn-his-cellsp cells) (fn-his-cursors-at rcs lens) (nat-listp starts)
       (equal (len cells) (len lens)) (equal (len starts) (len lens))
       (adt-apart s cap starts (fn-hp-x-add lens (fn-his-cell-bytes cells))))
  (fn-his-put-apart-from-pending j ys rcs starts))
 :hints (("Goal" :induct (fn-his-region-ind cells rcs lens starts)
          :in-theory (e/d (fn-his-cursors-at fn-hp-x-add fn-his-cell-bytes adt-apart len)
                          (fn-his-rcp adt-cap)))
         ("Subgoal *1/2"
          :use ((:instance fn-his-rc-merged-within-cap (rc (car rcs)) (start (car starts))
                           (used (car lens)) (ws (car cells)))))))

(defthm fn-his-flush-splits-merged-head
 (implies
  (and (fn-his-rcp rc) (natp start)
       (fn-his-put-apart-from-pending (+ (* 2048 (+ start (car rc))) (cadr rc)) ws rcs starts))
  (equal
   (fn-his-rcs-flush-write rcs starts
    (fn-hp-x-put (* 2048 (+ start (car rc))) (append (reverse (caddr rc)) ws) pgs-mem))
   (fn-hp-x-put (+ (* 2048 (+ start (car rc))) (cadr rc)) ws
    (fn-his-rcs-flush-write (cons rc rcs) (cons start starts) pgs-mem))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-his-flush-commutes-with-disjoint-put
                  (j (+ (* 2048 (+ start (car rc))) (cadr rc))) (ys ws)
                  (pgs-mem (fn-hp-x-put (* 2048 (+ start (car rc))) (reverse (caddr rc)) pgs-mem))))
          :in-theory (disable fn-his-rcp fn-hp-x-put fn-his-rcs-flush-write
                              fn-his-put-apart-from-pending reverse len))))

(defthm fn-his-rcs-fit-implies-flush-fit
 (implies (fn-his-rcs-fitp cells rcs starts nw nd)
          (fn-his-rcs-flush-fitp rcs starts nw nd))
 :hints (("Goal" :induct (fn-his-rcs-fitp cells rcs starts nw nd)
          :in-theory (e/d (fn-his-rc-fitp) (fn-his-rcp)))))

(defthm fn-his-cell-write-ready
 (implies (fn-his-rc-fitp (len ws) rc start nw nd)
  (let ((j (+ (* 2048 (+ start (car rc))) (cadr rc))))
   (and (natp j) (<= (+ j (len ws)) nw)
        (or (atom ws) (< (floor (+ j (len ws) -1) 2048) nd)))))
 :hints (("Goal" :use ((:instance fn-his-word-end-implies-dirty-bound
                                (j (+ (* 2048 (+ start (car rc))) (cadr rc))) (n (len ws))))
          :in-theory (e/d (fn-his-rc-fitp fn-his-rcp) (floor len)))))

(local
 (defun-nx fn-his-merged-split-ind (cells rcs lens starts mem)
  (declare (xargs :guard (and (fn-his-cursors-apart cells rcs starts) (true-listp lens))
                  :verify-guards t
                  :guard-hints (("Goal" :in-theory (disable fn-his-put-apart-from-cursors)))))
  (if (atom cells) mem
   (fn-his-merged-split-ind (cdr cells) (cdr rcs) (cdr lens) (cdr starts)
    (ec-call (fn-hp-x-put (* 2048 (+ (car starts) (car (car rcs))))
                          (append (reverse (caddr (car rcs))) (car cells)) mem))))))

(defthm fn-his-put-blocks-cons-ready
 (implies (and (natp j) (fn-hp-u64-listp ws)
               (<= (+ j (len ws)) (pgs-w-length pgs-mem))
               (or (atom ws) (< (floor (+ j (len ws) -1) 2048) (pgs-d-length pgs-mem))))
  (equal (fn-hp-x-put-blocks (cons (cons j ws) blocks) pgs-mem)
         (fn-hp-x-put-blocks blocks (fn-hp-x-put j ws pgs-mem))))
 :hints (("Goal" :expand ((fn-hp-x-put-blocks (cons (cons j ws) blocks) pgs-mem))
          :in-theory (e/d (fn-hp-x-put-blocks) (fn-hp-x-put floor fn-hp-u64-listp)))))

(defthm fn-his-cursor-offset
 (implies (and (fn-his-rcp rc) (natp start)
               (equal used (* 8 (+ (* 2048 (car rc)) (cadr rc)))))
  (equal (+ (* 2048 (nfix start)) (floor (nfix used) 8))
         (+ (* 2048 (+ start (car rc))) (cadr rc))))
 :hints (("Goal" :in-theory (e/d (fn-his-rcp) (len)))))

(defthm fn-his-head-cell-apart-pending
 (implies
  (and (consp cells) (fn-his-cellsp cells) (fn-his-cursors-at rcs lens)
       (nat-listp starts) (natp np)
       (equal (len cells) (len lens)) (equal (len starts) (len lens))
       (adt-placement-ok starts (fn-hp-x-add lens (fn-his-cell-bytes cells)) np))
  (fn-his-put-apart-from-pending
   (+ (* 2048 (+ (car starts) (car (car rcs)))) (cadr (car rcs)))
   (car cells) (cdr rcs) (cdr starts)))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-his-put-apart-from-placed-pending
                  (s (car starts)) (cap (adt-cap (+ (car lens) (* 8 (len (car cells))))))
                  (j (+ (* 2048 (+ (car starts) (car (car rcs)))) (cadr (car rcs))))
                  (ys (car cells)) (cells (cdr cells)) (rcs (cdr rcs)) (lens (cdr lens)) (starts (cdr starts)))
                (:instance fn-his-rc-merged-within-cap (ws (car cells)) (rc (car rcs))
                  (start (car starts)) (used (car lens))))
          :expand ((fn-his-cursors-at rcs lens)
                   (adt-placement-ok starts (fn-hp-x-add lens (fn-his-cell-bytes cells)) np))
          :in-theory (e/d (fn-hp-x-add fn-his-cell-bytes len)
                          (fn-his-rcp adt-apart adt-cap fn-his-put-apart-from-pending)))))

(defthm fn-his-bb-head-after-flush
 (implies
  (and (consp cells) (fn-his-cellsp cells) (fn-his-cursors-at rcs lens)
       (nat-listp starts) (natp np)
       (equal (len cells) (len lens)) (equal (len starts) (len lens))
       (adt-placement-ok starts (fn-hp-x-add lens (fn-his-cell-bytes cells)) np)
       (fn-his-rcs-fitp cells rcs starts (pgs-w-length pgs-mem) (pgs-d-length pgs-mem)))
  (equal
   (fn-hp-x-put-blocks (fn-hp-bb-list starts lens cells) (fn-his-rcs-flush-write rcs starts pgs-mem))
   (fn-hp-x-put-blocks (fn-hp-bb-list (cdr starts) (cdr lens) (cdr cells))
    (fn-his-rcs-flush-write (cdr rcs) (cdr starts)
     (fn-hp-x-put (* 2048 (+ (car starts) (car (car rcs))))
                  (append (reverse (caddr (car rcs))) (car cells)) pgs-mem)))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-his-rcs-fit-implies-flush-fit
                           (nw (pgs-w-length pgs-mem)) (nd (pgs-d-length pgs-mem)))
                (:instance fn-his-rcs-flush-write-keeps-lengths)
                (:instance fn-his-head-cell-apart-pending)
                (:instance fn-his-cell-write-ready (ws (car cells)) (rc (car rcs)) (start (car starts))
                  (nw (pgs-w-length pgs-mem)) (nd (pgs-d-length pgs-mem)))
                (:instance fn-his-cursor-offset (rc (car rcs)) (start (car starts)) (used (car lens)))
                (:instance fn-his-flush-splits-merged-head (ws (car cells)) (rc (car rcs))
                  (start (car starts)) (rcs (cdr rcs)) (starts (cdr starts))))
          :expand ((fn-his-cursors-at rcs lens) (fn-his-rcs-fitp cells rcs starts (pgs-w-length pgs-mem) (pgs-d-length pgs-mem))
                   (fn-hp-bb-list starts lens cells))
          :in-theory (disable fn-his-rcp fn-his-rc-fitp fn-hp-x-put fn-his-rcs-flush-write
                              fn-hp-x-put-blocks fn-his-put-append reverse floor adt-cap adt-apart
                              fn-his-put-apart-from-pending fn-hp-bb-list fn-his-cursors-at fn-his-rcs-fitp
                              fn-hp-u64-listp adt-placement-ok fn-hp-x-add fn-his-cell-bytes
                              fn-his-flush-consp fn-his-flush-cons fn-his-cursor-offset
                              fn-his-cell-write-ready fn-his-head-cell-apart-pending
                              fn-his-flush-splits-merged-head fn-his-rcs-fit-implies-flush-fit
                              fn-his-rcs-flush-fitp fn-his-rcs-flush-write-keeps-lengths)))
  :rule-classes nil)

(defthm fn-his-merged-head-write
 (implies
  (and (consp cells) (fn-his-cellsp cells)
       (fn-his-rcs-fitp cells rcs starts (pgs-w-length pgs-mem) (pgs-d-length pgs-mem)))
  (equal (fn-hp-x-put-blocks (fn-his-merged-blocks cells rcs starts) pgs-mem)
         (fn-hp-x-put-blocks (fn-his-merged-blocks (cdr cells) (cdr rcs) (cdr starts))
          (fn-hp-x-put (* 2048 (+ (car starts) (car (car rcs))))
                       (append (reverse (caddr (car rcs))) (car cells)) pgs-mem))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-his-merged-write-ready (ws (car cells)) (rc (car rcs)) (start (car starts))))
          :expand ((fn-his-merged-blocks cells rcs starts))
          :in-theory (e/d (fn-his-rc-fitp)
                          (fn-his-rcp fn-hp-x-put fn-hp-x-put-blocks fn-his-merged-blocks
                           fn-hp-u64-listp fn-his-put-append reverse floor))))
  :rule-classes nil)

(defthm fn-his-merged-blocks-split
 (implies
  (and (fn-his-cellsp cells) (fn-his-cursors-at rcs lens) (nat-listp starts) (natp np)
       (equal (len cells) (len lens)) (equal (len starts) (len lens))
       (adt-placement-ok starts (fn-hp-x-add lens (fn-his-cell-bytes cells)) np)
       (fn-his-rcs-fitp cells rcs starts (pgs-w-length pgs-mem) (pgs-d-length pgs-mem)))
  (equal (fn-hp-x-put-blocks (fn-his-merged-blocks cells rcs starts) pgs-mem)
         (fn-hp-x-put-blocks (fn-hp-bb-list starts lens cells)
          (fn-his-rcs-flush-write rcs starts pgs-mem))))
 :hints (("Goal" :induct (fn-his-merged-split-ind cells rcs lens starts pgs-mem)
          :in-theory (e/d (fn-his-cursors-at fn-hp-x-add fn-his-cell-bytes adt-placement-ok len)
                          (fn-his-rcp fn-his-rc-fitp fn-hp-x-put fn-his-rcs-flush-write
                           fn-hp-x-put-blocks fn-hp-bb-list fn-his-merged-blocks
                           fn-his-put-append reverse floor adt-cap adt-apart fn-hp-u64-listp
                           fn-his-flush-consp fn-his-flush-cons)))
         ("Subgoal *1/1" :in-theory (enable fn-his-merged-blocks fn-hp-bb-list fn-hp-x-put-blocks))
         ("Subgoal *1/2"
          :use ((:instance fn-his-merged-head-write)
                (:instance fn-his-bb-head-after-flush)
                (:instance fn-his-merged-write-keeps-lengths (ws (car cells)) (rc (car rcs)) (start (car starts)))))))
