; Canonical placement supplies the separation needed by cursor materialization.
(in-package "ACL2")
(include-book "history-image-content-proof")
(local (include-book "arithmetic/top" :dir :system))

(defthm fn-his-rc-merged-within-cap
 (implies (and (fn-his-rcp rc) (natp start)
               (equal used (* 8 (+ (* 2048 (car rc)) (cadr rc)))))
  (and (<= (* 2048 start) (* 2048 (+ start (car rc))))
       (<= (+ (* 2048 (+ start (car rc))) (cadr rc) (len ws))
           (* 2048 (+ start (adt-cap (+ used (* 8 (len ws)))))))))
 :hints (("Goal" :use ((:instance adt-cap-covers (u (+ used (* 8 (len ws))))))
          :in-theory (e/d (fn-his-rcp) (adt-cap adt-cap-covers len)))))

(defthm fn-his-put-apart-from-placed-cursors
 (implies
  (and (natp s) (natp cap) (natp j)
       (<= (* 2048 s) j) (<= (+ j (len ys)) (* 2048 (+ s cap)))
       (fn-his-cellsp cells) (fn-his-cursors-at rcs lens) (nat-listp starts)
       (equal (len cells) (len lens)) (equal (len starts) (len lens))
       (adt-apart s cap starts (fn-hp-x-add lens (fn-his-cell-bytes cells))))
  (fn-his-put-apart-from-cursors j ys cells rcs starts))
 :hints (("Goal" :induct (fn-his-region-ind cells rcs lens starts)
          :in-theory (e/d (fn-his-cursors-at fn-hp-x-add fn-his-cell-bytes adt-apart len)
                          (fn-his-rcp adt-cap)))
         ("Subgoal *1/2"
          :use ((:instance fn-his-rc-merged-within-cap (rc (car rcs)) (start (car starts))
                           (used (car lens)) (ws (car cells)))))))

(defthm fn-his-cursors-apart-of-placement
 (implies
  (and (fn-his-cellsp cells) (fn-his-cursors-at rcs lens) (nat-listp starts) (natp np)
       (equal (len cells) (len lens)) (equal (len starts) (len lens))
       (adt-placement-ok starts (fn-hp-x-add lens (fn-his-cell-bytes cells)) np))
  (fn-his-cursors-apart cells rcs starts))
 :hints (("Goal" :induct (fn-his-region-ind cells rcs lens starts)
          :in-theory (e/d (fn-his-cursors-at fn-his-cursors-apart fn-hp-x-add
                                           fn-his-cell-bytes adt-placement-ok len)
                          (fn-his-rcp fn-his-put-apart-from-cursors adt-cap adt-apart)))
         ("Subgoal *1/2"
          :use ((:instance fn-his-rc-merged-within-cap
                  (rc (car rcs)) (start (car starts)) (used (car lens)) (ws (car cells)))
                (:instance fn-his-put-apart-from-placed-cursors
                  (s (car starts)) (cap (adt-cap (+ (car lens) (* 8 (len (car cells))))))
                  (j (* 2048 (+ (car starts) (car (car rcs)))))
                  (ys (append (reverse (caddr (car rcs))) (car cells)))
                  (cells (cdr cells)) (rcs (cdr rcs)) (lens (cdr lens)) (starts (cdr starts)))))))
