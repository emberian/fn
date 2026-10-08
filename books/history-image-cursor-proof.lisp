; Cursor progress and materialization lemmas for the final-placement builder.
(in-package "ACL2")
(include-book "history-image-cursors")
(local (include-book "arithmetic/top" :dir :system))

(defthm fn-his-rc-write-position
 (implies (fn-his-rcp rc)
  (let ((out (mv-nth 0 (fn-his-rc-write ws rc start pgs-mem))))
   (and (fn-his-rcp out)
        (equal (+ (* 2048 (car out)) (cadr out))
               (+ (* 2048 (car rc)) (cadr rc) (len ws))))))
 :hints (("Goal" :induct (fn-his-rc-write ws rc start pgs-mem)
          :in-theory (e/d (fn-his-rcp len) (fn-hp-x-put reverse floor)))))

(defthm fn-his-rc-write-fits
 (implies (fn-his-rc-fitp (len ws) rc start nw nd)
  (fn-his-rc-fitp 0 (mv-nth 0 (fn-his-rc-write ws rc start pgs-mem)) start nw nd))
 :hints (("Goal" :use fn-his-rc-write-position
          :in-theory (e/d (fn-his-rc-fitp)
                          (fn-his-rc-write fn-his-rcp fn-his-rc-write-position)))))

(defthm fn-his-put-append
 (implies (and (natp j) (true-listp a))
  (equal (fn-hp-x-put j (append a b) pgs-mem)
         (fn-hp-x-put (+ j (len a)) b (fn-hp-x-put j a pgs-mem))))
 :hints (("Goal" :induct (fn-hp-x-put j a pgs-mem)
          :in-theory (e/d (fn-hp-x-put len) (floor update-pgs-wi update-pgs-di)))))

(defthm fn-his-rc-write-buffer-listp
 (implies (fn-his-rcp rc)
  (true-listp (caddr (mv-nth 0 (fn-his-rc-write ws rc start pgs-mem)))))
 :hints (("Goal" :use fn-his-rc-write-position
          :in-theory (e/d (fn-his-rcp) (fn-his-rc-write fn-his-rc-write-position)))))

(defthm fn-his-put-cons
 (implies (consp b)
  (equal (fn-hp-x-put j (cons a b) pgs-mem)
         (fn-hp-x-put (+ 1 j) b (fn-hp-x-put j (list a) pgs-mem))))
 :hints (("Goal" :expand ((fn-hp-x-put j (cons a b) pgs-mem)
                          (fn-hp-x-put j (list a) pgs-mem))
          :in-theory (disable floor update-pgs-wi update-pgs-di))))

(defthm fn-his-rc-write-materializes
 (implies (and (fn-his-rcp rc) (natp start) (true-listp ws))
  (let* ((res (fn-his-rc-write ws rc start pgs-mem))
         (out (mv-nth 0 res)) (mem (mv-nth 1 res)))
   (equal (fn-hp-x-put (* 2048 (+ start (car out))) (reverse (caddr out)) mem)
          (fn-hp-x-put (* 2048 (+ start (car rc)))
                       (append (reverse (caddr rc)) ws) pgs-mem))))
 :hints (("Goal" :induct (fn-his-rc-write ws rc start pgs-mem)
          :in-theory (e/d (fn-his-rcp len fn-hp-x-put)
                          (fn-his-put-cons floor update-pgs-wi update-pgs-di)))))

(defthm fn-his-rc-write-buffer-u64
 (implies (and (fn-hp-u64-listp ws) (fn-hp-u64-listp (caddr rc)))
  (fn-hp-u64-listp (caddr (mv-nth 0 (fn-his-rc-write ws rc start pgs-mem)))))
 :hints (("Goal" :induct (fn-his-rc-write ws rc start pgs-mem)
          :in-theory (disable fn-hp-x-put floor))))

(defthm fn-his-rcs-write-fits-flush
 (implies (and (fn-his-cellsp cells)
               (fn-his-rcs-fitp cells rcs starts
                                (pgs-w-length pgs-mem) (pgs-d-length pgs-mem)))
  (let ((out (fn-his-rcs-write cells rcs starts pgs-mem)))
   (fn-his-rcs-flush-fitp (mv-nth 0 out) starts
                         (pgs-w-length (mv-nth 1 out))
                         (pgs-d-length (mv-nth 1 out)))))
 :hints (("Goal" :induct (fn-his-rcs-write cells rcs starts pgs-mem)
           :in-theory (disable fn-his-rc-write fn-his-rc-fitp fn-his-rcp))
         ("Subgoal *1/2"
          :use ((:instance fn-his-rc-write-fits (ws (car cells)) (rc (car rcs))
                           (start (car starts)) (nw (pgs-w-length pgs-mem))
                           (nd (pgs-d-length pgs-mem)))
                (:instance fn-his-rc-write-buffer-u64 (ws (car cells)) (rc (car rcs))
                           (start (car starts)))))))

(defthm fn-his-put-keeps-verified
 (and (equal (pgs-v-length (fn-hp-x-put j ws pgs-mem)) (pgs-v-length pgs-mem))
      (equal (nth *pgs-vi* (fn-hp-x-put j ws pgs-mem)) (nth *pgs-vi* pgs-mem)))
 :hints (("Goal" :induct (fn-hp-x-put j ws pgs-mem)
          :in-theory (e/d (fn-hp-x-put pgs-v-length)
                          (floor update-pgs-wi update-pgs-di nth adt-nth-1+)))))

(defthm fn-his-rc-write-keeps-verified
 (and (equal (pgs-v-length (mv-nth 1 (fn-his-rc-write ws rc start pgs-mem))) (pgs-v-length pgs-mem))
      (equal (nth *pgs-vi* (mv-nth 1 (fn-his-rc-write ws rc start pgs-mem))) (nth *pgs-vi* pgs-mem)))
 :hints (("Goal" :induct (fn-his-rc-write ws rc start pgs-mem)
          :in-theory (disable fn-hp-x-put nth adt-nth-1+))))

(defthm fn-his-rcs-write-keeps-verified
 (and (equal (pgs-v-length (mv-nth 1 (fn-his-rcs-write cells rcs starts pgs-mem))) (pgs-v-length pgs-mem))
      (equal (nth *pgs-vi* (mv-nth 1 (fn-his-rcs-write cells rcs starts pgs-mem))) (nth *pgs-vi* pgs-mem)))
 :hints (("Goal" :induct (fn-his-rcs-write cells rcs starts pgs-mem)
          :in-theory (disable fn-his-rc-write nth adt-nth-1+))))

(defthm fn-his-rcs-put-keeps-d-and-v
 (and (equal (pgs-d-length (mv-nth 2 (fn-his-rcs-put cells rcs starts pgs-mem))) (pgs-d-length pgs-mem))
      (equal (pgs-v-length (mv-nth 2 (fn-his-rcs-put cells rcs starts pgs-mem))) (pgs-v-length pgs-mem))
      (equal (nth *pgs-vi* (mv-nth 2 (fn-his-rcs-put cells rcs starts pgs-mem))) (nth *pgs-vi* pgs-mem)))
 :hints (("Goal" :in-theory (e/d (fn-his-rcs-put)
                                (fn-his-rcs-write fn-his-rcs-fitp nth adt-nth-1+)))))

(defthm fn-his-flush-write-keeps-verified
 (and (equal (pgs-v-length (fn-his-rcs-flush-write rcs starts pgs-mem)) (pgs-v-length pgs-mem))
      (equal (nth *pgs-vi* (fn-his-rcs-flush-write rcs starts pgs-mem)) (nth *pgs-vi* pgs-mem)))
 :hints (("Goal" :induct (fn-his-rcs-flush-write rcs starts pgs-mem)
          :in-theory (disable fn-hp-x-put nth adt-nth-1+))))
