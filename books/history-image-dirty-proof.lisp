; Mark-all remains true through every cursor write and final flush.
(in-package "ACL2")
(include-book "history-image-build")
(include-book "history-image-cursor-proof")
(local (include-book "arithmetic/top" :dir :system))

(defthm fn-his-all-dirty-update-one
 (implies (and (natp p) (natp np) (fn-his-all-dirty p np d))
          (fn-his-all-dirty p np (update-nth i 1 d)))
 :hints (("Goal" :induct (fn-his-all-dirty p np d)
          :in-theory (enable fn-his-all-dirty))))

(defthm fn-his-put-keeps-all-dirty
 (implies (and (natp p) (natp np) (fn-his-all-dirty p np (nth *pgs-di* pgs-mem)))
          (fn-his-all-dirty p np (nth *pgs-di* (fn-hp-x-put j ws pgs-mem))))
 :hints (("Goal" :induct (fn-hp-x-put j ws pgs-mem)
          :in-theory (e/d (fn-hp-x-put) (fn-his-all-dirty floor)))))

(defthm fn-his-mark-sets-dirty
 (implies (and (natp i) (natp p) (natp k))
          (equal (nth p (nth *pgs-di* (fn-hp-x-mark i k pgs-mem)))
                 (if (and (<= i p) (< p k)) 1 (nth p (nth *pgs-di* pgs-mem)))))
 :hints (("Goal" :induct (fn-hp-x-mark i k pgs-mem)
          :in-theory (enable fn-hp-x-mark update-pgs-di))))

(local
 (defun fn-his-dirty-range-ind (p k)
  (declare (xargs :guard (and (natp p) (natp k)) :measure (nfix (- (nfix k) (nfix p)))))
  (if (>= (nfix p) (nfix k)) nil
    (fn-his-dirty-range-ind (+ 1 (nfix p)) k))))

(defthm fn-his-mark-all-dirty
 (implies (and (natp i) (natp p) (natp k) (<= i p))
          (fn-his-all-dirty p k (nth *pgs-di* (fn-hp-x-mark i k pgs-mem))))
 :hints (("Goal" :induct (fn-his-dirty-range-ind p k)
          :in-theory (disable fn-hp-x-mark nth))
         ("Subgoal *1/2" :use fn-his-mark-sets-dirty)))

(defthm fn-his-rc-write-keeps-all-dirty
 (implies (and (natp p) (natp np) (fn-his-all-dirty p np (nth *pgs-di* pgs-mem)))
          (fn-his-all-dirty p np (nth *pgs-di* (mv-nth 1 (fn-his-rc-write ws rc start pgs-mem)))))
 :hints (("Goal" :induct (fn-his-rc-write ws rc start pgs-mem)
          :in-theory (disable fn-hp-x-put fn-his-all-dirty nth adt-nth-1+))))

(defthm fn-his-rcs-write-keeps-all-dirty
 (implies (and (natp p) (natp np) (fn-his-all-dirty p np (nth *pgs-di* pgs-mem)))
          (fn-his-all-dirty p np (nth *pgs-di* (mv-nth 1 (fn-his-rcs-write cells rcs starts pgs-mem)))))
 :hints (("Goal" :induct (fn-his-rcs-write cells rcs starts pgs-mem)
          :in-theory (disable fn-his-rc-write fn-his-all-dirty nth adt-nth-1+))))

(defthm fn-his-flush-write-keeps-all-dirty
 (implies (and (natp p) (natp np) (fn-his-all-dirty p np (nth *pgs-di* pgs-mem)))
          (fn-his-all-dirty p np (nth *pgs-di* (fn-his-rcs-flush-write rcs starts pgs-mem))))
 :hints (("Goal" :induct (fn-his-rcs-flush-write rcs starts pgs-mem)
          :in-theory (disable fn-hp-x-put fn-his-all-dirty nth adt-nth-1+))))

(defthm fn-his-place-row-keeps-all-dirty
 (implies (and (natp p) (natp np) (fn-his-all-dirty p np (nth *pgs-di* pgs-mem)))
          (fn-his-all-dirty p np (nth *pgs-di* (mv-nth 2 (fn-his-place-row ev salt pw starts np pgs-mem)))))
 :hints (("Goal" :in-theory
          (e/d (fn-his-place-row fn-his-rcs-put)
               (fn-his-pwp fn-hp-x-row fn-his-rcs-write fn-his-rcs-fitp fn-his-cellsp
                fn-hp-mkey fn-hp-pack8 fn-his-all-dirty adt-placement-ok floor nth adt-nth-1+)))))

(defthm fn-his-place-all-keeps-all-dirty
 (implies (and (natp p) (natp np) (fn-his-all-dirty p np (nth *pgs-di* pgs-mem)))
          (fn-his-all-dirty p np (nth *pgs-di* (mv-nth 2 (fn-his-place-all h salt pw starts np pgs-mem)))))
 :hints (("Goal" :induct (fn-his-place-all h salt pw starts np pgs-mem)
          :in-theory (disable fn-his-place-row fn-his-all-dirty nth adt-nth-1+))))

(defthm fn-his-image-close-keeps-all-dirty
 (implies (and (natp p) (natp np) (fn-his-all-dirty p np (nth *pgs-di* pgs-mem)))
          (fn-his-all-dirty p np (nth *pgs-di* (mv-nth 1 (fn-his-image-close plan pw starts pgs-mem)))))
 :hints (("Goal" :in-theory
          (e/d (fn-his-image-close fn-his-rcs-flush)
               (fn-his-pwp fn-his-rcs-flush-write fn-his-rcs-flush-fitp fn-his-all-dirty nth adt-nth-1+)))))
