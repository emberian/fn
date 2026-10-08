; Pass 2 of the canonical history image: one encode per row, five final
; region cursors, and a generated resumable quantum. No growth or relocation.
(in-package "ACL2")
(include-book "history-image-plan")
(include-book "history-image-row-encode")
(include-book "history-image-cursors")

(defconst *fn-his-rc0* '(0 0 nil))
(defconst *fn-his-pw0*
 '(0 (0 0 0 0 0) ((0 0 nil) (0 0 nil) (0 0 nil) (0 0 nil) (0 0 nil))))

(defun fn-his-pwp (pw)
 (declare (xargs :guard t))
 (and (true-listp pw) (equal (len pw) 3)
      (natp (car pw)) (nat-listp (cadr pw)) (equal (len (cadr pw)) 5)))

(defun fn-his-place-row (ev salt pw starts np pgs-mem)
 (declare (xargs :stobjs pgs-mem :guard t
                 :guard-hints (("Goal" :in-theory
                                (disable fn-hp-x-row fn-hp-pack8 fn-his-rcs-put
                                         adt-placement-ok fn-hp-mkey floor)))))
 (if (not (and (fn-his-pwp pw) (nat-listp starts) (equal (len starts) 5) (natp np)))
     (mv '(:refused :placement) pw pgs-mem)
   (let ((n (car pw)) (lens (cadr pw)) (rcs (caddr pw)))
     (mv-let (v tl pe) (fn-hp-x-row ev)
       (if v (mv v pw pgs-mem)
         (let* ((plen (len pe)) (lens2 (fn-hp-x-add lens (list 8 8 8 8 plen))))
           (if (not (adt-placement-ok starts lens2 np))
               (mv '(:refused :plan-mismatch) pw pgs-mem)
             (let ((cells (list (list (fn-hp-mkey ev salt)) (list tl) (list (nth 4 lens))
                                (list plen) (fn-hp-pack8 (floor plen 8) pe))))
               (if (not (fn-his-cellsp cells)) (mv '(:refused :placement) pw pgs-mem)
                 (mv-let (v rcs pgs-mem) (fn-his-rcs-put cells rcs starts pgs-mem)
                   (if v (mv v pw pgs-mem)
                     (mv :ok (list (+ 1 n) lens2 rcs) pgs-mem))))))))))))

(defthm fn-his-place-row-status
 (and (not (equal (car (fn-his-place-row ev salt pw starts np pgs-mem)) :done))
      (not (equal (car (fn-his-place-row ev salt pw starts np pgs-mem)) :more)))
 :hints (("Goal" :in-theory
          (e/d (fn-his-place-row fn-hp-x-row fn-his-rcs-put)
               (fn-his-pwp fn-his-rcs-fitp fn-his-rcs-write fn-his-cellsp
                fn-hp-mkey fn-hp-pack8 fn-scc-encode fn-scc-encode-is-program
                fn-sccb-treep fn-hp-pad8 adt-placement-ok floor)))))

(defthm fn-his-place-row-keeps-w-length
 (equal (pgs-w-length (mv-nth 2 (fn-his-place-row ev salt pw starts np pgs-mem)))
        (pgs-w-length pgs-mem))
 :hints (("Goal" :in-theory
          (e/d (fn-his-place-row)
               (fn-his-pwp fn-hp-x-row fn-his-rcs-put fn-his-cellsp fn-hp-mkey
                fn-hp-pack8 adt-placement-ok floor)))))

(defthm fn-his-place-row-refuses-placement-unchanged
 (implies (equal (mv-nth 0 (fn-his-place-row ev salt pw starts np pgs-mem)) '(:refused :placement))
          (equal (mv-nth 2 (fn-his-place-row ev salt pw starts np pgs-mem)) pgs-mem))
 :hints (("Goal" :in-theory
          (e/d (fn-his-place-row fn-his-rcs-put)
               (fn-his-pwp fn-hp-x-row fn-his-rcs-write fn-his-rcs-fitp fn-his-cellsp
                fn-hp-mkey fn-hp-pack8 adt-placement-ok floor)))))

(local (in-theory (disable fn-his-place-row fn-hp-x-row fn-his-rcs-put)))
(def-loop/run fn-his-place (evs salt pw starts np pgs-mem)
 :acc pw :st pgs-mem :quantum *fn-his-build-yield-rows* :success :ok
 :row (fn-his-place-row (car evs) salt pw starts np pgs-mem)
 :row-theory (fn-hp-x-row fn-his-rcs-put)
 :end-status (if (null evs) :ok '(:refused :event)))

(defthm fn-his-place-drive-is-place-all
  (let ((a (fn-his-place-drive (+ 1 (len evs)) evs salt pw starts np pgs-mem))
        (b (fn-his-place-all evs salt pw starts np pgs-mem)))
    (and (equal (mv-nth 0 a) (mv-nth 0 b))
         (equal (mv-nth 1 a) (mv-nth 1 b))
         (equal (mv-nth 2 a) (mv-nth 2 b))))
  :hints (("Goal" :use fn-his-place-drive-is-all
           :in-theory (disable fn-his-place-drive fn-his-place-all)))
  :rule-classes nil)

(defthm fn-his-place-run-keeps-w-length
  (equal (pgs-w-length (mv-nth 3 (fn-his-place-run k evs salt pw starts np pgs-mem)))
         (pgs-w-length pgs-mem))
  :hints (("Goal" :induct (fn-his-place-run k evs salt pw starts np pgs-mem)
           :in-theory (disable fn-his-place-row)))
  :rule-classes nil)

(defthm fn-his-place-row-preserves-pwp
 (implies (fn-his-pwp pw)
          (fn-his-pwp (mv-nth 1 (fn-his-place-row ev salt pw starts np pgs-mem))))
 :hints (("Goal" :in-theory
          (e/d (fn-his-place-row fn-his-pwp fn-hp-x-add)
               (fn-hp-x-row fn-his-rcs-put fn-his-cellsp fn-hp-mkey
                fn-hp-pack8 adt-placement-ok floor)))))

(defthm fn-his-place-all-preserves-pwp
 (implies (fn-his-pwp pw)
          (fn-his-pwp (mv-nth 1 (fn-his-place-all evs salt pw starts np pgs-mem))))
 :hints (("Goal" :induct (fn-his-place-all evs salt pw starts np pgs-mem)
          :in-theory (disable fn-his-place-row fn-his-pwp))))

(defthm fn-his-place-drive-preserves-pwp
 (implies (fn-his-pwp pw)
          (fn-his-pwp (mv-nth 1 (fn-his-place-drive (+ 1 (len evs)) evs salt pw starts np pgs-mem))))
 :hints (("Goal" :use fn-his-place-drive-is-all
          :in-theory (disable fn-his-place-drive fn-his-place-all fn-his-pwp))))
