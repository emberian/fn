; The two passes and final flush, composed over the page-store entry.
(in-package "ACL2")
(include-book "history-image-open")
(include-book "history-image-place")

(defun fn-his-image-close (plan pw starts pgs-mem)
 (declare (xargs :stobjs pgs-mem :guard t))
 (cond ((not (fn-his-pwp pw)) (mv '(:refused :placement) pgs-mem))
       ((not (equal (list (car pw) (cadr pw)) plan))
        (mv '(:refused :plan-mismatch) pgs-mem))
       ((not (and (true-listp (caddr pw)) (equal (len (caddr pw)) 5)
                  (true-listp starts) (equal (len starts) 5)))
        (mv '(:refused :placement) pgs-mem))
       (t (fn-his-rcs-flush (caddr pw) starts pgs-mem))))

(local
 (defthm fn-his-place-drive-result-cells
  (implies (fn-his-pwp pw)
   (let ((out (mv-nth 1 (fn-his-place-drive (+ 1 (len evs)) evs salt pw starts np pgs-mem))))
    (and (consp out) (consp (cdr out)))))
  :hints (("Goal" :use fn-his-place-drive-preserves-pwp
           :in-theory (e/d (fn-his-pwp) (fn-his-place-drive fn-his-place-drive-preserves-pwp))))))

(defun fn-his-image-build-pgs (h salt pgs-mem)
 (declare (xargs :stobjs pgs-mem :guard t
                 :guard-hints (("Goal" :in-theory
                                (e/d ()
                                     (len fn-his-pwp fn-his-planp fn-his-plan-drive fn-his-place-drive
                                      fn-his-image-open fn-his-image-close))))))
 (mv-let (v plan) (fn-his-plan-drive (+ 1 (len h)) h (list 0 '(0 0 0 0 0)))
   (if v (mv v 0 '(0 0 0 0 0) nil 0 pgs-mem)
     (mv-let (v starts np pgs-mem) (fn-his-image-open plan pgs-mem)
       (if v (mv v 0 '(0 0 0 0 0) nil 0 pgs-mem)
         (mv-let (v pw pgs-mem)
           (fn-his-place-drive (+ 1 (len h)) h salt *fn-his-pw0* starts np pgs-mem)
           (if (not (eq v :ok)) (mv v (car pw) (cadr pw) starts np pgs-mem)
             (mv-let (v pgs-mem) (fn-his-image-close plan pw starts pgs-mem)
               (mv v (car pw) (cadr pw) starts np pgs-mem)))))))))

(defun fn-his-all-dirty (p np d)
 (declare (xargs :guard (and (natp p) (natp np) (<= p np) (true-listp d))
                 :measure (nfix (- (nfix np) (nfix p)))))
 (if (zp (- (nfix np) (nfix p))) t
   (and (equal (nth p d) 1) (fn-his-all-dirty (+ 1 (nfix p)) np d))))
