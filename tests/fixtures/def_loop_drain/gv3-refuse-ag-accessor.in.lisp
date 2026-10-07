(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-bump-number-loop (group nexts acc)
  (declare (xargs :guard (true-listp acc)))
  (if (consp nexts)
      (if (equal group (fn-ag-car (fn-ag-car nexts)))
          (revappend acc (cons (cons (fn-ag-car (fn-ag-car nexts))
                                     (1+ (fix (fn-ag-cdr (fn-ag-car nexts)))))
                               (fn-ag-cdr nexts)))
        (fn-bump-number-loop group (fn-ag-cdr nexts) (cons (fn-ag-car nexts) acc)))
    (revappend acc nil)))

(defun fn-bump-number (group nexts)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp nexts)
           (if (equal group (car (car nexts)))
               (cons (cons (car (car nexts))
                           (1+ (cdr (car nexts))))
                     (cdr nexts))
             (cons (car nexts)
                   (fn-bump-number group (cdr nexts))))
         nil)
       :exec (fn-bump-number-loop group nexts nil)))

(local
 (defthm fn-bump-number-loop-is-revappend
   (equal (fn-bump-number-loop group nexts acc)
          (revappend acc (fn-bump-number group nexts)))
   :hints (("Goal" :induct (fn-bump-number-loop group nexts acc)))))

(verify-guards fn-bump-number
  :hints (("Goal" :in-theory (disable fn-bump-number-loop)
                  :use ((:instance fn-bump-number-loop-is-revappend (acc nil))))))
