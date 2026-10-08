(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-ng-len-loop (rev acc)
  (declare (xargs :guard (rationalp acc) :verify-guards nil))
  (if (consp rev) (fn-ng-len-loop (cdr rev) (1+ acc)) acc))

(defun fn-ng-len (xs)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp xs) (1+ (fn-ng-len (fn-ag-cdr xs))) 0)
       :exec (fn-ng-len-loop (fn-ag-rev-onto xs nil) 0)))

(local
 (defthm fn-ng-len-loop-of-rev-onto
   (equal (fn-ng-len-loop (fn-ag-rev-onto xs zs) 0)
          (fn-ng-len-loop zs (fn-ng-len xs)))
   :hints (("Goal" :induct (fn-ag-rev-onto xs zs)
                   :in-theory (union-theories '(fn-ng-len-loop fn-ng-len fn-ag-rev-onto fn-ag-car fn-ag-cdr
                                                car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-ng-len-loop)

(verify-guards fn-ng-len
  :hints (("Goal" :in-theory (union-theories '(fn-ng-len fn-ng-len-loop)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-ng-len-loop-of-rev-onto (zs nil))))))
