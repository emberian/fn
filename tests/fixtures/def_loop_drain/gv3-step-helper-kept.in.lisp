(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-cll-key-values-step (x rest)
  (declare (xargs :guard t))
  (fn-cll-append *fn-cll-key-word* (fn-cll-append x rest)))

(defun fn-cll-key-values-loop (rev acc)
  (declare (xargs :guard t))
  (if (consp rev)
      (fn-cll-key-values-loop (cdr rev) (fn-cll-key-values-step (car rev) acc))
    acc))

(defun fn-cll-key-values (keys)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp keys)
           (fn-cll-append *fn-cll-key-word*
                          (fn-cll-append (car keys) (fn-cll-key-values (cdr keys))))
         nil)
       :exec (fn-cll-key-values-loop (fn-ag-rev-onto keys nil) nil)))

(defthm fn-cll-key-values-loop-of-rev-onto
  (equal (fn-cll-key-values-loop (fn-ag-rev-onto keys zs) nil)
         (fn-cll-key-values-loop zs (fn-cll-key-values keys)))
  :hints (("Goal" :induct (fn-ag-rev-onto keys zs)
                  :in-theory (union-theories
                              '(fn-cll-key-values-loop fn-cll-key-values fn-cll-key-values-step fn-ag-rev-onto
                                car-cons cdr-cons)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

(verify-guards fn-cll-key-values
  :hints (("Goal" :use ((:instance fn-cll-key-values-loop-of-rev-onto (zs nil)))
                  :in-theory (union-theories
                              '(fn-cll-key-values-loop fn-cll-key-values)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

(defthm fn-cll-key-values-step-of-nil
  (equal (fn-cll-key-values-step nil rest) (fn-cll-append *fn-cll-key-word* (fn-cll-append nil rest))))
