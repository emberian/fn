(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-tlsr-split-loop (n xs acc)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (not (consp xs)))
      (cons (fn-ag-rev-onto acc nil) xs)
    (fn-tlsr-split-loop (- n 1) (cdr xs) (cons (car xs) acc))))

(defun fn-tlsr-split (n xs)
  (declare (xargs :guard (natp n) :verify-guards nil))
  (mbe :logic (if (or (zp n) (not (consp xs)))
                  (cons nil xs)
                (let ((r (fn-tlsr-split (- n 1) (cdr xs))))
                  (cons (cons (car xs) (car r)) (cdr r))))
       :exec (fn-tlsr-split-loop n xs nil)))

(defthm fn-tlsr-split-loop-is-rev-onto
  (equal (fn-tlsr-split-loop n xs acc)
         (cons (fn-ag-rev-onto acc (car (fn-tlsr-split n xs)))
               (cdr (fn-tlsr-split n xs))))
  :hints (("Goal" :induct (fn-tlsr-split-loop n xs acc)
                  :in-theory (union-theories
                              '(fn-tlsr-split-loop fn-tlsr-split
                                fn-ag-rev-onto car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(verify-guards fn-tlsr-split
  :hints (("Goal" :in-theory (disable fn-tlsr-split-loop))))
