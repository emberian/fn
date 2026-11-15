; Shared pure installed-directory geometry for C and predecessor admission.
(in-package "ACL2")
(include-book "format-base")
(fn2-book-layer :b)
(defun fn2-run-installed-row-count (resident capacity)
 (declare (xargs :guard (and (natp resident) (natp capacity))))
 (+ resident (* 2 capacity)))
(defthm fn2-run-installed-row-count-natp
 (implies (and (natp resident) (natp capacity))
  (natp (fn2-run-installed-row-count resident capacity)))
 :rule-classes :type-prescription)
