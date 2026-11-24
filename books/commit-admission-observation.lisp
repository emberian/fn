; The workspace, owner, event and settlement columns in a range of member rows.
(in-package "ACL2")
(include-book "commit-members")
(fn2-book-layer :b)

(defun fn2-ctp-member-fields (r fn2-commit-member)
 (declare (xargs :stobjs fn2-commit-member :verify-guards nil))
 (if (< (nfix r) (fn2-commit-member-rows fn2-commit-member))
     (let ((row (fn2-commit-member-row-snapshot r fn2-commit-member)))
       (append (take 7 row) (nthcdr 10 row)))
   nil))

(defun fn2-ctp-member-fields-range (r n fn2-commit-member)
 (declare (xargs :stobjs fn2-commit-member :verify-guards nil :measure (nfix n)))
 (if (zp n) nil
  (cons (fn2-ctp-member-fields r fn2-commit-member)
        (fn2-ctp-member-fields-range (+ 1 (nfix r)) (- n 1) fn2-commit-member))))
