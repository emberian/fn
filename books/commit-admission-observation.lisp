; The member columns and row differences observed at transaction admission.
(in-package "ACL2")
(include-book "commit-members")
(fn2-book-layer :b)

(defun fn2-ctp-member-fields (r fn2-commit-member)
 (declare (xargs :stobjs fn2-commit-member :verify-guards nil))
  (if (< (nfix r) (fn2-commit-member-rows fn2-commit-member))
      (list (fn2-commit-member-kind r fn2-commit-member) (fn2-commit-member-slot r fn2-commit-member)
            (fn2-commit-member-gen r fn2-commit-member) (fn2-commit-member-len r fn2-commit-member)
            (fn2-commit-member-okind r fn2-commit-member) (fn2-commit-member-oslot r fn2-commit-member)
            (fn2-commit-member-ogen r fn2-commit-member) (fn2-commit-member-event r fn2-commit-member)
            (fn2-commit-member-settled r fn2-commit-member))
    nil))

(defun fn2-ctp-member-fields-range (r n fn2-commit-member)
 (declare (xargs :stobjs fn2-commit-member :verify-guards nil :measure (nfix n)))
 (if (zp n) nil
  (cons (fn2-ctp-member-fields r fn2-commit-member)
        (fn2-ctp-member-fields-range (+ 1 (nfix r)) (- n 1) fn2-commit-member))))

(defun fn2-ctp-diffs (a b)
 (declare (xargs :verify-guards nil))
 (cond ((or (atom a) (atom b)) nil)
       ((equal (car a) (car b)) (fn2-ctp-diffs (cdr a) (cdr b)))
       (t (cons (car b) (fn2-ctp-diffs (cdr a) (cdr b))))))
; Admission is total: :ok changes exactly one member row, and that row holds
; the admitted workspace and its owner; any other answer changes nothing.
(defun fn2-ctp-totalp (code slot gen len oslot before after)
 (declare (xargs :verify-guards nil))
 (if (eq code :ok)
     (let ((d (fn2-ctp-diffs (car before) (car after))))
      (and (equal (len d) 1)
           (equal (take 7 (car d))
                  (list *fn2-commit-member-kind-txn* slot gen len 9 oslot 5))))
   (and (member-eq code '(:exhausted :admission)) (equal before after))))
