(in-package "ACL2")
(include-book "../../books/post-identity-source-cursor-invariants")
; Literal positive witness: the actual control and byte step return a proper list.
(assert-event
 (let* ((c (fn-psc-begin :agent 4 "<a@b>" nil 4))
        (next (fn-psc-step c nil)))
  (and (true-listp c) (true-listp next)
       (true-listp (fn-psc-step next 97)))))
; Corrupted-state / hypothesis-removal witness: done does not repair improper state.
(assert-event
 (with-guard-checking :none
 (let ((c '(:done . :improper)))
  (and (not (true-listp c)) (not (true-listp (ec-call (fn-psc-step c 97))))))))
