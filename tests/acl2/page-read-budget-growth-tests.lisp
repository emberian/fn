(in-package "ACL2")
(include-book "../../books/page-read-budget-growth")
(defconst *prgrowth-ledger* '((1000 0 2 1 10) (100 0 1 0 1) 7 (((token) (100 0 1 0 1))) (400 0 0 0 0)))
(assert-event
 (let* ((r (mv-list 2 (fn-prl-resident-shrink 200 *prgrowth-ledger*))) (next (cadr r)))
  (and (equal (car r) :protected-growth-admitted)
       (fn-prs-fundedp (car *prgrowth-ledger*) (fn-prl-baseline *prgrowth-ledger*) '(0 0 0 0 0) (cadr *prgrowth-ledger*))
       (fn-prs-fundedp (car next) (fn-prl-baseline next) '(0 0 0 0 0) (cadr next))
       (equal (car next) '(800 0 2 1 10))
       (equal (cdr next) (cdr *prgrowth-ledger*)))))
(assert-event
 (and (equal (mv-list 2 (fn-prl-resident-shrink 501 *prgrowth-ledger*))
             (list :read-resources-unavailable *prgrowth-ledger*))
      (equal (mv-list 2 (fn-prl-resident-shrink -1 *prgrowth-ledger*))
             (list :read-resources-unavailable *prgrowth-ledger*))))
; Corrupted-state omission of the funding antecedent; custody remains framed.
(assert-event
 (let* ((bad (cons '(100 0 2 1 10) (cdr *prgrowth-ledger*)))
        (next (mv-nth 1 (fn-prl-resident-shrink 0 bad))))
  (and (not (fn-prs-fundedp (car bad) (fn-prl-baseline bad) '(0 0 0 0 0) (cadr bad)))
       (not (fn-prs-fundedp (car next) (fn-prl-baseline next) '(0 0 0 0 0) (cadr next)))
       (equal (cdr next) (cdr bad)))))
