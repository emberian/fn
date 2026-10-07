(in-package "ACL2")
(include-book "../../books/page-read-budget-growth")
(include-book "../../books/defkeystone")
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
        (next (mv-nth 1 (mv-list 2 (fn-prl-resident-shrink 0 bad)))))
  (and (not (fn-prs-fundedp (car bad) (fn-prl-baseline bad) '(0 0 0 0 0) (cadr bad)))
       (not (fn-prs-fundedp (car next) (fn-prl-baseline next) '(0 0 0 0 0) (cadr next)))
       (equal (cdr next) (cdr bad)))))

; ---------------------------------------------------------------------------
; fn-prl-resident-shrink-preserves-custody and -keeps-funding (TEETH CONTRACT
; v1).  fn-prl-resident-shrink answers two values, so the witnesses are ground
; theorems (:witness-lemma, :lemma; TEETH-OWED-MV-CLAIM lemma debt): each is
; the conjunction the entry would assert, with the claim's `let' binding the
; free variable explicitly so its translation is the instantiated claim's.
; The shrink by 200 of *prgrowth-ledger* is the witness; the funding
; antecedent is removed at the ledger whose resident budget (100) is below
; its funding, which the shrink refuses and returns unchanged.
(defconst *prgrowth-unfunded*
  (cons '(100 0 2 1 10) (cdr *prgrowth-ledger*)))

(defthm prgrowth-custody-witness
  (let ((next (mv-nth 1 (fn-prl-resident-shrink 200 *prgrowth-ledger*)))
        (ledger *prgrowth-ledger*))
    (and (equal (fn-prl-nth 1 next) (fn-prl-nth 1 ledger))
         (equal (fn-prl-nth 2 next) (fn-prl-nth 2 ledger))
         (equal (fn-prl-nth 3 next) (fn-prl-nth 3 ledger))
         (equal (fn-prl-nth 4 next) (fn-prl-nth 4 ledger)))))
(defthm prgrowth-custody-mutant-witness
  (and (let ((next (mv-nth 1 (fn-prl-resident-shrink 200 *prgrowth-ledger*)))
             (ledger *prgrowth-ledger*))
         (and (equal (fn-prl-nth 1 next) (fn-prl-nth 1 ledger))
              (equal (fn-prl-nth 2 next) (fn-prl-nth 2 ledger))
              (equal (fn-prl-nth 3 next) (fn-prl-nth 3 ledger))
              (equal (fn-prl-nth 4 next) (fn-prl-nth 4 ledger))))
       (not (let ((next (mv-nth 1 (fn-prl-resident-shrink 200 *prgrowth-ledger*)))
                  (ledger *prgrowth-ledger*))
              (and (equal (fn-prl-nth 1 next) '(0 0 0 0 0))
                   (equal (fn-prl-nth 2 next) (fn-prl-nth 2 ledger))
                   (equal (fn-prl-nth 3 next) (fn-prl-nth 3 ledger))
                   (equal (fn-prl-nth 4 next) (fn-prl-nth 4 ledger)))))))
(defteeth fn-prl-resident-shrink-preserves-custody
  :claim (() (let ((next (mv-nth 1 (fn-prl-resident-shrink amount ledger))))
               (and (equal (fn-prl-nth 1 next) (fn-prl-nth 1 ledger))
                    (equal (fn-prl-nth 2 next) (fn-prl-nth 2 ledger))
                    (equal (fn-prl-nth 3 next) (fn-prl-nth 3 ledger))
                    (equal (fn-prl-nth 4 next) (fn-prl-nth 4 ledger)))))
  :subject fn-prl-resident-shrink
  :witness-lemma prgrowth-custody-witness
  :witness ((amount 200) (ledger *prgrowth-ledger*))
  :mutations ((charged-cleared
               (:conclusion (let ((next (mv-nth 1 (fn-prl-resident-shrink amount ledger))))
                              (and (equal (fn-prl-nth 1 next) '(0 0 0 0 0))
                                   (equal (fn-prl-nth 2 next) (fn-prl-nth 2 ledger))
                                   (equal (fn-prl-nth 3 next) (fn-prl-nth 3 ledger))
                                   (equal (fn-prl-nth 4 next) (fn-prl-nth 4 ledger)))))
               ((amount 200) (ledger *prgrowth-ledger*))
               :fault "a shrink that clears the charged reads"
               :lemma prgrowth-custody-mutant-witness)))

