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


(defthm prgrowth-funding-witness
  (and (fn-prs-fundedp (fn-prl-nth 0 *prgrowth-ledger*) (fn-prl-baseline *prgrowth-ledger*) '(0 0 0 0 0)
                       (fn-prl-nth 1 *prgrowth-ledger*))
       (let ((next (mv-nth 1 (fn-prl-resident-shrink 200 *prgrowth-ledger*))))
         (fn-prs-fundedp (fn-prl-nth 0 next) (fn-prl-baseline next) '(0 0 0 0 0) (fn-prl-nth 1 next)))))
(defthm prgrowth-funding-without-funded
  (and (not (fn-prs-fundedp (fn-prl-nth 0 *prgrowth-unfunded*) (fn-prl-baseline *prgrowth-unfunded*) '(0 0 0 0 0)
                            (fn-prl-nth 1 *prgrowth-unfunded*)))
       (not (let ((next (mv-nth 1 (fn-prl-resident-shrink 0 *prgrowth-unfunded*))))
              (fn-prs-fundedp (fn-prl-nth 0 next) (fn-prl-baseline next) '(0 0 0 0 0) (fn-prl-nth 1 next))))))
(defthm prgrowth-funding-mutant-witness
  (and (fn-prs-fundedp (fn-prl-nth 0 *prgrowth-ledger*) (fn-prl-baseline *prgrowth-ledger*) '(0 0 0 0 0)
                       (fn-prl-nth 1 *prgrowth-ledger*))
       (let ((next (mv-nth 1 (fn-prl-resident-shrink 200 *prgrowth-ledger*))))
         (fn-prs-fundedp (fn-prl-nth 0 next) (fn-prl-baseline next) '(0 0 0 0 0) (fn-prl-nth 1 next)))
       (not (let ((next (mv-nth 1 (fn-prl-resident-shrink 200 *prgrowth-ledger*))))
              (not (fn-prs-fundedp (fn-prl-nth 0 next) (fn-prl-baseline next) '(0 0 0 0 0) (fn-prl-nth 1 next)))))))
(defteeth fn-prl-resident-shrink-keeps-funding
  :claim (((funded (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger) '(0 0 0 0 0)
                                   (fn-prl-nth 1 ledger))))
          (let ((next (mv-nth 1 (fn-prl-resident-shrink amount ledger))))
            (fn-prs-fundedp (fn-prl-nth 0 next) (fn-prl-baseline next) '(0 0 0 0 0)
                            (fn-prl-nth 1 next))))
  :subject fn-prl-resident-shrink
  :witness-lemma prgrowth-funding-witness
  :witness ((amount 200) (ledger *prgrowth-ledger*))
  :breaks ((funded ((amount 0) (ledger *prgrowth-unfunded*)) :lemma prgrowth-funding-without-funded))
  :mutations ((always-unfunded
               (:conclusion (let ((next (mv-nth 1 (fn-prl-resident-shrink amount ledger))))
                              (not (fn-prs-fundedp (fn-prl-nth 0 next) (fn-prl-baseline next) '(0 0 0 0 0)
                                                   (fn-prl-nth 1 next)))))
               ((amount 200) (ledger *prgrowth-ledger*))
               :fault "a shrink whose result is no longer funded"
               :lemma prgrowth-funding-mutant-witness)))

; ---------------------------------------------------------------------------
; Growth reserve (fn-prl-reserve-growth / fn-prl-convert-growth).  Ground
; ledger: register file 1, reserve 300 of the resident budget, then one
; interleaved read draw (admit, settle to cached, evict), then convert.
; This interleaving is the EVIDENCE for the cross-draw claim until
; PRL-ROW-SUM-INVARIANT lands; the theorem itself assumes charged covers the reserve.
(defconst *grr-l0* '((1000 0 2 1 10) (0 0 0 0 0) 0 nil (400 0 0 0 0)))
(defconst *grr-l1* (nth 1 (mv-list 2 (fn-prl-register *grr-l0* 1 '(0 0 1 0 0)))))
(defconst *grr-tok* (fn-prl-growth-token 0))
(defconst *grr-l2* (nth 2 (mv-list 3 (fn-prl-reserve-growth *grr-l1* 300))))
(defconst *grr-rtok* (nth 1 (mv-list 3 (fn-prl-admit *grr-l2* 5 1 0 10 0 '(50 0 0 1 1) '(50 0 0 1 0)))))
(defconst *grr-l3* (nth 2 (mv-list 3 (fn-prl-admit *grr-l2* 5 1 0 10 0 '(50 0 0 1 1) '(50 0 0 1 0)))))
(defconst *grr-l4* (nth 1 (mv-list 2 (fn-prl-settle *grr-l3* *grr-rtok* t))))
(defconst *grr-l5* (nth 1 (mv-list 2 (fn-prl-evict *grr-l4* *grr-rtok*))))
(assert-event
 (and (equal (nth 0 (mv-list 3 (fn-prl-reserve-growth *grr-l1* 300))) :admitted)
      (equal *grr-tok* (nth 1 (mv-list 3 (fn-prl-reserve-growth *grr-l1* 300))))
      (equal (nth 0 (mv-list 3 (fn-prl-admit *grr-l2* 5 1 0 10 0 '(50 0 0 1 1) '(50 0 0 1 0)))) :admitted)
      (equal (nth 0 (mv-list 2 (fn-prl-settle *grr-l3* *grr-rtok* t))) :settled)
      (equal (nth 0 (mv-list 2 (fn-prl-evict *grr-l4* *grr-rtok*))) :evicted)
      (equal (fn-prl-binding *grr-tok* (fn-prl-nth 3 *grr-l5*))
             (cons *grr-tok* (list '(300 0 0 0 0) :cached nil)))
      (equal (nth 0 (mv-list 2 (fn-prl-convert-growth *grr-l5* *grr-tok* 300))) :protected-growth-admitted)
      (equal (fn-prl-nth 0 (nth 1 (mv-list 2 (fn-prl-convert-growth *grr-l5* *grr-tok* 300))))
             '(700 0 2 1 10))))
; Refused reserve leaves the ledger unchanged (700 > 1000-400-0 free).
(assert-event
 (equal (mv-list 3 (fn-prl-reserve-growth *grr-l1* 700))
        (list :read-resources-unavailable nil *grr-l1*)))

(defconst *grr-tok99* (fn-prl-growth-token 99))
; hypothesis-break ledgers
(defconst *grr-neg*
  (fn-prl-build '(1000 0 2 1 10) '(100 0 0 0 0) 1
                (list (cons *grr-tok* (list '(-1 0 0 0 0) :cached nil))) '(400 0 0 0 0)))
(defconst *grr-thin*
  (fn-prl-build '(1000 0 2 1 10) '(100 0 0 0 0) 1
                (list (cons *grr-tok* (list '(700 0 0 0 0) :cached nil))) '(400 0 0 0 0)))
(defconst *grr-over*
  (fn-prl-build '(1000 0 2 1 10) '(2000 0 0 0 0) 1
                (list (cons *grr-tok* (list '(300 0 0 0 0) :cached nil))) '(400 0 0 0 0)))

(defteeth fn-prl-convert-growth-when-charged-covers-the-reserve
  :claim (((amount (natp amount))
           (bound (equal (fn-prl-binding token (fn-prl-nth 3 ledger))
                         (cons token (list (list amount 0 0 0 0) :cached nil))))
           (covers (<= amount (fn-prl-nth 0 (fn-prl-nth 1 ledger))))
           (funded (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                                   '(0 0 0 0 0) (fn-prl-nth 1 ledger))))
          (and (equal (mv-nth 0 (fn-prl-convert-growth ledger token amount))
                      :protected-growth-admitted)
               (let ((next (mv-nth 1 (fn-prl-convert-growth ledger token amount))))
                 (fn-prs-fundedp (fn-prl-nth 0 next) (fn-prl-baseline next)
                                 '(0 0 0 0 0) (fn-prl-nth 1 next)))))
  :subject fn-prl-convert-growth
  :witness ((amount 300) (token *grr-tok*) (ledger *grr-l5*))
  :breaks ((amount ((amount -1) (token *grr-tok*) (ledger *grr-neg*)))
           (bound ((amount 300) (token *grr-tok99*) (ledger *grr-l5*)))
           (covers ((amount 700) (token *grr-tok*) (ledger *grr-thin*)))
           (funded ((amount 300) (token *grr-tok*) (ledger *grr-over*))))
  :mutations ((answers-stale
               (:conclusion (equal (mv-nth 0 (fn-prl-convert-growth ledger token amount)) :stale))
               ((amount 300) (token *grr-tok*) (ledger *grr-l5*))
               :fault "a conversion that treats the live reserve row as stale")))

(defteeth fn-prl-evict-keeps-other-bindings
  :claim (((distinct (not (equal token other))))
          (equal (fn-prl-binding token (fn-prl-nth 3 (mv-nth 1 (fn-prl-evict ledger other))))
                 (fn-prl-binding token (fn-prl-nth 3 ledger))))
  :subject fn-prl-evict
  :witness ((token *grr-tok*) (other *grr-rtok*) (ledger *grr-l4*))
  :breaks ((distinct ((token *grr-tok*) (other *grr-tok*) (ledger *grr-l4*))))
  :mutations ((unbinds-reserve
               (:conclusion (equal (fn-prl-binding token (fn-prl-nth 3 (mv-nth 1 (fn-prl-evict ledger other))))
                                   nil))
               ((token *grr-tok*) (other *grr-rtok*) (ledger *grr-l4*))
               :fault "an eviction that drops every other holder's row")))

(defteeth-check)
