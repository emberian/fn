(in-package "ACL2")
(include-book "../../books/account-adoption-turn-return")
; Synthetic UNFUNDED actual algebra. No owner/ATS/last-alias authority claim.
(defconst *fn-act-return-original*
 '(:account-turn-reservation :original-ledger :proposed-ledger :resources 2 17))
(defconst *fn-act-return-current*
 (fn-act-promotion-carry *fn-act-return-original*
  (fn-act-row '(:account-preparation-turn 7 3 4) :promoted
              '(10 0 0 0 1) :candidate-step :source :old-request :old-job
              '(:new-request :new-job :yield)
              '(:account-turn-promotion :before :after (20 0 0 0 0)))))
(defconst *fn-act-return-ledger*
 (fn-prl-build '(200 0 0 0 100) '(15 0 0 0 3) 11 :binding-root '(40 0 0 0 0)))
(assert-event
 (mv-let (word current ledger)
  (fn-act-return-proposal '(:account-preparation-turn 7 3 4)
                         *fn-act-return-current* *fn-act-return-ledger*)
  (and (eq word :account-turn-settling)
       (equal ledger (fn-prl-build '(200 0 0 0 100) '(5 0 0 0 3) 11
                                  :binding-root '(40 0 0 0 0)))
       (equal current
        (fn-act-row '(:account-preparation-turn 7 3 4) :uncertain
                    '(10 0 0 0 1) :candidate-step :source :old-request :old-job
                    '(:new-request :new-job :yield)
                    (list :account-turn-settlement *fn-act-return-ledger* ledger
                          (fn-cp-nth 9 *fn-act-return-current*)))))))
; Corrupted remaining claim cannot hide under NFIX or debit another actor.
(assert-event
 (mv-let (word current ledger)
  (fn-act-return-proposal '(:account-preparation-turn 7 3 4)
   *fn-act-return-current*
   (fn-prl-build '(200 0 0 0 100) '(9 0 0 0 3) 11 :binding-root '(40 0 0 0 0)))
  (and (eq word :account-return-refused) (equal current *fn-act-return-current*)
       (equal ledger (fn-prl-build '(200 0 0 0 100) '(9 0 0 0 3) 11
                                  :binding-root '(40 0 0 0 0))))))
; Stale identity refuses the complete effect, while all original roots remain.
(assert-event
 (mv-let (word current ledger)
  (fn-act-return-proposal '(:account-preparation-turn 6 3 4)
                         *fn-act-return-current* *fn-act-return-ledger*)
  (and (eq word :account-return-refused) (equal current *fn-act-return-current*)
       (equal ledger *fn-act-return-ledger*))))
; Producer captures all four literal globals before the internal clear. This
; checks the fixed carrier's complete output, not last-alias authority.
(assert-event
 (mv-let (word current ledger)
  (fn-act-return-proposal '(:account-preparation-turn 7 3 4)
                         *fn-act-return-current* *fn-act-return-ledger*)
  (and (eq word :account-turn-settling)
       (equal
        (fn-act-settlement-carry '(:capture :ready :holder :outcome) current)
        (fn-act-row '(:account-preparation-turn 7 3 4) :uncertain
                    '(10 0 0 0 1) :candidate-step :source :old-request :old-job
                    '(:new-request :new-job :yield)
                    (list :account-turn-settlement *fn-act-return-ledger* ledger
                          (fn-cp-nth 9 *fn-act-return-current*)
                          '(:capture :ready :holder :outcome)))))))
