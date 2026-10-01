; INTERNAL account return algebra. An ordinary lexical return or ATS :left
; never calls this as authority; the actual owner epilogue is its producer.
(in-package "ACL2")
(include-book "account-adoption-turn")

; Preserve the real reservation/ATS association through the existing promoter.
; ORIGINAL is selected from CURRENT by the actual producer, not native input.
(defun fn-act-promotion-carry (original promoting)
 (declare (xargs :guard t))
 (let ((intent (fn-cp-nth 9 promoting)))
  (fn-act-row (fn-cp-nth 1 promoting) (fn-cp-nth 2 promoting)
              (fn-cp-nth 3 promoting) (fn-cp-nth 4 promoting)
              (fn-cp-nth 5 promoting) (fn-cp-nth 6 promoting)
              (fn-cp-nth 7 promoting) (fn-cp-nth 8 promoting)
              (list (fn-cp-nth 0 intent) (fn-cp-nth 1 intent)
                    (fn-cp-nth 2 intent) (fn-cp-nth 3 intent) original))))

; Temporary remaining claim is released only from the actual current C.
; The original promoted reusable amount remains U, even when aliases share.
; A corrupt carry cannot exploit clamped subtraction to refund another actor.
(defun fn-act-return-proposal (token current ledger)
 (declare (xargs :guard t))
 (let ((remaining (fn-cp-nth 3 current)) (charged (fn-prl-nth 1 ledger)))
  (if (not (and (fn-act-livep token current)
                 (eq (fn-cp-nth 2 current) :promoted)
                 (fn-prs-vectorp remaining) (fn-prs-vectorp charged)
                 (true-listp remaining) (true-listp charged)
                 (fn-prs-below remaining charged)))
      (mv :account-return-refused current ledger)
   (let ((proposed
          (fn-prl-build (fn-prl-nth 0 ledger)
                        (fn-prs-release-reusable charged remaining)
                        (fn-prl-nth 2 ledger) (fn-prl-nth 3 ledger)
                        (fn-prl-baseline ledger))))
    (mv :account-turn-settling
        (fn-act-row token :uncertain remaining (fn-cp-nth 4 current)
                    (fn-cp-nth 5 current) (fn-cp-nth 6 current)
                    (fn-cp-nth 7 current) (fn-cp-nth 8 current)
                    (list :account-turn-settlement ledger proposed
                          (fn-cp-nth 9 current)))
        proposed)))))
(in-theory (disable fn-act-promotion-carry fn-act-return-proposal))
