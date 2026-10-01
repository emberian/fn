; The only caller is the actual owner cleanup epilogue BEFORE ATS finish,
; after its private core result/closure aliases have been dropped. Source-only:
; installed family/cleanup producer and whole native proof remain unqualified.
(in-package "ACL2")
(include-book "account-adoption-turn-host")
(include-book "../books/account-adoption-turn-return")

(defun fn-owner-account-turn-epilogue-token
 (slot nonce fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
                 :mode :program :guard t))
 (let* ((row (fn-owner-account-turn-current state))
        (token (fn-cp-nth 1 row))
        (reservation (fn-cp-nth 4 (fn-cp-nth 9 row))))
  (if (and (fn-ats-role-bodyp slot nonce :owner-control
                            fn-allocation-turn-slots fn-page-read-pool)
           (fn-act-livep token row) (eq (fn-cp-nth 2 row) :promoted)
           (eq (fn-cp-nth 0 reservation) :account-turn-reservation)
           (equal slot (fn-cp-nth 4 reservation))
           (equal nonce (fn-cp-nth 5 reservation)))
      (mv :account-return-current token)
    (mv :account-return-unavailable nil))))

; Token-only account identity; row/roots/amounts derive from CURRENT. A slot
; stamp is the real enclosing BODY association, not a joined observation.
(defun fn-owner-account-turn-return
 (token slot nonce fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
                 :mode :program :guard t))
 (mv-let (word issued)
   (fn-owner-account-turn-epilogue-token slot nonce fn-allocation-turn-slots
                                      fn-page-read-pool state)
  (if (not (and (eq word :account-return-current)
                 (fn-cado-receipt-coordinatep token)
                 (fn-cado-receipt-coordinatep issued) (equal token issued)))
      (mv :account-return-unavailable fn-page-read-pool state)
   (mv-let (ready settling proposed)
     (fn-act-return-proposal issued (fn-owner-account-turn-current state)
                                  (fn-owner-page-read-ledger fn-page-read-pool))
    (if (not (eq ready :account-turn-settling))
        (mv :recovery-required fn-page-read-pool state)
     (let ((state (fn-owner-account-turn-keep settling state)))
      (mv-let (published fn-page-read-pool)
        (fn-owner-page-read-counter-publish proposed fn-page-read-pool)
       (if (not (eq published :published))
           (mv :recovery-required fn-page-read-pool state)
        (let ((state (fn-owner-account-turn-keep nil state)))
         ; Current request/job/selected-operation are never cleared here.
         (mv :account-turn-returned fn-page-read-pool state)))))))))

)

; Named actual owner-epilogue entry, not an exported row/amount observer.
(defun fn-owner-account-turn-return-current
 (slot nonce fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
                 :mode :program :guard t))
 (if (not (fn-owner-account-turn-current state))
     (mv :account-turn-not-owned fn-page-read-pool state)
  (mv-let (word token)
    (fn-owner-account-turn-epilogue-token slot nonce fn-allocation-turn-slots
                                       fn-page-read-pool state)
   (if (not (eq word :account-return-current))
       (mv :account-return-pending fn-page-read-pool state)
    (fn-owner-account-turn-return token slot nonce fn-allocation-turn-slots
                                  fn-page-read-pool state)))))
