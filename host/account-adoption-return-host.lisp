; The only caller is the actual owner cleanup epilogue BEFORE ATS finish,
; after its private core result/closure aliases have been dropped. Source-only:
; installed family/cleanup producer and whole native proof remain unqualified.
(in-package "ACL2")
(include-book "account-adoption-turn-host")
(include-book "account-config-continuation-host")
(include-book "../books/account-adoption-turn-return")
(include-book "account-durable-alias-clear-host")

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
     (let* ((operation (fn-cp-nth 4 settling))
            (aliases
             (and (eq operation :operation-select)
              (list (and (boundp-global 'fn-owner-history-account-capture state)
                         (f-get-global 'fn-owner-history-account-capture state))
                    (and (boundp-global 'fn-owner-history-account-state state)
                         (f-get-global 'fn-owner-history-account-state state))
                    (fn-owner-account-adoption-operation state)
                    (fn-owner-account-durable-outcome state))))
            (settling (fn-act-settlement-carry aliases settling))
            (state (fn-owner-account-turn-keep settling state)))
      (mv-let (published receipt fn-page-read-pool)
        (fn-owner-page-read-counter-begin proposed (fn-cp-nth 1 issued)
                                         :account-settle settling fn-page-read-pool)
       (if (not (eq published :counter-publishing))
           (mv :recovery-required fn-page-read-pool state)
        ; The recovery-mode pool continuation and CURRENT own the exact old
        ; aliases before this internal consumer clears their original globals.
        ; Request/next-job remain permanent U roots. Canonical APR is separate.
        (mv-let (cleared state)
         (if (eq operation :operation-select)
             (fn-owner-account-durable-alias-clear-internal
               issued receipt fn-page-read-pool state)
           (mv :account-aliases-cleared state))
         (if (not (eq cleared :account-aliases-cleared))
             (mv :recovery-required fn-page-read-pool state)
          (let ((state (fn-owner-account-turn-keep nil state)))
           (mv-let (finished fn-page-read-pool)
            (fn-owner-page-read-counter-finish receipt fn-page-read-pool)
            (mv (if (eq finished :published) :account-turn-returned :recovery-required)
                fn-page-read-pool state))))))))))))

)

; Named actual owner-epilogue entry, not an exported row/amount observer.
(defun fn-owner-account-turn-return-current
 (slot nonce fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
                 :mode :program :guard t))
 (if (not (fn-owner-account-turn-current state))
     ; CURRENT may already be cleared at a crash before CounterFinish. Its
     ; exact roots then remain in the recovery-mode pool continuation. NIL is
     ; not authority to finish this ticket or reinterpret that pending cut.
     (mv (if (and (eq (fn-prp-mode fn-page-read-pool) :served)
                  (member-eq (fn-prp-alloc-mode fn-page-read-pool) '(:active :draining)))
             :account-turn-not-owned :account-return-pending)
         fn-page-read-pool state)
  (if (eq (fn-cp-nth 0 (fn-cp-nth 3 (fn-owner-account-adoption-operation state))) :configure)
      (fn-owner-account-config-suspend-current slot nonce fn-allocation-turn-slots
                                              fn-page-read-pool state)
  (mv-let (word token)
    (fn-owner-account-turn-epilogue-token slot nonce fn-allocation-turn-slots
                                       fn-page-read-pool state)
   (if (not (eq word :account-return-current))
       (mv :account-return-pending fn-page-read-pool state)
    (fn-owner-account-turn-return token slot nonce fn-allocation-turn-slots
                                  fn-page-read-pool state)))))

)
