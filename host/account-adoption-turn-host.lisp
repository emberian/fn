; Typed account actor. No canonical APR row or supplied vector is a receipt.
(in-package "ACL2")
(include-book "../books/account-adoption-turn-state")
(include-book "../books/account-adoption-turn-return")
(include-book "../books/page-read-counter-transaction")
(include-book "../books/allocation-turn-body-authority")
(include-book "../books/owner-canonical-epoch")
(include-book "owner-host")
(include-book "../books/runtime-operation-source")

; The original account resource result is selected by the installed compiler
; source getter. A family/request list subtotal is never lowered here.
; fn-owner-account-operation-resources is the runtime owner's additive seam.
; Only the composed phase2 producer calls this with its original result.
; No native endpoint accepts resources; the allocating body still validates
; its genuine enclosing ticket and registered CURRENT before constructor work.
(defun fn-owner-account-turn-admit-resources-internal
 (operation source resources slot nonce fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
                 :mode :program :guard (boundp-global 'fn-owner state)))
 (cond
  ((not (fn-ats-role-bodyp slot nonce :owner-control
                          fn-allocation-turn-slots fn-page-read-pool))
   (mv :account-turn-body-unavailable fn-page-read-pool state))
  ((fn-owner-account-turn-current state)
   (mv :account-turn-busy fn-page-read-pool state))
  ((not (and (fn-cado-widthp 8 resources)
             (eq (fn-cp-nth 0 resources) :account-adoption-resources)
             (eq operation (fn-cp-nth 1 resources))))
   (mv :account-turn-resources-unavailable fn-page-read-pool state))
  (t
     (mv-let (word row proposed)
       (fn-act-reserve (fn-owner-canonical-epoch state)
          (fn-cfg-generation (fn-owner-config state)) operation source
          (fn-owner-account-adoption-request state)
          (fn-owner-account-adoption-job state)
          (fn-cp-nth 2 resources) (fn-cp-nth 3 resources) nil
          (fn-owner-page-read-ledger fn-page-read-pool))
      (if (not (eq word :account-turn-reserved))
          (mv word fn-page-read-pool state)
       ; Persist ORIGINAL and proposed counter cut before the pool mutation.
       ; Raw escape cannot retry this nonce: CURRENT remains fenced.
       (let* ((intent (list :account-turn-reservation
                           (fn-owner-page-read-ledger fn-page-read-pool)
                           proposed resources slot nonce))
              (fenced (fn-act-row (fn-cp-nth 1 row) :uncertain
                         (fn-cp-nth 3 row) operation source
                         (fn-cp-nth 6 row) (fn-cp-nth 7 row) nil intent))
              (state (fn-owner-account-turn-keep fenced state)))
        (mv-let (published receipt fn-page-read-pool)
          (fn-owner-page-read-counter-begin proposed
             (fn-cp-nth 1 (fn-cp-nth 1 row)) :account-reserve fenced fn-page-read-pool)
         (if (not (eq published :counter-publishing))
             (mv :recovery-required fn-page-read-pool state)
          (let ((state (fn-owner-account-turn-keep
                        (fn-act-row (fn-cp-nth 1 row) :reserved
                          (fn-cp-nth 3 row) operation source
                          (fn-cp-nth 6 row) (fn-cp-nth 7 row) nil intent) state)))
           (mv-let (finished fn-page-read-pool)
             (fn-owner-page-read-counter-finish receipt fn-page-read-pool)
            (mv (if (eq finished :published) :account-turn-reserved :recovery-required)
                fn-page-read-pool state
)))))))))))

(defun fn-owner-account-turn-admit
 (operation source slot nonce fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
                 :mode :program :guard (boundp-global 'fn-owner state)))
 (mv-let (available resources)
  (fn-owner-account-operation-resources operation fn-page-read-pool state)
  (if (not (eq available :account-operation-resources-available))
      (mv :account-turn-resources-unavailable fn-page-read-pool state)
   (fn-owner-account-turn-admit-resources-internal operation source resources
      slot nonce fn-allocation-turn-slots fn-page-read-pool state))))

; Actual allocating callee must read this CURRENT receipt in the same BODY.
; Equality is fixed sourceKey6 only; request/job graphs are never compared.
(defun fn-owner-account-turn-current-bodyp
 (operation source slot nonce fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
                 :mode :program :guard t))
 (let* ((row (fn-owner-account-turn-current state))
        (intent (fn-cp-nth 9 row)))
  (and (fn-ats-role-bodyp slot nonce :owner-control
                         fn-allocation-turn-slots fn-page-read-pool)
       (fn-act-livep (fn-cp-nth 1 row) row)
       (eq (fn-cp-nth 2 row) :reserved)
       (eq (fn-cp-nth 4 row) operation)
       (if (eq operation :begin) (null source)
         (and (fn-cado-source-keyp source)
              (fn-cado-source-keyp (fn-cp-nth 5 row))
              (equal source (fn-cp-nth 5 row))))
       (eq (fn-cp-nth 0 intent) :account-turn-reservation)
       (equal slot (fn-cp-nth 4 intent))
       (equal nonce (fn-cp-nth 5 intent)))))

; Output is the actual callee result, saved BEFORE request/job publication.
; Full resource claim remains retained until the real last-alias return.
(defun fn-owner-account-turn-produced (output fn-page-read-pool state)
 (declare (xargs :stobjs (fn-page-read-pool state) :mode :program :guard t))
 (let* ((row (fn-owner-account-turn-current state))
        (token (fn-cp-nth 1 row)) (intent (fn-cp-nth 9 row))
        (resources (fn-cp-nth 3 intent)))
  (mv-let (word produced) (fn-act-produced token output row)
   (if (not (eq word :account-turn-produced))
       (mv :recovery-required fn-page-read-pool state)
    (let ((state (fn-owner-account-turn-keep produced state)))
     (mv-let (promotion promoting)
       (fn-act-promotion-intent token (fn-cp-nth 4 resources) produced
                                 (fn-owner-page-read-ledger fn-page-read-pool))
      (if (not (eq promotion :account-turn-promoting))
          (mv :recovery-required fn-page-read-pool state)
       (let* ((promoting (fn-act-promotion-carry intent promoting))
              (state (fn-owner-account-turn-keep promoting state)))
        (mv-let (published receipt fn-page-read-pool)
          (fn-owner-page-read-counter-begin
             (fn-cp-nth 2 (fn-cp-nth 9 promoting)) (fn-cp-nth 1 token)
             :account-promote promoting fn-page-read-pool)
         (if (not (eq published :counter-publishing))
             (mv :recovery-required fn-page-read-pool state)
          (mv-let (final next) (fn-act-promotion-published token promoting)
           (let ((state (fn-owner-account-turn-keep next state)))
            (mv-let (finished fn-page-read-pool)
              (fn-owner-page-read-counter-finish receipt fn-page-read-pool)
             (mv (if (eq finished :published) final :recovery-required)
                 fn-page-read-pool state)))))))))))))

; No lifetime release or ATS-finish is inferred from promotion, :yield,
; :accepted, or lexical return. The registered last-alias producer is missing.

)
