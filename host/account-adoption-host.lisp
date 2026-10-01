; Actual static/redeemed lifecycle. Native transports the enclosing issuer's
; real ATS receipt; it neither selects credentials nor supplies an authority.
(in-package "ACL2")
(include-book "account-adoption-turn-host")
(include-book "account-adoption-begin-source-host")
(include-book "account-adoption-operation-host")
(include-book "../books/account-adoption-result")
(include-book "../books/consumer-account-adoption-driver")

; Source evaluator executes in the enclosing paid gate, before constructors.
; Original result field5 is this whole operation's compiled BODY request bound,
; not a family subtotal or native price. ATS cleanup belongs the outer owner.
(defun fn-owner-account-adoption-prepay
 (operation slot nonce fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
                 :mode :program :guard t))
 (if (not (and (fn-ats-matchingp slot nonce fn-allocation-turn-slots fn-page-read-pool)
               (equal (fn-ats-kindsi slot fn-allocation-turn-slots) :owner-control)
               (eql (fn-ats-phasesi slot fn-allocation-turn-slots) 2)))
     (mv :account-turn-body-unavailable fn-allocation-turn-slots fn-page-read-pool)
 (mv-let (word resources)
  (fn-owner-account-operation-resources operation fn-page-read-pool state)
  (if (not (and (eq word :account-operation-resources-available)
                (fn-cado-widthp 8 resources)
                (eq (fn-cp-nth 0 resources) :account-adoption-resources)
                (eq (fn-cp-nth 1 resources) operation)
                (natp (fn-cp-nth 5 resources))))
      (mv :account-turn-resources-unavailable fn-allocation-turn-slots fn-page-read-pool)
   (fn-ats-prepay-body-internal slot nonce (fn-cp-nth 5 resources)
                               fn-allocation-turn-slots fn-page-read-pool)))))

(defun fn-owner-account-adoption-begin
 (config bindings entropy slot nonce fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
                 :mode :program :guard (boundp-global 'fn-owner state)))
 (if (or (fn-owner-account-adoption-request state)
         (fn-owner-account-adoption-job state))
     (mv :refused :account-input-busy fn-allocation-turn-slots fn-page-read-pool state)
  (mv-let (paid resources fn-allocation-turn-slots fn-page-read-pool)
   (fn-owner-account-adoption-begin-prepay config bindings entropy slot nonce
     fn-allocation-turn-slots fn-page-read-pool state)
   (if (not (eq paid :prepaid))
       (mv :unavailable paid fn-allocation-turn-slots fn-page-read-pool state)
    (mv-let (issued fn-page-read-pool state)
     (fn-owner-account-turn-admit-resources-internal :begin nil resources
       slot nonce fn-allocation-turn-slots fn-page-read-pool state)
     (if (not (and (eq issued :account-turn-reserved)
                   (fn-owner-account-turn-current-bodyp :begin nil slot nonce
                       fn-allocation-turn-slots fn-page-read-pool state)))
         (mv :unavailable issued fn-allocation-turn-slots fn-page-read-pool state)
      (mv-let (receipt-word token) (fn-owner-account-turn-receipt state)
       (declare (ignore receipt-word))
       (let* ((store (fn-owner-store state)) (cp (fn-sn-consumer store))
              (incarnation (fn-cp-nth 2 cp))
              (txid (fn-state-next-txid (fn-node-acceptance (fn-sn-node store))))
              (base (fn-owner-config state))
              (source (fn-cado-source-key token (fn-owner-canonical-epoch state)
                          (fn-cfg-generation base) incarnation txid))
              (candidate (fn-cp-authority-namespace incarnation txid))
              (redeemed (fn-cfg-accounts (fn-cfg-value base)))
              (request (fn-cado-request config bindings entropy base source candidate redeemed))
              (one (fn-cadd-begin config bindings candidate redeemed source 0))
              (job (and (eq (fn-cp-nth 0 one) :yield) (fn-cp-nth 1 one))))
        ; Save actual produced roots before either process-local installation.
        (mv-let (collected fn-page-read-pool state)
         (fn-owner-account-turn-produced (list request job one) fn-page-read-pool state)
         (if (not (eq collected :account-turn-promoted))
             (mv :recovery-required :account-turn-collection
                 fn-allocation-turn-slots fn-page-read-pool state)
          (let* ((state (fn-owner-account-adoption-request-install request state))
                 (state (fn-owner-account-adoption-job-install job state)))
           (mv (if job :yield (fn-cp-nth 0 one)) (if job nil (fn-cp-nth 1 one)) fn-allocation-turn-slots fn-page-read-pool state)))))))))))

)
(defun fn-owner-account-adoption-tick
 (slot nonce fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state)
                 :mode :program :guard (boundp-global 'fn-owner state)))
 (mv-let (source-word source incarnation txid) (fn-owner-account-adoption-source state)
  (declare (ignore txid))
  (let* ((job (fn-owner-account-adoption-job state))
         (phase (fn-cp-nth 1 job))
         (operation (if (eq phase :ready) :operation-select :candidate-step)))
   (cond
    ((not (eq source-word :source-current))
     (mv :refused :account-input-source-unavailable fn-allocation-turn-slots fn-page-read-pool state))
    ; A genuine durable typed C collector advances configuration generation.
    ; Its installed :done job retains the original input source for readout.
    ((eq phase :done)
     (mv :accepted nil fn-allocation-turn-slots fn-page-read-pool state))
    ((not (and (equal (fn-owner-canonical-epoch state) (fn-cp-nth 2 source))
               (equal (fn-cfg-generation (fn-owner-config state)) (fn-cp-nth 3 source))
               (fn-cp-idp (fn-cp-nth 2 (fn-sn-consumer (fn-owner-store state))))
               (equal incarnation (fn-cp-nth 2 (fn-sn-consumer (fn-owner-store state))))))
     (mv :refused :account-input-source-changed fn-allocation-turn-slots fn-page-read-pool state))
    ((eq phase :await-durable)
     (mv :refused :account-publication-pending fn-allocation-turn-slots fn-page-read-pool state))
    (t
     (mv-let (paid fn-allocation-turn-slots fn-page-read-pool)
      (fn-owner-account-adoption-prepay operation slot nonce fn-allocation-turn-slots fn-page-read-pool state)
      (if (not (eq paid :prepaid))
          (mv :unavailable paid fn-allocation-turn-slots fn-page-read-pool state)
       (mv-let (issued fn-page-read-pool state)
        (fn-owner-account-turn-admit operation source slot nonce fn-allocation-turn-slots fn-page-read-pool state)
        (if (not (and (eq issued :account-turn-reserved)
                      (fn-owner-account-turn-current-bodyp operation source slot nonce
                          fn-allocation-turn-slots fn-page-read-pool state)))
            (mv :unavailable issued fn-allocation-turn-slots fn-page-read-pool state)
         (if (eq phase :ready)
             (fn-owner-account-adoption-operation-select slot nonce fn-allocation-turn-slots fn-page-read-pool state)
          (let* ((row (and (eq phase :redeemed) (car (fn-cp-nth 6 job))))
                 (name (fn-cfg-row-b row))
                 ; Existing credential grammar, not a stored-name ceiling.
                 ; Rows which cannot be valid credentials are skipped without
                 ; materializing their oversized name/verifier strings.
                 (bounded (and row (stringp name)
                               (<= (length name) *fn-auth-max-name-octets*)
                               (stringp (fn-cfg-row-c row))
                               (equal (length (fn-cfg-row-c row)) 224))))
             (let* ((credential (and bounded (fn-auth-account-cred row)))
                    (eligible (and row (equal (fn-cfg-row-n row) 1) (fn-auth-credp credential)))
                    (one (fn-cadd-tick job credential eligible))
                    (next (and (member-eq (fn-cp-nth 0 one) '(:yield :prepared)) (fn-cp-nth 1 one))))
              (mv-let (collected fn-page-read-pool state)
               (fn-owner-account-turn-produced (list (fn-owner-account-adoption-request state) next one)
                                               fn-page-read-pool state)
               (if (not (eq collected :account-turn-promoted))
                   (mv :recovery-required :account-turn-collection
                       fn-allocation-turn-slots fn-page-read-pool state)
                (let ((state (if next (fn-owner-account-adoption-job-install next state) state)))
                 (mv (if next :yield (fn-cp-nth 0 one)) (if next nil (fn-cp-nth 1 one)) fn-allocation-turn-slots fn-page-read-pool state))))))))))))))))

; Only the real durable collector can install phase :done. :ready remains
; pending and no status readout clears input/turn/operation/PRS custody.
(defun fn-owner-account-adoption-status (state)
 (declare (xargs :stobjs state :guard t))
 (let ((phase (fn-cp-nth 1 (fn-owner-account-adoption-job state))))
  (case phase (:done '(:accepted))
        ((:ready :static :redeemed :insert-static :insert-redeemed :await-durable) '(:yield))
        (otherwise '(:refused :account-adoption-unavailable)))))
