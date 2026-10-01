; Internal pooled once-selection. Native holds only the opaque operation ID.
; Source-only caller assembly: the typed account-turn producer and the actual
; installed allowance are independent prerequisites, never a supplied tuple.
(in-package "ACL2")
(include-book "owner-host")
(include-book "account-adoption-turn-host")
(include-book "../books/account-adoption-input-source")
(include-book "../books/consumer-account-operation-state")
(include-book "../books/consumer-account-transaction-driver")
(include-book "../books/owner-canonical-epoch")

; Fixed14: tag, opaque ID, issued input-source, SAME selection/job, captured
; epoch/C generation/E count, actual identity sequence/txid, authority ns/rev,
; original request alias, and SAME reserved selector turn receipt. This entry
; neither issues nor completes the enclosing actual :owner-control ticket.
(defun fn-owner-account-adoption-operation-select
       (slot nonce fn-allocation-turn-slots fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-page-read-pool state) :mode :program
                 :guard (boundp-global 'fn-owner state)))
 (let ((prior (fn-owner-account-adoption-operation state)))
  (if prior
      (mv :refused :account-publication-pending
          fn-allocation-turn-slots fn-page-read-pool state)
   (mv-let (source-word source incarnation expected-txid)
     (fn-owner-account-adoption-source state)
    (let* ((job (fn-owner-account-adoption-job state))
           (store (fn-owner-store state)) (cp (fn-sn-consumer store))
           (authority (fn-cp-nth 6 cp))
           (pending (fn-cp-nth 5 authority))
           (candidate (fn-cp-nth 3 job))
           (epoch (fn-owner-canonical-epoch state))
           (generation (fn-cfg-generation (fn-owner-config state)))
           (sequence (fn-sn-identity-next store))
           (txid (fn-state-next-txid (fn-node-acceptance (fn-sn-node store))))
           (field (fn-sf-records-field (fn-sn-files store)))
           ; Concrete snoc/based-suffix metadata only. The legacy raw-list
           ; count branch is refused before it could traverse the journal.
           (count (and (if (fn-sfr-basedp field)
                           (or (null (fn-sfr-suffix field))
                               (fn-sl-snoc-formp (fn-sfr-suffix field)))
                         (or (null field) (fn-sl-snoc-formp field)))
                       (fn-sf-records-count (fn-sn-files store)))))
     (cond
      ((not (and (eq source-word :source-current)
                  (eq (fn-cp-nth 1 job) :ready) (natp count)
                  (equal epoch (fn-cp-nth 2 source))
                  (equal generation (fn-cp-nth 3 source))
                  (fn-cp-idp incarnation)
                  (fn-cp-idp (fn-cp-nth 2 cp))
                  (equal incarnation (fn-cp-nth 2 cp))))
       (mv :refused :account-input-source-changed
           fn-allocation-turn-slots fn-page-read-pool state))
      ; An observed coordinate is not a reservation. Before the first durable
      ; begin, restart/rebind the uncommitted candidate on interference. A
      ; matching durable pending candidate instead retains its literal ID.
      ((and (null pending) (not (equal expected-txid txid)))
       (mv :refused :candidate-source-changed
           fn-allocation-turn-slots fn-page-read-pool state))
      (t
       (mv-let (receipt-word turn-token)
         (fn-owner-account-turn-receipt state)
        (if (not (and (eq receipt-word :account-turn-reserved)
                       (fn-owner-account-turn-current-bodyp
                        :operation-select source slot nonce
                        fn-allocation-turn-slots fn-page-read-pool state)))
            (mv :unavailable :account-operation-turn-unavailable
                fn-allocation-turn-slots fn-page-read-pool state)
         ; Tick already prepaid the actual operation census and reserved the
         ; typed turn. This consumes its current stored receipt/BODY relation;
         ; a positive status atom or a supplied source tuple is insufficient.
         (let* ((selection
                  (fn-catd-next job cp sequence txid (fn-sn-keyring-generation store)
                                generation count))
                (kind (fn-cp-nth 0 selection)))
          (if (not (member-eq kind '(:publish :configure)))
              (mv kind (fn-cp-nth 1 selection)
                  fn-allocation-turn-slots fn-page-read-pool state)
           (let* ((id (list :account-operation candidate sequence txid))
                  (holder
                   (list :account-adoption-operation id source selection job
                         epoch generation count sequence txid
                         (fn-cp-nth 3 authority) (fn-cp-nth 1 authority)
                         (fn-owner-account-adoption-request state) turn-token))
                  (state (f-put-global 'fn-owner-account-adoption-operation holder state)))
            (mv kind id fn-allocation-turn-slots fn-page-read-pool state)))))))))))))
