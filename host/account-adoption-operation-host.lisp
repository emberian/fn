; Internal pooled once-selection. Native holds only the opaque operation ID.
; Source-only caller assembly: the typed account-turn producer and the actual
; installed allowance are independent prerequisites, never a supplied tuple.
(in-package "ACL2")
(include-book "owner-host")
(include-book "account-preparation-admission-host")
(include-book "../books/account-adoption-input-source")
(include-book "../books/consumer-account-operation-state")
(include-book "../books/consumer-account-transaction-driver")
(include-book "../books/owner-canonical-epoch")

; Fixed13: tag, opaque ID, issued input-source, SAME selection/job, captured
; epoch/C generation/E count, actual identity sequence/txid, authority ns/rev,
; and the original registered request alias. No graph comparison or reselect.
(defun fn-owner-account-adoption-operation-select (fn-page-read-pool state)
 (declare (xargs :stobjs (fn-page-read-pool state) :mode :program
                 :guard (boundp-global 'fn-owner state)))
 (let ((prior (fn-owner-account-adoption-operation state)))
  (if prior
      (mv nil '(:refused :account-publication-pending) fn-page-read-pool state)
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
       (mv nil '(:refused :account-input-source-changed) fn-page-read-pool state))
      ; An observed coordinate is not a reservation. Before the first durable
      ; begin, restart/rebind the uncommitted candidate on interference. A
      ; matching durable pending candidate instead retains its literal ID.
      ((and (null pending) (not (equal expected-txid txid)))
       (mv nil '(:refused :candidate-source-changed) fn-page-read-pool state))
      (t
       (mv-let (admission fn-page-read-pool state)
         (fn-owner-account-preparation-admit source '(:account-operation-select)
                                            fn-page-read-pool state)
        (if (not (eq admission :account-preparation-admitted))
            (mv nil (list :unavailable admission) fn-page-read-pool state)
         ; This allocating decision is reached only from the actual typed
         ; operation issuer. The current diagnostic gate cannot reach it.
         (let* ((selection
                  (fn-catd-next job cp sequence txid (fn-sn-keyring-generation store)
                                generation count))
                (kind (fn-cp-nth 0 selection)))
          (if (not (member-eq kind '(:publish :configure)))
              (mv nil selection fn-page-read-pool state)
           (let* ((id (list :account-operation candidate sequence txid))
                  (holder
                   (list :account-adoption-operation id source selection job
                         epoch generation count sequence txid
                         (fn-cp-nth 3 authority) (fn-cp-nth 1 authority)
                         (fn-owner-account-adoption-request state)))
                  (state (f-put-global 'fn-owner-account-adoption-operation holder state)))
            (mv nil (list kind id) fn-page-read-pool state)))))))))))))
