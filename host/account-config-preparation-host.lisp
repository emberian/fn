; Actual typed C semantic preparation from the sole acquired writer lease.
; The enclosing account BODY pays before each allocating call. This leaf does
; not mint a ticket, interpret an atom as funds, or supply a native plan setter.
; High PROGRAM composition remains source-unadmitted. A saved full8 is not
; installation readiness: posting/view/canonical/source joins remain explicit.
(in-package "ACL2")
(include-book "account-config-source-host")
(include-book "../books/consumer-account-carries-state")
(include-book "../books/consumer-account-transaction-driver")
(include-book "../books/consumer-account-config-commit")
(include-book "../books/account-config-history-cursor")
(include-book "../books/account-config-generation-cursor")

; Fixed14: tag,id,turn,full8,record,base8,metadata,phase,history,
; group cursor,old generation,new generation,next node,StoreFields14. The captured base
; includes the literal old view/posting/obligation aliases throughout yields.
(defun fn-owner-account-config-preparation-state (state)
 (declare (xargs :stobjs state :guard t))
 (and (boundp-global 'fn-owner-account-config-preparation state)
      (f-get-global 'fn-owner-account-config-preparation state)))

(defun fn-owner-account-config-preparation-step (state)
 (declare (xargs :stobjs state :mode :program :guard (boundp-global 'fn-owner state)))
 (let* ((lease (fn-owner-account-config-source state))
        (holder (fn-owner-account-adoption-operation state))
        (prior (fn-owner-account-config-preparation-state state)))
  (cond
   ((not (eq (fn-owner-history-config-writer-gate state) :config-writer-current))
    (mv :account-config-source-changed state))
   ((and prior (eq (fn-prl-nth 0 prior) :account-config-preparation-intent))
    ; Process escape during the ONE account decision never reruns it.
    (mv :recovery-required state))
   ((not prior)
    (let* ((base (and (boundp-global 'fn-owner-history-config-base state)
                     (f-get-global 'fn-owner-history-config-base state)))
           (store (fn-prl-nth 2 base))
           (metadata (fn-owner-account-carries-read state))
           (record (fn-prl-nth 8 lease))
           (job (fn-prl-nth 4 holder)))
     (if (not (and (fn-apr-widthp 8 base)
                   (eq (fn-prl-nth 0 base) :history-config-base)
                   (equal (fn-prl-nth 1 base) (fn-prl-nth 1 lease))
                   (fn-apr-widthp 5 metadata)
                   (eq (fn-prl-nth 0 metadata) :account-carries)))
         (mv :account-config-base-unavailable state)
      (let* ((state (f-put-global 'fn-owner-account-config-preparation
                      (list :account-config-preparation-intent
                            (fn-prl-nth 1 lease) (fn-prl-nth 2 lease)) state))
             (full (fn-acj-commit (fn-sn-consumer store) metadata
                     (fn-catd-preparation job) record
                     (fn-cp-nth 11 job) (fn-prl-nth 5 lease))))
       (if (not (eq (fn-cp-nth 0 full) :ok))
           ; The durable C has not been written. Retain the selected holder
           ; and original input; a refusal cannot authorize a changed retry.
           (let ((state (f-put-global 'fn-owner-account-config-preparation
                          (list :account-config-preparation-refused
                                (fn-prl-nth 1 lease) (fn-prl-nth 2 lease) full) state)))
            (mv :refused state))
        (let* ((cfg (fn-cp-nth 6 full))
               (next-node (fn-replay-advance-txid (fn-sn-node store)
                                                 (fn-cfg-record-txid record)))
               (state (f-put-global 'fn-owner-account-config-preparation
                       (list :account-config-preparation (fn-prl-nth 1 lease)
                             (fn-prl-nth 2 lease) full record base metadata
                             :groups (fn-ach-begin (fn-sn-config-history store) record)
                             (fn-acg-begin (fn-cfg-groups (fn-cfg-value cfg))
                                           (fn-cfg-generation (fn-prl-nth 3 base))
                                           (fn-cfg-generation cfg))
                             (fn-cfg-generation (fn-prl-nth 3 base))
                             (fn-cfg-generation cfg) next-node nil) state)))
         (mv :yield state)))))))
   ((eq (fn-prl-nth 0 prior) :account-config-preparation-refused)
    (mv :refused state))
   ((not (and (fn-apr-widthp 14 prior)
               (eq (fn-prl-nth 0 prior) :account-config-preparation)
               (equal (fn-prl-nth 1 prior) (fn-prl-nth 1 lease))
               (fn-cado-receipt-coordinatep (fn-prl-nth 2 prior))
               (equal (fn-prl-nth 2 prior) (fn-prl-nth 2 lease))))
    (mv :recovery-required state))
   ((eq (fn-prl-nth 7 prior) :groups)
    (let* ((one (fn-acg-tick (fn-prl-nth 9 prior)))
           (word (fn-cp-nth 0 one)))
     (if (eq word :rebuild)
         ; A future generation transition needs the general bounded
         ; posting/view rebuild. Never reuse a now-different old table.
         (mv :configuration-generation-rebuild-required state)
      (if (not (member-eq word '(:yield :ready)))
          (mv :configuration-generation-phase-unavailable state)
       (let* ((next (update-nth 9 (fn-cp-nth 1 one) prior))
              (next (if (eq word :ready) (update-nth 7 :history next) next))
              (state (f-put-global 'fn-owner-account-config-preparation next state)))
        (mv :yield state))))))
   ((eq (fn-prl-nth 7 prior) :history)
    (let* ((one (fn-ach-tick (fn-prl-nth 8 prior)))
           (next (update-nth 8 (fn-cp-nth 1 one) prior))
           (next (if (eq (fn-cp-nth 0 one) :ready)
                     (update-nth 7 :store-fields next) next))
           (state (f-put-global 'fn-owner-account-config-preparation next state)))
     (mv :yield state)))
   ((eq (fn-prl-nth 7 prior) :store-fields-intent)
    (mv :recovery-required state))
   ((eq (fn-prl-nth 7 prior) :store-fields)
    (let* ((base-store (fn-prl-nth 2 (fn-prl-nth 5 prior)))
           (state (f-put-global 'fn-owner-account-config-preparation
                    (update-nth 7 :store-fields-intent prior) state))
           ; No physical E append, identity decision, account decision or
           ; historical refresh occurs here. Every changed child is from
           ; the once-produced C decision or actual completed history cursor.
           (fields (list :history-store-fields
                     (fn-sn-groups base-store) (fn-sn-capacity base-store)
                     (fn-prl-nth 12 prior)
                     (fn-sn-keyring base-store) (fn-sn-index base-store)
                     (fn-sn-keyring-generation base-store)
                     (fn-sn-verdicts base-store) (fn-sn-keyring-snapshots base-store)
                     (fn-sn-identity-next base-store)
                     (fn-cp-nth 4 (fn-prl-nth 8 prior))
                     (fn-cp-nth 1 (fn-prl-nth 3 prior))
                     (fn-sn-topic base-store) (fn-sn-event-index base-store)))
           (next (update-nth 13 fields (update-nth 7 :semantic-joins prior)))
           (state (f-put-global 'fn-owner-account-config-preparation next state)))
     (mv :configuration-semantic-pending state)))
   (t (mv :configuration-semantic-pending state)))))

; Actual fixed-field output from the registered continuation, not an input
; tuple or freshly recomputed semantic result. Installation still requires
; the complete plan/canonical/source producer returned by the MV7 boundary.
(defun fn-owner-account-config-store-fields-result (state)
 (declare (xargs :stobjs state :mode :program :guard (boundp-global 'fn-owner state)))
 (let ((s (fn-owner-account-config-preparation-state state)))
  (if (and (eq (fn-owner-history-config-writer-gate state) :config-writer-current)
           (fn-apr-widthp 14 s) (eq (fn-prl-nth 0 s) :account-config-preparation)
           (eq (fn-prl-nth 7 s) :semantic-joins))
      (mv :config-store-fields (fn-prl-nth 13 s) (fn-prl-nth 3 s))
    (mv :account-config-store-fields-unavailable nil nil))))

; MV7 frozen for actual journal begin. Pending readout retains the actual
; decision but has NIL plan/canonical/obligation/new-source, so it cannot be
; mistaken for a fixed installer grant. The final semantic producer must
; establish posting/view law and SAME next source/canonical tuple first.
(defun fn-owner-account-config-preparation-result (state)
 (declare (xargs :stobjs state :mode :program :guard (boundp-global 'fn-owner state)))
 (let ((s (fn-owner-account-config-preparation-state state)))
  (if (and (eq (fn-owner-history-config-writer-gate state) :config-writer-current)
           (fn-apr-widthp 14 s) (eq (fn-prl-nth 0 s) :account-config-preparation))
      (mv :configuration-semantic-pending (fn-prl-nth 4 s) (fn-prl-nth 3 s)
          nil nil nil nil)
    (mv :account-config-source-unavailable nil nil nil nil nil nil))))
