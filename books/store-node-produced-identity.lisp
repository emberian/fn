; Single produced ORIGINALctx decision constructor seam. No allocation authority.
(in-package "ACL2")
(include-book "store-node")
(include-book "replay-context-projection")
(include-book "replay-produced-size")

(defun fn-snpi-finish-from-core-context (s files record node ctx)
  (declare (xargs :guard t))
  (let* ((old-ctx (fn-sn-identity-context s))
         ; Known identical historical snapshots advance the journal cursor
         ; but do not roll back the active key generation or its table.
         (new-snapshotp (and (fn-stxk-p record)
                            (not (equal (fn-stxk-context-current-generation ctx)
                                        (fn-stxk-context-current-generation old-ctx)))))
         (new-verdicts (fn-replay-verdict-pairs
                        (fn-stxk-context-verdicts ctx)))
         (index (if (fn-hstxa-p record)
                    (fn-stx-index-add (fn-sn-index s)
                                      (fn-sn-composite-delta record
                                                             (fn-sn-keyring s)))
                  (fn-sn-index s))))
    (fn-sn-make-v6
     (fn-sn-groups s) (fn-sn-capacity s) files node
     ; Publish one snapshot only after its durable completion. Historical
     ; contexts and forks remain; no served recontext of prior article bytes.
     (if new-snapshotp
         (fn-ssk-apply-snapshot record (fn-sn-keyring s))
       (fn-sn-keyring s))
     index
     (if new-snapshotp
         (nfix (fn-stxk-keyring-generation record))
       (fn-sn-keyring-generation s))
     (append new-verdicts (fn-sn-verdicts s))
     (fn-stxk-context-snapshots ctx) (fn-stxk-context-next ctx)
     (fn-sn-config-history s) (fn-sn-consumer s)
     (fn-sn-topic s) (fn-sn-event-index s))))


(defun fn-snpi-finish-produced (s files record node original fields snapshot-carry)
 (declare (xargs :guard t))
 (mv-let (checked next-fields status effect child sizes)
  (fn-ris-produced-step-with-effects original fields record snapshot-carry)
  (mv (fn-snpi-finish-from-core-context s files record node
        (fn-ripc-core-checked-context checked effect child))
      checked next-fields status effect child sizes)))

(defthm fn-snpi-constructor-is-actual-finish
 (equal (fn-snpi-finish-from-core-context s files record node
          (fn-replay-identity-step (fn-sn-identity-context s) record))
        (fn-sn-finish-identity s files record node))
 :hints (("Goal" :in-theory (enable fn-snpi-finish-from-core-context fn-sn-finish-identity))))

(defthm fn-snpi-one-original-decision-preserves-complete-core-result
 (implies (equal (fn-sn-identity-context s) (fn-ripc-without-prior-verdicts original))
  (equal (mv-nth 0 (fn-snpi-finish-produced s files record node original fields snapshot-carry))
         (fn-sn-finish-identity s files record node)))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-ripc-one-original-decision-is-the-core-decision (ctx original) (event record)))
  :in-theory (e/d (fn-snpi-finish-produced fn-ris-produced-step-with-effects)
    (fn-snpi-finish-from-core-context fn-sn-finish-identity
     fn-replay-identity-produced-effects fn-ripc-without-prior-verdicts
     fn-ripc-core-checked-context fn-replay-identity-step)))))

; The caller fetches CHECKED and RECORD from its actual CURRENT operation.
; This book does not turn a supplied old packet into an allocation capability.
(defun fn-snpi-prepare-from-checked (s event checked)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (or (fn-stxe-p event) (fn-stxk-p event) (fn-hstxa-p event))
           (eq (car (fn-cpe-projection-step
                     (fn-sn-consumer s) event (fn-sn-identity-next s))) :ok)
           (consp (fn-replay-apply-record (fn-sn-node s) event))
           (equal (fn-stxk-context-kind
                   checked)
                  :ok))
      (let ((files (fn-sf-prepare-record (fn-sn-files s) event
                                         (fn-sn-groups s) (fn-sn-capacity s))))
        (if (equal (fn-sf-phase files) :record-staged)
            (fn-sn-update s files (fn-sn-node s))
          s))
    s))

(defun fn-snpi-completion-from-checked (s record checked)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (and (mbe :logic (fn-sn-statep s) :exec t)
       (equal (fn-sf-phase (fn-sn-files s)) :completing)
       (let ()
         (and (cond ((fn-store-retention-event-p record)
                (consp (fn-replay-apply-retention-event (fn-sn-node s) record)))
               ((or (fn-stxe-p record) (fn-stxk-p record) (fn-hstxa-p record))
                (and (consp (fn-replay-apply-record (fn-sn-node s) record))
                     (equal (fn-stxk-context-kind
                             checked) :ok)))
               ((or (fn-cpe-eventp record) (fn-th-topic-eventp record))
                (consp (fn-replay-apply-record (fn-sn-node s) record)))
               ; The row's context was decided under the generation in
               ; force at its intern; the finish consumes it only under the
               ; same one (fn-sn-set-keyring is refused outside :ready, so
               ; the generation cannot move inside a transaction).
               (t (and (fn-sn-record-bindsp (fn-sn-node s) record)
                       (equal (fn-hc-generation (fn-held-context record))
                              (fn-sn-keyring-generation s)))))))
       (equal (fn-sf-completion (fn-sn-files s))
              (fn-sf-record-pair record))))

(verify-guards fn-snpi-prepare-from-checked
 :hints (("Goal" :in-theory (e/d (fn-sn-statep)
  (fn-sf-statep fn-node-statep fn-record-p fn-held-p fn-hstxa-p
   fn-stxe-p fn-stxk-p fn-sn-record-bindsp)))))
(verify-guards fn-snpi-completion-from-checked
 :hints (("Goal" :in-theory (e/d (fn-sn-statep)
  (fn-sf-statep fn-node-statep fn-record-p fn-held-p fn-hstxa-p
   fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-sn-record-bindsp)))))

(defthm fn-snpi-prepare-checked-result-is-actual-prepare
 (implies (equal checked (fn-replay-identity-step (fn-sn-identity-context s) event))
  (equal (fn-snpi-prepare-from-checked s event checked) (fn-sn-prepare-identity s event)))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-snpi-prepare-from-checked fn-sn-prepare-identity)
  (fn-sn-statep fn-sf-prepare-record fn-sn-update fn-replay-identity-step
   fn-sn-identity-context fn-cpe-projection-step fn-replay-apply-record
   fn-stxe-p fn-stxk-p fn-hstxa-p)))))
(defthm fn-snpi-current-record-checked-result-is-actual-completion
 (implies (and (equal record (fn-sn-completion-record s))
               (equal checked (fn-replay-identity-step (fn-sn-identity-context s) record)))
  (equal (fn-snpi-completion-from-checked s record checked) (fn-sn-completion-core-enabledp s)))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-snpi-completion-from-checked fn-sn-completion-core-enabledp)
  (fn-sn-statep fn-sn-completion-record fn-replay-identity-step fn-sn-identity-context
   fn-replay-apply-record fn-replay-apply-retention-event fn-sn-record-bindsp
   fn-record-p fn-held-p fn-hstxa-p fn-store-retention-event-p fn-stxe-p fn-stxk-p)))))
