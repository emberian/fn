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
