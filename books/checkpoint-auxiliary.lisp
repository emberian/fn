; Versioned diagnostic contract for auxiliary Store state after exact-history
; recovery.  A node checkpoint stores only the core node; the selected
; transaction pack and authoritative Store reopen preserve the other fields
; by replaying their exact event bytes in the original dense sequence.
(in-package "ACL2")
(include-book "store-node")
(include-book "checkpoint-compaction")

(defconst *fn-cpa-version* 1)

; The full replay is deliberately confined to recovery, never a served path.
; Returning :bad keeps a partial or malformed consumer/identity history from
; being presented as a complete checkpoint comparison.
(defun fn-cpa-auxiliary-of-history (records)
  (declare (xargs :guard t :verify-guards nil))
  (let ((identity (fn-replay-identity records))
        (consumer (fn-cpe-projection-replay nil records 0)))
    (if (and (equal (fn-stxk-context-kind identity) :ok)
             (equal (car consumer) :ok))
        (list :ok *fn-cpa-version*
              (fn-replay-verdict-pairs (fn-stxk-context-verdicts identity))
              (fn-stxk-context-snapshots identity)
              (fn-stxk-context-next identity)
              (fn-cp-nth 1 consumer))
      (list :bad :history))))

(defun fn-cpa-store-auxiliary-agrees (store)
  (declare (xargs :guard t :verify-guards nil))
  (let ((expected
         (fn-cpa-auxiliary-of-history (fn-sf-records (fn-sn-files store)))))
    (if (and (equal (car expected) :ok)
             (equal (nth 1 expected) *fn-cpa-version*)
             (equal (nth 2 expected) (fn-sn-verdicts store))
             (equal (nth 3 expected) (fn-sn-keyring-snapshots store))
             (equal (nth 4 expected) (fn-sn-identity-next store))
             (equal (nth 5 expected) (fn-sn-consumer store)))
        (list :ok *fn-cpa-version*)
      (list :mismatch :auxiliary-state))))

; A cold writable clone must publish this event before accepting a consumer
; command.  The caller supplies only entropy for the new incarnation; the
; dense sequence and allocator coordinates come from the recovered Store.
; This is a proposal, not evidence of a completed durable publication.
(defun fn-cpa-rollover-proposal (store fresh-id)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((consumer (fn-sn-consumer store))
         (sequence (fn-sn-identity-next store))
         (txid (fn-state-next-txid
                (fn-node-acceptance (fn-sn-node store)))))
    (cond ((not (fn-cp-statep consumer)) (list :refused :unbootstrapped))
          ((not (fn-cp-idp fresh-id)) (list :refused :incarnation-id))
          ((equal fresh-id (fn-cp-nth 2 consumer))
           (list :refused :same-incarnation))
          ((or (not (fn-cp-uintp sequence))
               (equal sequence *fn-cbor-max-uint*)
               (not (fn-cp-uintp txid)))
           (list :refused :coordinates))
          (t (list :ok (fn-cpe-make sequence txid txid
                                    (list :rollover fresh-id)))))))
