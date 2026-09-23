; Versioned diagnostic contract for auxiliary Store state after exact-history
; recovery.  A node checkpoint stores only the core node; the selected
; transaction pack and authoritative Store reopen preserve the other fields
; by replaying their exact event bytes in the original dense sequence.
(in-package "ACL2")
(include-book "store-node")
(include-book "checkpoint-compaction")

(defconst *fn-cpa-version* 1)
(defconst *fn-cpa-clone-fence-name*
  '(99 108 111 110 101 45 112 101 110 100 105 110 103 46 102 110 99 101))
(defconst *fn-cpa-clone-max-depth* 16)
(defconst *fn-cpa-clone-max-entries* 1000000)

(defun fn-cpa-clone-fence-read-bound () *fn-cpe-max-octets*)
(defun fn-cpa-clone-max-depth () *fn-cpa-clone-max-depth*)
(defun fn-cpa-clone-max-entries () *fn-cpa-clone-max-entries*)

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

; This constructor is used only by the saved-image integration fixture until
; the consumer interface has a public bootstrap policy.  It still derives all
; Store coordinates in ACL2 and admits only the first consumer bootstrap.
(defun fn-cpa-bootstrap-proposal (store history-id incarnation-id)
  (declare (xargs :guard t :verify-guards nil))
  (let ((sequence (fn-sn-identity-next store))
        (txid (fn-state-next-txid
               (fn-node-acceptance (fn-sn-node store)))))
    (cond ((fn-sn-consumer store) (list :refused :already-bootstrapped))
          ((or (not (fn-cp-idp history-id))
               (not (fn-cp-idp incarnation-id)))
           (list :refused :identity))
          ((or (not (fn-cp-uintp sequence))
               (equal sequence *fn-cbor-max-uint*)
               (not (fn-cp-uintp txid)))
           (list :refused :coordinates))
          (t (list :ok (fn-cpe-make
                        sequence txid txid
                        (list :bootstrap history-id incarnation-id)))))))

(defun fn-cpa-last-record (records)
  (declare (xargs :measure (len records)))
  (if (consp records)
      (if (consp (cdr records))
          (fn-cpa-last-record (cdr records))
        (car records))
    nil))

; The fence contains the canonical v1 consumer rollover event itself.  It is
; never an alternative journal: :completed requires that exact event at the
; end of the authoritative completed history.  The host may remove the fence
; only after a new observed reopen returns :completed.
(defun fn-cpa-clone-phase (store marker-event)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((op (fn-cpe-operation marker-event))
         (fresh-id (fn-cp-nth 1 op))
         (consumer (fn-sn-consumer store)))
    (cond ((or (not (fn-cpe-eventp marker-event))
               (not (equal (fn-cp-nth 0 op) :rollover))
               (not (fn-cp-statep consumer)))
           :refused)
          ((equal (fn-cp-nth 2 consumer) fresh-id)
           (if (and (equal marker-event
                           (fn-cpa-last-record
                            (fn-sf-records (fn-sn-files store))))
                    (equal (fn-sn-identity-next store)
                           (1+ (fn-cpe-sequence marker-event))))
               :completed
             :refused))
          ((equal (fn-cpa-rollover-proposal store fresh-id)
                  (list :ok marker-event))
           :pending)
          (t :refused))))

(defun fn-cpa-clone-phase-of-octets (store marker-octets)
  (declare (xargs :guard t :verify-guards nil))
  (let ((decoded (fn-cpe-decode-exact marker-octets)))
    (if (equal (car decoded) :ok)
        (fn-cpa-clone-phase store (fn-cp-nth 1 decoded))
      :refused)))
