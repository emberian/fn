(in-package "ACL2")
(include-book "bp-receiver-invariants")
; codecs withdrew the record and cbor proof vocabularies at export (2026-09-19);
; this book reasons under them, so open them here, locally.
(local (in-theory (enable fn-record-record-vocabulary fn-record-codec-vocabulary fn-record-guard-vocabulary
                          fn-record-invariants-vocabulary fn-cbor-record-vocabulary
                          fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary)))
(local (in-theory (disable
 fn-bprr-nth
 fn-bprr-textp
 fn-bprr-configp
 fn-bprr-config
 fn-bprr-octetsp
 fn-bprr-recordp
 fn-bprr-decode-value
 fn-bprr-apply-record
 fn-bprr-replay-rest
 fn-bprr-replay
 fn-bpr-config-destination
 fn-bpr-config-policy-id
 fn-bpr-config-issuer
 fn-bpr-make-config
 fn-bpr-configp
 fn-bpr-context-work-id
 fn-bpr-context-msgid
 fn-bpr-context-subject
 fn-bpr-context-archive-id
 fn-bpr-context-peer-eid
 fn-bpr-context-policy-id
 fn-bpr-context-incarnation
 fn-bpr-context-auth-context
 fn-bpr-context-terms-id
 fn-bpr-context-request
 fn-bpr-make-context
 fn-bpr-contextp
 fn-bpr-context-listp
 fn-bpr-find-context
 fn-bpr-find-context-msgid
 fn-bpr-state-config
 fn-bpr-state-contexts
 fn-bpr-state-receipts
 fn-bpr-state-pending
 fn-bpr-make-state
 fn-bpr-receipt-entry-context
 fn-bpr-receipt-entry-receipt
 fn-bpr-make-receipt-entry
 fn-bpr-receipt-entryp
 fn-bpr-receipt-listp
 fn-bpr-statep
 fn-bpr-initial-state
 fn-bpr-context-from-request
 fn-bpr-store-record-acceptedp
 fn-bpr-request-acceptablep
 fn-bpr-accept-request
 fn-bpr-receipt-for
 fn-bpr-find-receipt
 fn-bpr-prepare-receipt
 fn-bpr-commit-receipt
 fn-bpr-receipt-adu
 fn-bpa-car
 fn-bpa-cdr
 fn-bpa-nth
 fn-bpa-request-work-id
 fn-bpa-request-subject
 fn-bpa-request-source-eid
 fn-bpa-request-destination-eid
 fn-bpa-request-policy-id
 fn-bpa-request-incarnation
 fn-bpa-request-auth-context
 fn-bpa-request-terms-id
 fn-bpa-request-article
 fn-bpa-make-request
 fn-bpa-receipt-id
 fn-bpa-receipt-work-id
 fn-bpa-receipt-subject
 fn-bpa-receipt-issuer
 fn-bpa-receipt-peer-eid
 fn-bpa-receipt-policy-id
 fn-bpa-receipt-incarnation
 fn-bpa-receipt-auth-context
 fn-bpa-receipt-terms-id
 fn-bpa-make-receipt
 fn-bpa-metadatap
 fn-bpa-requestp
 fn-bpa-receiptp
 fn-bpa-messagep
 fn-bpa-encode-fields
 fn-bpa-request-fields
 fn-bpa-receipt-fields
 fn-bpa-encode
 fn-bpa-read-fields
 fn-bpa-request-from-fields
 fn-bpa-receipt-from-fields
 fn-bpa-decode-fields
 fn-bpa-decode-after-magic
 fn-bpa-decode-candidate
 fn-bpa-decode-exact
 fn-bpa-result-okp
 fn-bpa-result-message
 fn-bpa-byte-field-listp
 fn-bpi-policy-destination
 fn-bpi-policy-endpoint
 fn-bpi-policy-group-map
 fn-bpi-policy-archive-id
 fn-bpi-policy-subject
 fn-bpi-policy-evidence
 fn-bpi-policy-charge
 fn-bpi-policy-id
 fn-bpi-policy-terms-id
 fn-bpi-policy-issuer-eid
 fn-bpi-make-policy
 fn-bpi-context-destination
 fn-bpi-context-source-eid
 fn-bpi-context-bundle-id
 fn-bpi-context-lifetime
 fn-bpi-make-context
 fn-bpi-group-map-entryp
 fn-bpi-group-mapp
 fn-bpi-map-values
 fn-bpi-find-group
 fn-bpi-map-one
 fn-bpi-map-groups
 fn-bpi-policy-p
 fn-bpi-context-p
 fn-bpi-policy-appliesp
 fn-bpi-record-for
 fn-bpi-ingress-prepare
 fn-bpi-result-kind
 fn-bpi-result-store
 fn-bpi-result-record
 fn-bpi-finish-prepared
 fn-bpi-node-record-committedp
 fn-bpi-durably-acceptedp
 fn-bpi-adu-durably-acceptedp
 fn-bpi-receipt-eligibility
 fn-sn-groups
 fn-sn-capacity
 fn-sn-files
 fn-sn-node
 fn-sn-make
 fn-sn-statep
 fn-sn-initial
 fn-sn-update
 fn-sn-pending-record
 fn-sn-record-bindsp
 fn-sn-prepare-node
 fn-sn-prepare
 fn-sn-find-record
 fn-sn-completion-record
 fn-sn-completion-enabledp
 fn-sn-finish
 fn-sn-file-step
 fn-sn-io
 fn-sn-crash
 fn-sn-recover
 fn-sn-fence-node
 fn-sn-resolve-node
 fn-sf-phase
 fn-sf-frontier
 fn-sf-frontier-candidate
 fn-sf-records
 fn-sf-record-candidate
 fn-sf-completion
 fn-sf-successes
 fn-sf-barriers
 fn-sf-make
 fn-sf-phasep
 fn-sf-fencedp
 fn-sf-pairp
 fn-sf-record-pair
 fn-sf-record-valuesp
 fn-sf-next-lower
 fn-sf-record-listp
 fn-sf-candidatep
 fn-sf-record-has-pairp
 fn-sf-success-listp
 fn-sf-frontier-phasep
 fn-sf-record-phasep
 fn-sf-completion-phasep
 fn-sf-phase-shapep
 fn-sf-statep
 fn-sf-initial-state
 fn-sf-start-frontier
 fn-sf-frontier-file-result
 fn-sf-frontier-replace-result
 fn-sf-frontier-dir-result
 fn-sf-replay-node
 fn-sf-history-recoverablep
 fn-sf-refuse-reservation
 fn-sf-prepare-record
 fn-sf-record-file-result
 fn-sf-prepublish-abort
 fn-sf-abort-completion
 fn-sf-record-link-result
 fn-sf-record-dir-result
 fn-sf-core-completion
 fn-sf-emit-success
 fn-sf-lose-success
 fn-sf-crash-choicep
 fn-sf-frontier-new-visiblep
 fn-sf-record-present-visiblep
 fn-sf-crash
 fn-sf-recover
 fn-sf-recovery-barrier
 fn-record-string-octets-aux
 fn-record-string-octets
 fn-record-octets-chars
 fn-record-octets-string
 fn-record-ascii-octetp
 fn-record-ascii-octet-listp
 fn-record-ascii-stringp
 fn-record-octet-stringp
 fn-record-nonempty-at-mostp
 fn-record-msgidp
 fn-record-payloadp
 fn-record-group-namep
 fn-record-no-duplicatesp
 fn-record-group-listp
 fn-record-groupsp
 fn-record-groups-validp
 fn-record-metadata-bytes-p
 fn-record-uint32p
 fn-record-sequence
 fn-record-txid
 fn-record-generation
 fn-record-msgid
 fn-record-payload
 fn-record-groups
 fn-record-obligation-id
 fn-record-content-subject
 fn-record-release-evidence
 fn-record-charge
 fn-record-make
 fn-record-p
 fn-record-encode-groups
 fn-record-parse-ok
 fn-record-parse-error
 fn-record-parse-okp
 fn-record-parse-value
 fn-record-parse-rest
 fn-record-result-okp
 fn-record-result-record
 fn-record-read-uint
 fn-record-read-bytes
 fn-record-parse-groups
 fn-record-decode-tail
 fn-record-decode-after-header)))

(local (in-theory (enable fn-bpa-car fn-bpa-cdr)))



(local (in-theory (disable fn-bprv-relationalp fn-bprv-entries-decidedp
 fn-bprv-contexts-backedp fn-bprv-context-backedp fn-bprv-entries-linkedp
 fn-bprv-entry-linkedp fn-bprv-pending-linkedp fn-bprv-entry-decidedp)))

; Extension/retry cannot overwrite an existing context or committed receipt.
(defthm fn-bprv-accept-preserves-existing-context
 (implies (consp (fn-bpr-find-context id (fn-bpr-state-contexts st)))
  (equal (fn-bpr-find-context id
           (fn-bpr-state-contexts (cadr (fn-bpr-accept-request st store record request authorized))))
         (fn-bpr-find-context id (fn-bpr-state-contexts st))))
 :hints (("Goal" :in-theory (enable fn-bpr-accept-request))))
(defthm fn-bprv-prepare-contexts-unchanged
 (equal (fn-bpr-state-contexts (fn-bpr-prepare-receipt st work-id receipt-id authorized))
        (fn-bpr-state-contexts st))
 :hints (("Goal" :in-theory (enable fn-bpr-prepare-receipt))))
(defthm fn-bprv-commit-contexts-unchanged
 (equal (fn-bpr-state-contexts (fn-bpr-commit-receipt st work-id receipt-id outcome))
        (fn-bpr-state-contexts st))
 :hints (("Goal" :in-theory (enable fn-bpr-commit-receipt))))
(defthm fn-bprv-find-receipt-cons
 (equal (fn-bpr-find-receipt id (cons entry entries))
        (if (equal id (fn-bpr-context-work-id (fn-bpr-receipt-entry-context entry)))
            entry (fn-bpr-find-receipt id entries)))
 :hints (("Goal" :expand ((fn-bpr-find-receipt id (cons entry entries))))))
(defthm fn-bprv-commit-preserves-existing-receipt
 (implies (and (fn-bprv-relationalp store st)
               (fn-bpr-find-receipt id (fn-bpr-state-receipts st)))
  (equal (fn-bpr-find-receipt id
           (fn-bpr-state-receipts (fn-bpr-commit-receipt st work-id receipt-id outcome)))
         (fn-bpr-find-receipt id (fn-bpr-state-receipts st))))
 :hints (("Goal" :in-theory (enable fn-bpr-commit-receipt fn-bprv-relationalp
                                   fn-bprv-pending-linkedp))))
(defthm fn-bprv-apply-record-preserves-existing-context
 (implies (consp (fn-bpr-find-context id (fn-bpr-state-contexts st)))
  (equal (fn-bpr-find-context id
           (fn-bpr-state-contexts (cadr (fn-bprr-apply-record st store r))))
         (fn-bpr-find-context id (fn-bpr-state-contexts st))))
 :hints (("Goal" :in-theory (enable fn-bprr-apply-record))))
(defthm fn-bprv-apply-record-preserves-existing-receipt
 (implies (and (fn-bprv-relationalp store st)
               (fn-bpr-find-receipt id (fn-bpr-state-receipts st)))
  (equal (fn-bpr-find-receipt id
           (fn-bpr-state-receipts (cadr (fn-bprr-apply-record st store r))))
         (fn-bpr-find-receipt id (fn-bpr-state-receipts st))))
 :hints (("Goal" :in-theory (enable fn-bprr-apply-record))))
(defthm fn-bprv-replay-rest-preserves-existing-context
 (implies (consp (fn-bpr-find-context id (fn-bpr-state-contexts st)))
  (equal (fn-bpr-find-context id
           (fn-bpr-state-contexts (cadr (fn-bprr-replay-rest st store records))))
         (fn-bpr-find-context id (fn-bpr-state-contexts st))))
 :hints (("Goal" :induct (fn-bprr-replay-rest st store records)
   :in-theory (enable fn-bprr-replay-rest))))
(defthm fn-bprv-replay-rest-preserves-existing-receipt
 (implies (and (fn-bprv-relationalp store st)
               (fn-bpr-find-receipt id (fn-bpr-state-receipts st)))
  (equal (fn-bpr-find-receipt id
           (fn-bpr-state-receipts (cadr (fn-bprr-replay-rest st store records))))
         (fn-bpr-find-receipt id (fn-bpr-state-receipts st))))
 :hints (("Goal" :induct (fn-bprr-replay-rest st store records)
   :in-theory (enable fn-bprr-replay-rest))))

(defthm fn-bprv-found-receipt-linked
 (implies (and (fn-bprv-entries-linkedp config contexts entries)
               (fn-bpr-find-receipt id entries))
          (fn-bprv-entry-linkedp config contexts (fn-bpr-find-receipt id entries)))
 :hints (("Goal" :induct (fn-bpr-find-receipt id entries)
   :in-theory (enable fn-bpr-find-receipt fn-bprv-entries-linkedp))))
(defthm fn-bprv-found-receipt-work-id
 (implies (fn-bpr-find-receipt id entries)
          (equal (fn-bpr-context-work-id
                   (fn-bpr-receipt-entry-context (fn-bpr-find-receipt id entries))) id))
 :hints (("Goal" :induct (fn-bpr-find-receipt id entries)
   :in-theory (enable fn-bpr-find-receipt))))
(defthm fn-bprv-found-receipt-decided
 (implies (and (fn-bprv-entries-decidedp entries journal)
               (fn-bpr-find-receipt id entries))
          (fn-bprv-entry-decidedp (fn-bpr-find-receipt id entries) journal))
 :hints (("Goal" :induct (fn-bpr-find-receipt id entries)
   :in-theory (enable fn-bpr-find-receipt fn-bprv-entries-decidedp))))
(defthm fn-bprv-found-receipt-member
 (implies (fn-bpr-find-receipt id entries)
          (member-equal (fn-bpr-find-receipt id entries) entries))
 :hints (("Goal" :induct (fn-bpr-find-receipt id entries)
   :in-theory (enable fn-bpr-find-receipt))))

; This is an output implication, not an output filter: the actual encoder and
; journal transitions are unchanged.
(defthm fn-bprv-output-has-linked-committed-entry
 (implies (and (fn-bprv-relationalp store st) (fn-bpr-receipt-adu st request))
  (let* ((context (fn-bpr-find-context (fn-bpa-request-work-id request) (fn-bpr-state-contexts st)))
         (entry (fn-bpr-find-receipt (fn-bpr-context-work-id context) (fn-bpr-state-receipts st))))
   (and (consp context)
        (equal request (fn-bpr-context-request context))
        (member-equal entry (fn-bpr-state-receipts st))
        (equal context (fn-bpr-receipt-entry-context entry))
        (fn-bprv-context-backedp store (fn-bpr-state-config st) context)
        (equal (fn-bpr-receipt-entry-receipt entry)
          (fn-bpr-receipt-for context (fn-bpr-state-config st)
            (fn-bpa-receipt-id (fn-bpr-receipt-entry-receipt entry))))
        (equal (fn-bpr-receipt-adu st request)
          (fn-bpa-encode (fn-bpr-receipt-entry-receipt entry))))))
 :rule-classes nil
 :hints (("Goal"
   :use ((:instance fn-bprv-found-receipt-linked
            (config (fn-bpr-state-config st)) (contexts (fn-bpr-state-contexts st))
            (entries (fn-bpr-state-receipts st)) (id (fn-bpa-request-work-id request))))
   :in-theory (e/d (fn-bpr-receipt-adu fn-bprv-relationalp fn-bprv-entry-linkedp)
                    (fn-bprv-found-receipt-linked)))))

(defthm fn-bprv-replayed-receipt-is-grounded
 (let* ((st (cadr (fn-bprr-replay store records)))
        (context (fn-bpr-find-context (fn-bpa-request-work-id request) (fn-bpr-state-contexts st)))
        (entry (fn-bpr-find-receipt (fn-bpr-context-work-id context) (fn-bpr-state-receipts st)))
        (record (fn-bprv-find-record store (fn-bpr-state-config st) context
                                     (fn-sf-records (fn-sn-files store)))))
  (implies (fn-bpr-receipt-adu st request)
   (and (fn-sn-statep store)
        (equal (fn-sf-phase (fn-sn-files store)) :ready)
        (fn-record-p record)
        (member-equal record (fn-sf-records (fn-sn-files store)))
        (fn-bpi-node-record-committedp (fn-sn-node store) record)
        (equal context (fn-bpr-context-from-request record request))
        (equal (fn-bpa-request-article request) (fn-record-payload record))
        (equal (fn-bpa-request-subject request) (fn-record-content-subject record))
        (member-equal entry (fn-bpr-state-receipts st))
        (fn-bprv-entry-decidedp entry records)
        (equal (fn-bpr-receipt-entry-receipt entry)
          (fn-bpr-receipt-for context (fn-bpr-state-config st)
           (fn-bpa-receipt-id (fn-bpr-receipt-entry-receipt entry))))
        (equal (fn-bpr-receipt-adu st request)
          (fn-bpa-encode (fn-bpr-receipt-entry-receipt entry))))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-bprv-output-has-linked-committed-entry
           (st (cadr (fn-bprr-replay store records))))
        (:instance fn-bprv-backed-context-has-actual-ready-record
           (config (fn-bpr-state-config (cadr (fn-bprr-replay store records))))
           (context (fn-bpr-find-context (fn-bpa-request-work-id request)
                      (fn-bpr-state-contexts (cadr (fn-bprr-replay store records))))))
        (:instance fn-bprv-replay-receipts-have-committed-decisions)
        (:instance fn-bprv-found-receipt-decided
           (id (fn-bpa-request-work-id request))
           (entries (fn-bpr-state-receipts (cadr (fn-bprr-replay store records))))
           (journal records)))
  :in-theory (e/d (fn-bpr-receipt-adu fn-bprv-relationalp)
    (fn-bprv-replay-receipts-have-committed-decisions fn-bprv-found-receipt-decided)))))
