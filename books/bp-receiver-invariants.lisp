(in-package "ACL2")
(include-book "bp-receiver-journal-invariants")
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
 fn-record-encode
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
 fn-record-decode-after-header
 fn-record-decode-exact)))

(local (in-theory (enable fn-bpa-car fn-bpa-cdr)))



(local (in-theory (disable fn-bprv-relationalp fn-bprv-entries-decidedp
 fn-bprv-contexts-backedp fn-bprv-context-backedp fn-bprv-entries-linkedp
 fn-bprv-entry-linkedp fn-bprv-pending-linkedp fn-bprv-entry-decidedp)))
(defthm fn-bprv-initial-relational
 (fn-bprv-relationalp store (fn-bpr-initial-state config))
 :hints (("Goal" :in-theory (enable fn-bpr-initial-state fn-bprv-relationalp
  fn-bprv-contexts-backedp fn-bprv-entries-linkedp fn-bprv-pending-linkedp
  fn-bpr-state-config fn-bpr-state-contexts fn-bpr-state-receipts fn-bpr-state-pending fn-bpr-make-state fn-bpa-nth))))
(defthm fn-bprv-initial-receipts-empty
 (equal (fn-bpr-state-receipts (fn-bpr-initial-state config)) nil)
 :hints (("Goal" :in-theory (enable fn-bpr-initial-state fn-bpr-state-receipts fn-bpr-make-state fn-bpa-nth))))
(defthm fn-bprv-journal-subset-weaken
 (implies (fn-bprv-journal-subsetp records journal)
          (fn-bprv-journal-subsetp records (cons r journal)))
 :hints (("Goal" :induct (fn-bprv-journal-subsetp records journal))))
(defthm fn-bprv-journal-subset-self
 (fn-bprv-journal-subsetp records records)
 :hints (("Goal" :induct (len records))))
(defthm fn-bprv-journal-subset-tail
 (fn-bprv-journal-subsetp (cdr records) records)
 :hints (("Goal" :cases ((consp records))
   :use ((:instance fn-bprv-journal-subset-weaken
      (records (cdr records)) (journal (cdr records)) (r (car records)))))))
(defthm fn-bprv-nil-relational
 (fn-bprv-relationalp store nil)
 :hints (("Goal" :in-theory (enable fn-bprv-relationalp fn-bprv-contexts-backedp
 fn-bprv-entries-linkedp fn-bprv-pending-linkedp fn-bpr-state-config
 fn-bpr-state-contexts fn-bpr-state-receipts fn-bpr-state-pending fn-bpa-nth))))
(defthm fn-bprv-replay-has-context-and-store-relation
 (fn-bprv-relationalp store (cadr (fn-bprr-replay store records)))
 :hints (("Goal" :in-theory (enable fn-bprr-replay))))
(defthm fn-bprv-empty-receipts-decided
 (fn-bprv-entries-decidedp nil journal)
 :hints (("Goal" :in-theory (enable fn-bprv-entries-decidedp))))
(defthm fn-bprv-nil-state-receipts
 (equal (fn-bpr-state-receipts nil) nil)
 :hints (("Goal" :in-theory (enable fn-bpr-state-receipts fn-bpa-nth))))
(defthm fn-bprv-replay-receipts-have-committed-decisions
 (fn-bprv-entries-decidedp
  (fn-bpr-state-receipts (cadr (fn-bprr-replay store records))) records)
 :hints (("Goal"
  :use ((:instance fn-bprv-replay-rest-preserves-decisions
    (st (fn-bpr-initial-state (fn-bprr-config (car records))))
    (records (cdr records)) (journal records)))
  :in-theory (e/d (fn-bprr-replay)
    (fn-bprv-replay-rest-preserves-decisions fn-bprr-replay-rest)))))

(defun fn-bprv-no-committed-decisionsp (journal)
 (if (consp journal)
  (and (not (and (fn-bprr-recordp (car journal))
                 (equal (fn-bprr-nth 0 (car journal)) :receipt-decision)
                 (equal (fn-bprr-nth 3 (car journal)) :committed)))
       (fn-bprv-no-committed-decisionsp (cdr journal))) t))
(defthm fn-bprv-no-commit-no-decided-entry
 (implies (fn-bprv-no-committed-decisionsp journal)
          (not (fn-bprv-entry-decidedp entry journal)))
 :hints (("Goal" :induct (fn-bprv-no-committed-decisionsp journal)
   :in-theory (enable fn-bprv-entry-decidedp fn-bprv-decision-for-entryp))))
(defthm fn-bprv-no-commit-no-committed-receipts
 (implies (and (fn-bprv-no-committed-decisionsp journal)
               (fn-bprv-entries-decidedp entries journal))
          (not (consp entries)))
 :hints (("Goal" :in-theory (enable fn-bprv-entries-decidedp))))
(defthm fn-bprv-no-committed-receipts-no-adu
 (implies (not (consp (fn-bpr-state-receipts st)))
          (equal (fn-bpr-receipt-adu st request) nil))
 :hints (("Goal" :in-theory (enable fn-bpr-receipt-adu fn-bpr-find-receipt))))
(defthm fn-bprv-replay-no-receipt-before-committed-decision
 (implies (fn-bprv-no-committed-decisionsp records)
  (equal (fn-bpr-receipt-adu (cadr (fn-bprr-replay store records)) request) nil))
 :hints (("Goal"
  :use (fn-bprv-replay-receipts-have-committed-decisions
        (:instance fn-bprv-no-commit-no-committed-receipts
          (journal records)
          (entries (fn-bpr-state-receipts (cadr (fn-bprr-replay store records))))))
  :in-theory (disable fn-bprv-replay-receipts-have-committed-decisions
                       fn-bprv-no-commit-no-committed-receipts))))
