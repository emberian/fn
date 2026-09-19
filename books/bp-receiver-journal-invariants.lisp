(in-package "ACL2")
(include-book "bp-receiver-context-invariants")
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


; A committed receipt must have a matching typed :committed journal decision.
(defun fn-bprv-decision-for-entryp (r entry)
 (and (fn-bprr-recordp r)
      (equal (fn-bprr-nth 0 r) :receipt-decision)
      (equal (fn-bprr-nth 1 r)
        (fn-bpr-context-work-id (fn-bpr-receipt-entry-context entry)))
      (equal (fn-bprr-nth 2 r)
        (fn-bpa-receipt-id (fn-bpr-receipt-entry-receipt entry)))
      (equal (fn-bprr-nth 3 r) :committed)))
(defun fn-bprv-entry-decidedp (entry journal)
 (if (consp journal)
     (or (fn-bprv-decision-for-entryp (car journal) entry)
         (fn-bprv-entry-decidedp entry (cdr journal))) nil))
(defun fn-bprv-entries-decidedp (entries journal)
 (if (consp entries)
     (and (fn-bprv-entry-decidedp (car entries) journal)
          (fn-bprv-entries-decidedp (cdr entries) journal)) t))
(defun fn-bprv-journal-subsetp (records journal)
 (if (consp records)
     (and (member-equal (car records) journal)
          (fn-bprv-journal-subsetp (cdr records) journal)) t))
(local (in-theory (disable fn-bprv-decision-for-entryp)))
(defthm fn-bprv-entry-decided-from-member
 (implies (and (member-equal r journal) (fn-bprv-decision-for-entryp r entry))
          (fn-bprv-entry-decidedp entry journal))
 :hints (("Goal" :induct (fn-bprv-entry-decidedp entry journal))))
(defthm fn-bprv-nth-zero
 (equal (fn-bprr-nth 0 x) (car x))
 :hints (("Goal" :in-theory (enable fn-bprr-nth))))
(defthm fn-bprv-nth-one
 (equal (fn-bprr-nth 1 x) (cadr x))
 :hints (("Goal" :in-theory (enable fn-bprr-nth))))
(defthm fn-bprv-accept-receipts-unchanged
 (equal (fn-bpr-state-receipts (cadr (fn-bpr-accept-request st store record request authorized)))
        (fn-bpr-state-receipts st))
 :hints (("Goal" :in-theory (enable fn-bpr-accept-request))))
(defthm fn-bprv-prepare-receipts-unchanged
 (equal (fn-bpr-state-receipts (fn-bpr-prepare-receipt st work-id receipt-id authorized))
        (fn-bpr-state-receipts st))
 :hints (("Goal" :in-theory (enable fn-bpr-prepare-receipt))))
(defthm fn-bprv-decision-addition-covered
 (implies (and (fn-bprv-entries-decidedp (fn-bpr-state-receipts st) journal)
               (fn-bprr-recordp r)
               (equal (fn-bprr-nth 0 r) :receipt-decision)
               (member-equal r journal))
  (fn-bprv-entries-decidedp
   (fn-bpr-state-receipts (fn-bpr-commit-receipt st (fn-bprr-nth 1 r)
                           (fn-bprr-nth 2 r) (fn-bprr-nth 3 r))) journal))
 :hints (("Goal"
   :use ((:instance fn-bprv-entry-decided-from-member (entry (fn-bpr-state-pending st))))
   :in-theory (e/d (fn-bpr-commit-receipt fn-bprv-entries-decidedp fn-bprv-decision-for-entryp)
      (fn-bprv-entry-decidedp fn-bprv-entry-decided-from-member)))))
(local (in-theory (disable fn-bprv-relationalp fn-bprv-entries-decidedp)))
(defthm fn-bprv-apply-record-preserves-relation
 (implies (fn-bprv-relationalp store st)
          (fn-bprv-relationalp store (cadr (fn-bprr-apply-record st store r))))
 :hints (("Goal" :in-theory (enable fn-bprr-apply-record))))
(defthm fn-bprv-apply-record-preserves-decisions
 (implies (and (fn-bprv-entries-decidedp (fn-bpr-state-receipts st) journal)
               (member-equal r journal))
          (fn-bprv-entries-decidedp
           (fn-bpr-state-receipts (cadr (fn-bprr-apply-record st store r))) journal))
 :hints (("Goal" :use fn-bprv-decision-addition-covered
  :in-theory (e/d (fn-bprr-apply-record) (fn-bprv-decision-addition-covered)))))
(defthm fn-bprv-replay-rest-preserves-relation
 (implies (fn-bprv-relationalp store st)
          (fn-bprv-relationalp store (cadr (fn-bprr-replay-rest st store records))))
 :hints (("Goal" :induct (fn-bprr-replay-rest st store records)
    :in-theory (enable fn-bprr-replay-rest))))
(defthm fn-bprv-replay-rest-preserves-decisions
 (implies (and (fn-bprv-entries-decidedp (fn-bpr-state-receipts st) journal)
               (fn-bprv-journal-subsetp records journal))
          (fn-bprv-entries-decidedp
           (fn-bpr-state-receipts (cadr (fn-bprr-replay-rest st store records))) journal))
 :hints (("Goal" :induct (fn-bprr-replay-rest st store records)
    :in-theory (enable fn-bprr-replay-rest fn-bprv-journal-subsetp))))
