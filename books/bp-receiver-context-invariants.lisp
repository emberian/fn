(in-package "ACL2")
(include-book "bp-receiver-store-invariants")
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

; Relational part of the receiver invariant. Typed state is proved separately.
(defun fn-bprv-entry-linkedp (config contexts entry)
 (let ((context (fn-bpr-receipt-entry-context entry))
       (receipt (fn-bpr-receipt-entry-receipt entry)))
  (and (consp context)
       (equal context (fn-bpr-find-context (fn-bpr-context-work-id context) contexts))
       (equal receipt (fn-bpr-receipt-for context config (fn-bpa-receipt-id receipt))))))
(defun fn-bprv-entries-linkedp (config contexts entries)
 (if (consp entries)
  (and (fn-bprv-entry-linkedp config contexts (car entries))
       (fn-bprv-entries-linkedp config contexts (cdr entries))) t))
(defun fn-bprv-pending-linkedp (config contexts receipts pending)
 (or (not (consp pending))
     (and (fn-bprv-entry-linkedp config contexts pending)
          (not (fn-bpr-find-receipt
            (fn-bpr-context-work-id (fn-bpr-receipt-entry-context pending)) receipts)))))
(defun fn-bprv-relationalp (store st)
 (and (fn-bprv-contexts-backedp store (fn-bpr-state-config st) (fn-bpr-state-contexts st))
      (fn-bprv-entries-linkedp (fn-bpr-state-config st) (fn-bpr-state-contexts st)
                              (fn-bpr-state-receipts st))
      (fn-bprv-pending-linkedp (fn-bpr-state-config st) (fn-bpr-state-contexts st)
                              (fn-bpr-state-receipts st) (fn-bpr-state-pending st))))

(defthm fn-bprv-context-backed-implies-consp
 (implies (fn-bprv-context-backedp store config context) (consp context))
 :hints (("Goal" :use ((:instance fn-bprv-found-record-binds
   (records (fn-sf-records (fn-sn-files store)))))
   :in-theory (e/d (fn-bprv-context-backedp fn-bprv-record-binds)
    (fn-bprv-find-record fn-bprv-found-record-binds))))
 :rule-classes :forward-chaining)
(local (in-theory (disable fn-bprv-context-backedp fn-bprv-record-binds fn-bprv-find-record)))
(defthm fn-bprv-nonnil-found-context-backed
 (implies (and (fn-bprv-contexts-backedp store config contexts)
               (fn-bpr-find-context id contexts))
          (fn-bprv-context-backedp store config (fn-bpr-find-context id contexts)))
 :hints (("Goal" :induct (fn-bpr-find-context id contexts)
    :in-theory (enable fn-bpr-find-context))))
(defthm fn-bprv-nonnil-found-context-consp
 (implies (and (fn-bprv-contexts-backedp store config contexts)
               (fn-bpr-find-context id contexts))
          (consp (fn-bpr-find-context id contexts)))
 :hints (("Goal" :use (fn-bprv-nonnil-found-context-backed
  (:instance fn-bprv-context-backed-implies-consp (context (fn-bpr-find-context id contexts))))
  :in-theory (disable fn-bprv-nonnil-found-context-backed fn-bprv-context-backed-implies-consp fn-bprv-contexts-backedp))))
(defthm fn-bprv-found-context-id
 (implies (consp (fn-bpr-find-context id contexts))
          (equal (fn-bpr-context-work-id (fn-bpr-find-context id contexts)) id))
 :hints (("Goal" :induct (fn-bpr-find-context id contexts)
    :in-theory (enable fn-bpr-find-context))))
(defthm fn-bprv-find-context-cons
 (equal (fn-bpr-find-context id (cons context contexts))
        (if (equal id (fn-bpr-context-work-id context)) context
          (fn-bpr-find-context id contexts)))
 :hints (("Goal" :expand ((fn-bpr-find-context id (cons context contexts))))))
(defthm fn-bprv-fresh-context-preserves-lookup
 (implies (and (not (fn-bpr-find-context (fn-bpr-context-work-id context) contexts))
               (consp (fn-bpr-find-context id contexts)))
          (equal (fn-bpr-find-context id (cons context contexts))
                 (fn-bpr-find-context id contexts))))
(defthm fn-bprv-entry-linked-fresh-context
 (implies (and (fn-bprv-entry-linkedp config contexts entry)
               (not (fn-bpr-find-context (fn-bpr-context-work-id context) contexts)))
          (fn-bprv-entry-linkedp config (cons context contexts) entry)))
(defthm fn-bprv-entries-linked-fresh-context
 (implies (and (fn-bprv-entries-linkedp config contexts entries)
               (not (fn-bpr-find-context (fn-bpr-context-work-id context) contexts)))
          (fn-bprv-entries-linkedp config (cons context contexts) entries))
 :hints (("Goal" :induct (fn-bprv-entries-linkedp config contexts entries)
    :in-theory (disable fn-bprv-entry-linkedp))))
(defthm fn-bprv-state-config-make
 (equal (fn-bpr-state-config (fn-bpr-make-state config contexts receipts pending)) config)
 :hints (("Goal" :in-theory (enable fn-bpr-state-config fn-bpr-make-state fn-bpa-nth))))
(defthm fn-bprv-state-contexts-make
 (equal (fn-bpr-state-contexts (fn-bpr-make-state config contexts receipts pending)) contexts)
 :hints (("Goal" :in-theory (enable fn-bpr-state-contexts fn-bpr-make-state fn-bpa-nth))))
(defthm fn-bprv-state-receipts-make
 (equal (fn-bpr-state-receipts (fn-bpr-make-state config contexts receipts pending)) receipts)
 :hints (("Goal" :in-theory (enable fn-bpr-state-receipts fn-bpr-make-state fn-bpa-nth))))
(defthm fn-bprv-state-pending-make
 (equal (fn-bpr-state-pending (fn-bpr-make-state config contexts receipts pending)) pending)
 :hints (("Goal" :in-theory (enable fn-bpr-state-pending fn-bpr-make-state fn-bpa-nth))))
(defthm fn-bprv-receipt-entry-context-make
 (equal (fn-bpr-receipt-entry-context (fn-bpr-make-receipt-entry context receipt)) context)
 :hints (("Goal" :in-theory (enable fn-bpr-receipt-entry-context fn-bpr-make-receipt-entry fn-bpa-nth))))
(defthm fn-bprv-receipt-entry-receipt-make
 (equal (fn-bpr-receipt-entry-receipt (fn-bpr-make-receipt-entry context receipt)) receipt)
 :hints (("Goal" :in-theory (enable fn-bpr-receipt-entry-receipt fn-bpr-make-receipt-entry fn-bpa-nth))))
(defthm fn-bprv-receipt-for-id
 (equal (fn-bpa-receipt-id (fn-bpr-receipt-for context config receipt-id)) receipt-id)
 :hints (("Goal" :in-theory (enable fn-bpa-receipt-id fn-bpr-receipt-for fn-bpa-make-receipt fn-bpa-nth))))
(defthm fn-bprv-new-entry-linked
 (implies (consp (fn-bpr-find-context id contexts))
  (fn-bprv-entry-linkedp config contexts
   (fn-bpr-make-receipt-entry (fn-bpr-find-context id contexts)
      (fn-bpr-receipt-for (fn-bpr-find-context id contexts) config receipt-id)))))
(defthm fn-bprv-new-entry-pending-linked
 (implies (and (consp (fn-bpr-find-context id contexts))
               (not (fn-bpr-find-receipt id receipts)))
  (fn-bprv-pending-linkedp config contexts receipts
   (fn-bpr-make-receipt-entry (fn-bpr-find-context id contexts)
      (fn-bpr-receipt-for (fn-bpr-find-context id contexts) config receipt-id)))))
(local (in-theory (disable fn-bprv-entry-linkedp fn-bprv-entries-linkedp
                           fn-bprv-pending-linkedp fn-bprv-contexts-backedp)))
(defthm fn-bprv-accept-preserves-relation
 (implies (fn-bprv-relationalp store st)
  (fn-bprv-relationalp store
   (cadr (fn-bpr-accept-request st store record request authorized))))
 :hints (("Goal" :in-theory (enable fn-bpr-accept-request fn-bprv-relationalp
   fn-bprv-pending-linkedp))))
(defthm fn-bprv-prepare-preserves-relation
 (implies (fn-bprv-relationalp store st)
  (fn-bprv-relationalp store (fn-bpr-prepare-receipt st work-id receipt-id authorized)))
 :hints (("Goal" :in-theory (enable fn-bpr-prepare-receipt fn-bprv-relationalp))))
(defthm fn-bprv-commit-preserves-relation
 (implies (fn-bprv-relationalp store st)
  (fn-bprv-relationalp store (fn-bpr-commit-receipt st work-id receipt-id outcome)))
 :hints (("Goal" :in-theory (enable fn-bpr-commit-receipt fn-bprv-relationalp
    fn-bprv-pending-linkedp fn-bprv-entries-linkedp))))
