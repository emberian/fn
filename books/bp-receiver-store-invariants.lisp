(in-package "ACL2")
(include-book "bp-receipt-records")
; This book reasons under the receiver definitions; open them here, locally.
(local (in-theory (enable fn-bp-receiver-vocabulary fn-bp-receiver-records-vocabulary
                          fn-bpi-node-record-committedp)))
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
; A finite witness search grounds every retained context in the actual Store.
; The Store argument stays fixed during receiver journal replay.
(defun fn-bprv-record-binds (store config context record)
  (and (consp record)
       (fn-bpr-request-acceptablep store config record
                                   (fn-bpr-context-request context) t)
       (equal context
              (fn-bpr-context-from-request record (fn-bpr-context-request context)))))
(defun fn-bprv-find-record (store config context records)
  (if (consp records)
      (if (fn-bprv-record-binds store config context (car records))
          (car records)
        (fn-bprv-find-record store config context (cdr records)))
    nil))
(defun fn-bprv-context-backedp (store config context)
  (consp (fn-bprv-find-record store config context
                             (fn-sf-records (fn-sn-files store)))))
(defun fn-bprv-contexts-backedp (store config contexts)
  (if (consp contexts)
      (and (fn-bprv-context-backedp store config (car contexts))
           (fn-bprv-contexts-backedp store config (cdr contexts)))
    t))

(defthm fn-bprv-request-of-derived-context
  (equal (fn-bpr-context-request (fn-bpr-context-from-request record request)) request)
  :hints (("Goal" :in-theory (enable fn-bpr-context-request
    fn-bpr-context-from-request fn-bpr-make-context fn-bpa-nth))))
(defthm fn-bprv-acceptable-implies-consp-record
  (implies (fn-bpr-request-acceptablep store config record request authorized)
           (consp record))
  :hints (("Goal" :in-theory (enable fn-bpr-request-acceptablep fn-record-p))))
(defthm fn-bprv-derived-context-record-binds
  (implies (fn-bpr-request-acceptablep store config record request authorized)
           (fn-bprv-record-binds store config
                                 (fn-bpr-context-from-request record request) record))
  :hints (("Goal" :use fn-bprv-acceptable-implies-consp-record
   :in-theory (e/d (fn-bprv-record-binds fn-bpr-request-acceptablep) (fn-bprv-acceptable-implies-consp-record)))))
(defthm fn-bprv-record-binds-consp
 (implies (fn-bprv-record-binds store config context record) (consp record))
 :rule-classes :forward-chaining)
(local (in-theory (disable fn-bprv-record-binds)))
(defthm fn-bprv-find-record-from-member
  (implies (and (member-equal record records)
                (consp record)
                (fn-bprv-record-binds store config context record))
           (consp (fn-bprv-find-record store config context records)))
  :hints (("Goal" :induct (fn-bprv-find-record store config context records))))
(defthm fn-bprv-acceptable-record-is-member
  (implies (fn-bpr-request-acceptablep store config record request authorized)
           (member-equal record (fn-sf-records (fn-sn-files store))))
  :hints (("Goal" :in-theory (enable fn-bpr-request-acceptablep fn-bpr-store-record-acceptedp))))
(defthm fn-bprv-derived-context-backed
  (implies (fn-bpr-request-acceptablep store config record request authorized)
           (fn-bprv-context-backedp store config (fn-bpr-context-from-request record request)))
  :hints (("Goal" :use ((:instance fn-bprv-find-record-from-member
      (context (fn-bpr-context-from-request record request))
      (records (fn-sf-records (fn-sn-files store)))))
    :in-theory (enable fn-bprv-context-backedp))))
(defthm fn-bprv-found-record-binds
  (implies (consp (fn-bprv-find-record store config context records))
           (fn-bprv-record-binds store config context
                                 (fn-bprv-find-record store config context records)))
  :hints (("Goal" :induct (fn-bprv-find-record store config context records))))
(defthm fn-bprv-found-record-is-member
  (implies (consp (fn-bprv-find-record store config context records))
           (member-equal (fn-bprv-find-record store config context records) records))
  :hints (("Goal" :induct (fn-bprv-find-record store config context records))))
(defthm fn-bprv-backed-context-has-actual-ready-record
  (implies (fn-bprv-context-backedp store config context)
   (let ((record (fn-bprv-find-record store config context
                                     (fn-sf-records (fn-sn-files store)))))
     (and (fn-sn-statep store)
          (equal (fn-sf-phase (fn-sn-files store)) :ready)
          (fn-record-p record)
          (member-equal record (fn-sf-records (fn-sn-files store)))
          (fn-bpi-node-record-committedp (fn-sn-node store) record)
          (equal context (fn-bpr-context-from-request record (fn-bpr-context-request context)))
          (equal (fn-bpa-request-article (fn-bpr-context-request context))
                 (fn-record-payload record))
          (equal (fn-bpa-request-subject (fn-bpr-context-request context))
                 (fn-record-content-subject record)))))
  :rule-classes nil
  :hints (("Goal"
    :use ((:instance fn-bprv-found-record-binds
             (records (fn-sf-records (fn-sn-files store))))
          (:instance fn-bprv-found-record-is-member
             (records (fn-sf-records (fn-sn-files store)))))
    :in-theory (e/d (fn-bprv-context-backedp fn-bprv-record-binds
                       fn-bpr-request-acceptablep fn-bpr-store-record-acceptedp)
                     (fn-bprv-find-record fn-bprv-found-record-binds fn-bprv-found-record-is-member)))))
(defthm fn-bprv-contexts-backed-cons
  (implies (and (fn-bprv-context-backedp store config context)
                (fn-bprv-contexts-backedp store config contexts))
           (fn-bprv-contexts-backedp store config (cons context contexts))))
(defthm fn-bprv-found-context-backed
  (implies (and (fn-bprv-contexts-backedp store config contexts)
                (consp (fn-bpr-find-context work-id contexts)))
           (fn-bprv-context-backedp store config (fn-bpr-find-context work-id contexts)))
  :hints (("Goal" :induct (fn-bpr-find-context work-id contexts)
     :in-theory (enable fn-bpr-find-context))))
