; Receiver relation over an evolving Store: the history-indexed restatement.
; Design: specs/bp-evolving-store.md (packet C1-04).  The Store the host
; passes to fn-bprj-install/preflight/apply (host/bp-receipt-journal-host.lisp
; lines 12, 18-19, 22-23) is mutated by fn-sn-* ingress between calls; this
; relation mentions only its record history, which is append-only.
(in-package "ACL2")
(include-book "bp-receiver-trace-invariants")
(include-book "store-node-traces")
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
(local (in-theory (disable fn-snt-relation fn-snt-step fn-snt-run fn-sf-prefixp
                           fn-bpr-context-from-request-is-constructor)))

; -----------------------------------------------------------------------------
; The Store as an evolving object.  The receiver sees it through its record
; history alone; phase and node are never mentioned by the relation, which is
; what makes the relation true of a Store in motion (specs/bp-evolving-store.md).

(defun fn-bprv-history (store) (fn-sf-records (fn-sn-files store)))
(defun fn-bprv-phase (store) (fn-sf-phase (fn-sn-files store)))

; Grounding of one context: fn-bpr-request-acceptablep with the Store conjunct
; replaced by history membership (searched by fn-bprv-find-grounding-record)
; and the trusted-policy argument already at t.
(defun fn-bprv-record-grounds (config context record)
  (let ((request (fn-bpr-context-request context)))
    (and (consp record) (fn-record-p record)
         (fn-bpa-requestp request)
         (equal (fn-bpa-request-destination-eid request)
                (fn-bpr-config-destination config))
         (equal (fn-bpa-request-policy-id request)
                (fn-bpr-config-policy-id config))
         (equal (fn-bpa-request-subject request)
                (fn-record-content-subject record))
         (equal (fn-bpa-request-article request) (fn-record-payload record))
         (equal context (fn-bpr-context-from-request record request)))))
(defun fn-bprv-find-grounding-record (config context history)
  (if (consp history)
      (if (fn-bprv-record-grounds config context (car history))
          (car history)
        (fn-bprv-find-grounding-record config context (cdr history)))
    nil))
(defun fn-bprv-context-groundedp (config context history)
  (consp (fn-bprv-find-grounding-record config context history)))
(defun fn-bprv-contexts-groundedp (config contexts history)
  (if (consp contexts)
      (and (fn-bprv-context-groundedp config (car contexts) history)
           (fn-bprv-contexts-groundedp config (cdr contexts) history))
    t))

; R(history, receiver-state).  The linked, pending and decided conjuncts are
; the existing definitions, unchanged.
(defun fn-bprv-history-relationalp (history st)
  (and (fn-bprv-contexts-groundedp (fn-bpr-state-config st)
                                   (fn-bpr-state-contexts st) history)
       (fn-bprv-entries-linkedp (fn-bpr-state-config st)
                                (fn-bpr-state-contexts st)
                                (fn-bpr-state-receipts st))
       (fn-bprv-pending-linkedp (fn-bpr-state-config st)
                                (fn-bpr-state-contexts st)
                                (fn-bpr-state-receipts st)
                                (fn-bpr-state-pending st))))
(defun fn-bprv-evolving-invariantp (store st journal)
  (and (fn-bpr-statep st)
       (fn-bprv-history-relationalp (fn-bprv-history store) st)
       (fn-bprv-entries-decidedp (fn-bpr-state-receipts st) journal)))

; -----------------------------------------------------------------------------
; Prefix and grounding facts (L3, L4, L5, L6).

(defthm fn-bprv-prefix-preserves-member
  (implies (and (fn-sf-prefixp h1 h2) (member-equal x h1))
           (member-equal x h2))
  :hints (("Goal" :induct (fn-sf-prefixp h1 h2)
           :in-theory (enable fn-sf-prefixp))))

(defthm fn-bprv-record-grounds-consp
  (implies (fn-bprv-record-grounds config context record) (consp record))
  :rule-classes :forward-chaining)
(defthm fn-bprv-grounds-implies-consp-context
  (implies (fn-bprv-record-grounds config context record) (consp context))
  :hints (("Goal" :in-theory (enable fn-bpr-context-from-request fn-bpr-make-context)))
  :rule-classes :forward-chaining)
(local (in-theory (disable fn-bprv-record-grounds)))
(defthm fn-bprv-find-grounding-record-from-member
  (implies (and (member-equal record history)
                (fn-bprv-record-grounds config context record))
           (consp (fn-bprv-find-grounding-record config context history)))
  :hints (("Goal" :induct (fn-bprv-find-grounding-record config context history))))
(defthm fn-bprv-found-grounding-record-grounds
  (implies (consp (fn-bprv-find-grounding-record config context history))
           (fn-bprv-record-grounds config context
                                   (fn-bprv-find-grounding-record config context history)))
  :hints (("Goal" :induct (fn-bprv-find-grounding-record config context history))))
(defthm fn-bprv-found-grounding-record-is-member
  (implies (consp (fn-bprv-find-grounding-record config context history))
           (member-equal (fn-bprv-find-grounding-record config context history) history))
  :hints (("Goal" :induct (fn-bprv-find-grounding-record config context history))))

(defthm fn-bprv-grounded-monotone
  (implies (and (fn-bprv-context-groundedp config context h1)
                (fn-sf-prefixp h1 h2))
           (fn-bprv-context-groundedp config context h2))
  :hints (("Goal"
           :use ((:instance fn-bprv-find-grounding-record-from-member
                            (record (fn-bprv-find-grounding-record config context h1))
                            (history h2))
                 (:instance fn-bprv-prefix-preserves-member
                            (x (fn-bprv-find-grounding-record config context h1))))
           :in-theory (e/d (fn-bprv-context-groundedp)
                           (fn-bprv-find-grounding-record
                            fn-bprv-find-grounding-record-from-member
                            fn-bprv-prefix-preserves-member)))))
(defthm fn-bprv-grounded-implies-consp-context
  (implies (fn-bprv-context-groundedp config context h) (consp context))
  :hints (("Goal" :use ((:instance fn-bprv-found-grounding-record-grounds (history h))
                        (:instance fn-bprv-grounds-implies-consp-context
                                   (record (fn-bprv-find-grounding-record config context h))))
           :in-theory (e/d (fn-bprv-context-groundedp)
                           (fn-bprv-find-grounding-record
                            fn-bprv-found-grounding-record-grounds
                            fn-bprv-grounds-implies-consp-context))))
  :rule-classes :forward-chaining)
(local (in-theory (disable fn-bprv-context-groundedp)))
(defthm fn-bprv-contexts-grounded-monotone
  (implies (and (fn-bprv-contexts-groundedp config contexts h1)
                (fn-sf-prefixp h1 h2))
           (fn-bprv-contexts-groundedp config contexts h2))
  :hints (("Goal" :induct (fn-bprv-contexts-groundedp config contexts h1))))
(defthm fn-bprv-contexts-grounded-cons
  (implies (and (fn-bprv-context-groundedp config context h)
                (fn-bprv-contexts-groundedp config contexts h))
           (fn-bprv-contexts-groundedp config (cons context contexts) h)))
(defthm fn-bprv-found-context-grounded
  (implies (and (fn-bprv-contexts-groundedp config contexts h)
                (fn-bpr-find-context id contexts))
           (fn-bprv-context-groundedp config (fn-bpr-find-context id contexts) h))
  :hints (("Goal" :induct (fn-bpr-find-context id contexts)
           :in-theory (enable fn-bpr-find-context))))
(defthm fn-bprv-nonnil-found-context-grounded-consp
  (implies (and (fn-bprv-contexts-groundedp config contexts h)
                (fn-bpr-find-context id contexts))
           (consp (fn-bpr-find-context id contexts)))
  :hints (("Goal" :use (fn-bprv-found-context-grounded
                        (:instance fn-bprv-grounded-implies-consp-context
                                   (context (fn-bpr-find-context id contexts))))
           :in-theory (disable fn-bprv-found-context-grounded
                               fn-bprv-grounded-implies-consp-context
                               fn-bprv-contexts-groundedp))))
(defthm fn-bprv-history-relational-monotone
  (implies (and (fn-bprv-history-relationalp h1 st) (fn-sf-prefixp h1 h2))
           (fn-bprv-history-relationalp h2 st))
  :hints (("Goal" :in-theory (e/d (fn-bprv-history-relationalp)
                                  (fn-bprv-contexts-groundedp fn-bprv-entries-linkedp
                                   fn-bprv-pending-linkedp)))))

; -----------------------------------------------------------------------------
; The live gate implies grounding in the history it inspected (L8).

(defthm fn-bprv-acceptable-grounds
  (implies (fn-bpr-request-acceptablep store config record request authorized)
           (fn-bprv-record-grounds config (fn-bpr-context-from-request record request) record))
  :hints (("Goal" :use fn-bprv-acceptable-implies-consp-record
           :in-theory (e/d (fn-bprv-record-grounds fn-bpr-request-acceptablep)
                           (fn-bprv-acceptable-implies-consp-record)))))
(defthm fn-bprv-acceptable-implies-grounded
  (implies (fn-bpr-request-acceptablep store config record request authorized)
           (fn-bprv-context-groundedp config (fn-bpr-context-from-request record request)
                                      (fn-bprv-history store)))
  :hints (("Goal"
           :use ((:instance fn-bprv-find-grounding-record-from-member
                            (context (fn-bpr-context-from-request record request))
                            (history (fn-sf-records (fn-sn-files store))))
                 fn-bprv-acceptable-record-is-member fn-bprv-acceptable-grounds)
           :in-theory (e/d (fn-bprv-context-groundedp fn-bprv-history)
                           (fn-bprv-find-grounding-record
                            fn-bprv-find-grounding-record-from-member
                            fn-bprv-acceptable-record-is-member
                            fn-bprv-acceptable-grounds)))))

; -----------------------------------------------------------------------------
; Receiver-side preservation (L9 to L12).  The same store on both sides of L9
; is the receiver step's atomicity: ingress does not run inside fn-bprj-apply.

(local (in-theory (disable fn-bprv-entry-linkedp fn-bprv-entries-linkedp
                           fn-bprv-pending-linkedp fn-bprv-contexts-groundedp
                           fn-bprv-history)))
(defthm fn-bprv-accept-preserves-history-relation
  (implies (fn-bprv-history-relationalp (fn-bprv-history store) st)
           (fn-bprv-history-relationalp
            (fn-bprv-history store)
            (cadr (fn-bpr-accept-request st store record request authorized))))
  :hints (("Goal" :in-theory (enable fn-bpr-accept-request fn-bprv-history-relationalp
                                     fn-bprv-pending-linkedp))))
(defthm fn-bprv-prepare-preserves-history-relation
  (implies (fn-bprv-history-relationalp h st)
           (fn-bprv-history-relationalp h (fn-bpr-prepare-receipt st work-id receipt-id authorized)))
  :hints (("Goal" :in-theory (enable fn-bpr-prepare-receipt fn-bprv-history-relationalp))))
(defthm fn-bprv-commit-preserves-history-relation
  (implies (fn-bprv-history-relationalp h st)
           (fn-bprv-history-relationalp h (fn-bpr-commit-receipt st work-id receipt-id outcome)))
  :hints (("Goal" :in-theory (enable fn-bpr-commit-receipt fn-bprv-history-relationalp
                                     fn-bprv-pending-linkedp fn-bprv-entries-linkedp))))
(local (in-theory (disable fn-bprv-history-relationalp fn-bprv-entries-decidedp)))
(defthm fn-bprv-apply-record-preserves-history-relation
  (implies (fn-bprv-history-relationalp (fn-bprv-history store) st)
           (fn-bprv-history-relationalp (fn-bprv-history store)
                                        (cadr (fn-bprr-apply-record st store r))))
  :hints (("Goal" :in-theory (enable fn-bprr-apply-record))))
(defthm fn-bprv-apply-record-preserves-evolving-invariant
  (implies (and (fn-bprv-evolving-invariantp store st journal)
                (member-equal r journal))
           (fn-bprv-evolving-invariantp store (cadr (fn-bprr-apply-record st store r)) journal))
  :hints (("Goal" :use ((:instance fn-bprr-apply-record-preserves-statep (record r)))
           :in-theory (e/d (fn-bprv-evolving-invariantp)
                           (fn-bprr-apply-record-preserves-statep)))))
(defthm fn-bprv-replay-rest-preserves-history-relation
  (implies (fn-bprv-history-relationalp (fn-bprv-history store) st)
           (fn-bprv-history-relationalp (fn-bprv-history store)
                                        (cadr (fn-bprr-replay-rest st store records))))
  :hints (("Goal" :induct (fn-bprr-replay-rest st store records)
           :in-theory (enable fn-bprr-replay-rest))))
(defthm fn-bprv-replay-rest-preserves-evolving-invariant
  (implies (and (fn-bprv-evolving-invariantp store st journal)
                (fn-bprv-journal-subsetp records journal))
           (fn-bprv-evolving-invariantp store (cadr (fn-bprr-replay-rest st store records)) journal))
  :hints (("Goal" :use fn-bprr-replay-rest-preserves-statep
           :in-theory (e/d (fn-bprv-evolving-invariantp)
                           (fn-bprr-replay-rest-preserves-statep)))))

; -----------------------------------------------------------------------------
; Initial and replayed states (L15, L16).

(defthm fn-bprv-initial-history-relational
  (fn-bprv-history-relationalp h (fn-bpr-initial-state config))
  :hints (("Goal" :in-theory (enable fn-bpr-initial-state fn-bprv-history-relationalp
                                     fn-bprv-contexts-groundedp fn-bprv-entries-linkedp
                                     fn-bprv-pending-linkedp fn-bpr-state-config
                                     fn-bpr-state-contexts fn-bpr-state-receipts
                                     fn-bpr-state-pending fn-bpr-make-state fn-bpa-nth))))
(defthm fn-bprv-nil-history-relational
  (fn-bprv-history-relationalp h nil)
  :hints (("Goal" :in-theory (enable fn-bprv-history-relationalp fn-bprv-contexts-groundedp
                                     fn-bprv-entries-linkedp fn-bprv-pending-linkedp
                                     fn-bpr-state-config fn-bpr-state-contexts
                                     fn-bpr-state-receipts fn-bpr-state-pending fn-bpa-nth))))
(defthm fn-bprv-initial-evolving-invariant
  (implies (fn-bpr-configp config)
           (fn-bprv-evolving-invariantp store (fn-bpr-initial-state config) journal))
  :hints (("Goal" :in-theory (enable fn-bprv-evolving-invariantp))))
(defthm fn-bprv-replay-has-history-relation
  (fn-bprv-history-relationalp (fn-bprv-history store) (cadr (fn-bprr-replay store records)))
  :hints (("Goal" :in-theory (enable fn-bprr-replay))))
(defthm fn-bprv-successful-replay-has-evolving-invariant
  (implies (and (car (fn-bprr-replay store records))
                (fn-sf-prefixp (fn-bprv-history store) (fn-bprv-history later)))
           (fn-bprv-evolving-invariantp later (cadr (fn-bprr-replay store records)) records))
  :hints (("Goal"
           :use (fn-bprr-successful-replay-has-statep
                 fn-bprv-replay-receipts-have-committed-decisions
                 fn-bprv-replay-has-history-relation
                 (:instance fn-bprv-history-relational-monotone
                            (h1 (fn-bprv-history store)) (h2 (fn-bprv-history later))
                            (st (cadr (fn-bprr-replay store records)))))
           :in-theory (e/d (fn-bprv-evolving-invariantp)
                           (fn-bprr-successful-replay-has-statep
                            fn-bprv-replay-receipts-have-committed-decisions
                            fn-bprv-replay-has-history-relation
                            fn-bprv-history-relational-monotone)))))

; -----------------------------------------------------------------------------
; Grounded receipt, in every phase (L17, L18).

(defthm fn-bprv-grounded-context-has-history-record
  (implies (fn-bprv-context-groundedp config context h)
           (let ((record (fn-bprv-find-grounding-record config context h)))
             (and (fn-record-p record)
                  (member-equal record h)
                  (equal context (fn-bpr-context-from-request
                                  record (fn-bpr-context-request context)))
                  (equal (fn-bpa-request-article (fn-bpr-context-request context))
                         (fn-record-payload record))
                  (equal (fn-bpa-request-subject (fn-bpr-context-request context))
                         (fn-record-content-subject record)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bprv-found-grounding-record-grounds (history h))
                        (:instance fn-bprv-found-grounding-record-is-member (history h)))
           :in-theory (e/d (fn-bprv-context-groundedp fn-bprv-record-grounds)
                           (fn-bprv-find-grounding-record
                            fn-bprv-found-grounding-record-grounds
                            fn-bprv-found-grounding-record-is-member)))))

(defthm fn-bprv-evolving-output-has-linked-committed-entry
  (implies (and (fn-bprv-history-relationalp h st) (fn-bpr-receipt-adu st request))
           (let* ((context (fn-bpr-find-context (fn-bpa-request-work-id request)
                                                (fn-bpr-state-contexts st)))
                  (entry (fn-bpr-find-receipt (fn-bpr-context-work-id context)
                                              (fn-bpr-state-receipts st))))
             (and (consp context)
                  (equal request (fn-bpr-context-request context))
                  (member-equal entry (fn-bpr-state-receipts st))
                  (equal context (fn-bpr-receipt-entry-context entry))
                  (fn-bprv-context-groundedp (fn-bpr-state-config st) context h)
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
           :in-theory (e/d (fn-bpr-receipt-adu fn-bprv-history-relationalp fn-bprv-entry-linkedp)
                           (fn-bprv-found-receipt-linked)))))

(defthm fn-bprv-evolving-output-is-history-grounded
  (implies (and (fn-bprv-evolving-invariantp store st journal)
                (fn-bpr-receipt-adu st request))
           (let* ((context (fn-bpr-find-context (fn-bpa-request-work-id request)
                                                (fn-bpr-state-contexts st)))
                  (entry (fn-bpr-find-receipt (fn-bpr-context-work-id context)
                                              (fn-bpr-state-receipts st)))
                  (record (fn-bprv-find-grounding-record
                           (fn-bpr-state-config st) context (fn-bprv-history store))))
             (and (consp context)
                  (equal request (fn-bpr-context-request context))
                  (fn-record-p record)
                  (member-equal record (fn-bprv-history store))
                  (equal context (fn-bpr-context-from-request record request))
                  (equal (fn-bpa-request-article request) (fn-record-payload record))
                  (equal (fn-bpa-request-subject request)
                         (fn-record-content-subject record))
                  (member-equal entry (fn-bpr-state-receipts st))
                  (fn-bprv-entry-decidedp entry journal)
                  (equal (fn-bpr-receipt-entry-receipt entry)
                         (fn-bpr-receipt-for context (fn-bpr-state-config st)
                                             (fn-bpa-receipt-id
                                              (fn-bpr-receipt-entry-receipt entry))))
                  (equal (fn-bpr-receipt-adu st request)
                         (fn-bpa-encode (fn-bpr-receipt-entry-receipt entry))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bprv-evolving-output-has-linked-committed-entry
                            (h (fn-bprv-history store)))
                 (:instance fn-bprv-grounded-context-has-history-record
                            (config (fn-bpr-state-config st))
                            (context (fn-bpr-find-context (fn-bpa-request-work-id request)
                                                          (fn-bpr-state-contexts st)))
                            (h (fn-bprv-history store)))
                 (:instance fn-bprv-found-receipt-decided
                            (id (fn-bpa-request-work-id request))
                            (entries (fn-bpr-state-receipts st))))
           :in-theory (e/d (fn-bpr-receipt-adu fn-bprv-evolving-invariantp)
                           (fn-bprv-found-receipt-decided)))))

; -----------------------------------------------------------------------------
; Retained receipts survive later receiver steps against the same history
; (restatements of the retention theorems over fn-bprv-history).

(defthm fn-bprv-evolving-commit-preserves-existing-receipt
  (implies (and (fn-bprv-history-relationalp h st)
                (fn-bpr-find-receipt id (fn-bpr-state-receipts st)))
           (equal (fn-bpr-find-receipt id (fn-bpr-state-receipts
                                           (fn-bpr-commit-receipt st work-id receipt-id outcome)))
                  (fn-bpr-find-receipt id (fn-bpr-state-receipts st))))
  :hints (("Goal" :in-theory (enable fn-bpr-commit-receipt fn-bprv-history-relationalp
                                     fn-bprv-pending-linkedp))))
(defthm fn-bprv-evolving-apply-record-preserves-existing-receipt
  (implies (and (fn-bprv-history-relationalp (fn-bprv-history store) st)
                (fn-bpr-find-receipt id (fn-bpr-state-receipts st)))
           (equal (fn-bpr-find-receipt id (fn-bpr-state-receipts
                                           (cadr (fn-bprr-apply-record st store r))))
                  (fn-bpr-find-receipt id (fn-bpr-state-receipts st))))
  :hints (("Goal" :in-theory (enable fn-bprr-apply-record))))
(defthm fn-bprv-evolving-replay-rest-preserves-existing-receipt
  (implies (and (fn-bprv-history-relationalp (fn-bprv-history store) st)
                (fn-bpr-find-receipt id (fn-bpr-state-receipts st)))
           (equal (fn-bpr-find-receipt id (fn-bpr-state-receipts
                                           (cadr (fn-bprr-replay-rest st store records))))
                  (fn-bpr-find-receipt id (fn-bpr-state-receipts st))))
  :hints (("Goal" :induct (fn-bprr-replay-rest st store records)
           :in-theory (enable fn-bprr-replay-rest))))
(defthm fn-bprv-evolving-replay-rest-preserves-receipt-adu
  (implies (and (fn-bprv-history-relationalp (fn-bprv-history store) st)
                (fn-bpr-receipt-adu st request))
           (equal (fn-bpr-receipt-adu (cadr (fn-bprr-replay-rest st store records)) request)
                  (fn-bpr-receipt-adu st request)))
  :hints (("Goal"
           :use ((:instance fn-bprv-evolving-output-has-linked-committed-entry
                            (h (fn-bprv-history store)))
                 fn-bprv-output-implies-statep
                 fn-bprr-replay-rest-preserves-statep)
           :in-theory (e/d (fn-bpr-receipt-adu)
                           (fn-bprv-output-implies-statep
                            fn-bprr-replay-rest-preserves-statep)))))
