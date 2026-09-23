; Node-committedness of every history record in an idle Store (L19, L20 of
; specs/bp-evolving-store.md), and the carry of the live acceptance gate to
; every later ready Store.  Replay applies each record through the actual
; fn-node-prepare/fn-node-complete pair (books/replay.lisp); nothing here
; changes a transition.
;
; Restated 2026-09-23 (PRF-007): the history lemmas quantify over article
; records, `(fn-record-p record)'.  Since 6ab2c783 and 346a8f99 a Store history
; also carries retention and statement events, which install no article under
; their own name; tests/acl2/bp-receiver-evolving-tests commits a retention
; undertake on a related :ready Store where the unrestated conclusion is false.
(in-package "ACL2")
(include-book "bp-receiver-evolving-history-invariants")
; codecs withdrew the record and cbor proof vocabularies at export (2026-09-19);
; this book reasons under them, so open them here, locally.
(local (in-theory (enable fn-record-record-vocabulary fn-record-codec-vocabulary fn-record-guard-vocabulary
                          fn-record-invariants-vocabulary fn-cbor-record-vocabulary
                          fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary)))
; Withdrawn at the core export (2026-09-19); this book reasons under them
; as it did when they were enabled on include.
(local (in-theory (enable fn-accept-complete fn-accept-prepare fn-clear-pending fn-initial-state
                          fn-install-pending fn-node-complete fn-node-initial-state
                          fn-node-pending-matchesp fn-node-prepare fn-node-recover fn-node-stagep
                          fn-node-statep fn-replay fn-replay-advance-txid fn-replay-apply-record
                          fn-replay-faultp fn-replay-loop fn-replay-okp fn-retain-admissiblep
                          fn-retain-admit fn-retain-statep fn-statep)))
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
(local (in-theory (disable fn-snt-relation fn-snt-step fn-snt-run fn-sf-prefixp
                           fn-node-statep fn-statep fn-retain-statep
                           fn-node-prepare fn-node-complete fn-node-recover
                           fn-replay-advance-txid fn-replay-apply-record
                           fn-replay-loop fn-replay fn-replay-okp fn-replay-faultp
                           fn-accept-prepare fn-accept-complete fn-install-pending
                           fn-clear-pending fn-article-from-pending
                           fn-retain-admissiblep fn-retain-admit
                           fn-selection-validp fn-acceptedp fn-allocate-memberships
                           fn-advance-nexts fn-octet-listp fn-node-binding-listp
                           fn-node-articles-have-archive-bindingsp fn-node-stagep
                           fn-subsetp fn-article-msgids fn-node-binding-ids
                           fn-retain-obligation-ids fn-retain-pins
                           fn-node-pending-matchesp fn-pending-matchesp
                           fn-find-article fn-node-find-binding
                           fn-node-binding-msgids fn-node-initial-state
                           fn-initial-state fn-initial-nexts)))

; -----------------------------------------------------------------------------
; Every history record is node-committed whenever the Store is idle (L19).
; The node of an idle related Store is fn-sf-replay-node of its history
; (fn-snt-ready-or-recovered-node-is-exact-replay); replay applies each record
; through the actual fn-node-prepare/fn-node-complete pair, which installs its
; article and binding, and every later record preserves them.  Every proof
; below names its theory explicitly: the inherited rule set of the trace books
; does not terminate on these goals.

(defun fn-bprv-node-idlep (node) (null (fn-node-stage node)))

(defthm fn-bprv-node-statep-facts
  (implies (fn-node-statep s)
           (and (consp s)
                (fn-statep (fn-node-acceptance s))
                (equal (null (fn-node-stage s))
                       (null (fn-state-pending (fn-node-acceptance s))))
                (or (not (equal (fn-state-fenced (fn-node-acceptance s)) t))
                    (consp (fn-node-stage s)))))
  :rule-classes nil
  ; core exports the shape facts as forward-chaining rules (fn-node-state-shapep-forward-shape,
  ; docs/proof-style.md s1); it supplies (consp s) here now that fn-node-statep is opaque.
  :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons fn-node-statep len
                                               fn-node-state-shapep-forward-shape)
                                             (theory 'minimal-theory)))))
(defthm fn-bprv-node-statep-consp
  (implies (fn-node-statep s) (consp s))
  :hints (("Goal" :use fn-bprv-node-statep-facts
           :in-theory (theory 'minimal-theory)))
  :rule-classes :forward-chaining)
(defthm fn-bprv-node-statep-acceptance
  (implies (fn-node-statep s) (fn-statep (fn-node-acceptance s)))
  :hints (("Goal" :use fn-bprv-node-statep-facts
           :in-theory (theory 'minimal-theory))))
(defthm fn-bprv-committed-implies-node-statep
  (implies (fn-bpi-node-record-committedp node record) (fn-node-statep node))
  :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons fn-bpi-node-record-committedp)
                                             (theory 'minimal-theory))))
  :rule-classes :forward-chaining)

; One step: applying a record to an idle node installs that record's article
; and binding, and leaves the node idle again.  The step is taken apart along
; the actual definitions: advance, prepare, complete, install.

(defthm fn-bprv-advance-keeps-idle
  (implies (fn-bprv-node-idlep node)
           (fn-bprv-node-idlep (fn-replay-advance-txid node txid)))
  :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons fn-replay-advance-txid fn-bprv-node-idlep
                                fn-node-stage fn-node-make-state)
                              (theory 'minimal-theory)))))

; fn-node-prepare on an idle node that ends staged: the stage carries the
; record's identity, the acceptance is the actual fn-accept-prepare step, and
; that step did change the acceptance.
(defthm fn-bprv-staged-prepare-facts
  (implies (and (fn-node-statep s) (fn-bprv-node-idlep s)
                (consp (fn-node-stage (fn-node-prepare s generation msgid payload groups
                                                       obligation-id subject evidence charge stamp))))
           (let ((prepared (fn-node-prepare s generation msgid payload groups
                                            obligation-id subject evidence charge stamp)))
             (and (equal (fn-node-stage-msgid (fn-node-stage prepared)) msgid)
                  (equal (fn-node-stage-subject (fn-node-stage prepared)) subject)
                  (equal (fn-node-stage-id (fn-node-stage prepared)) obligation-id)
                  (equal (fn-node-acceptance prepared)
                         (fn-accept-prepare (fn-node-acceptance s) generation msgid payload groups stamp))
                  (equal (fn-node-bindings prepared) (fn-node-bindings s))
                  (not (equal (fn-accept-prepare (fn-node-acceptance s) generation msgid payload groups stamp)
                              (fn-node-acceptance s))))))
  :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons fn-node-prepare fn-bprv-node-idlep fn-node-stage
                                fn-node-acceptance fn-node-bindings fn-node-make-state
                                fn-node-make-stage fn-node-stage-msgid
                                fn-node-stage-subject fn-node-stage-id)
                              (theory 'minimal-theory)))))

; fn-accept-prepare that changed the state staged exactly the proposal.
(defthm fn-bprv-changed-accept-prepare-facts
  (implies (and (fn-statep s)
                (not (equal (fn-accept-prepare s generation msgid payload groups stamp) s)))
           (let ((next (fn-accept-prepare s generation msgid payload groups stamp)))
             (and (equal (fn-state-pending next)
                         (fn-make-pending (fn-state-next-txid s) generation msgid payload groups
                                          (fn-allocate-memberships groups (fn-state-nexts s)) t stamp))
                  (equal (fn-state-fenced next) nil)
                  (equal (fn-state-articles next) (fn-state-articles s)))))
  :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons fn-accept-prepare fn-make-state fn-state-pending
                                fn-state-fenced fn-state-articles)
                              (theory 'minimal-theory)))))

; The matching durable completion is the definition's durable branch.
(defthm fn-bprv-durable-complete-unfolds
  (implies (fn-node-pending-matchesp s txid generation)
           (equal (fn-node-complete s txid generation :durable)
                  (fn-node-make-state
                   (fn-accept-complete (fn-node-acceptance s) txid generation :durable)
                   (fn-node-stage-retention (fn-node-stage s))
                   nil
                   (cons (fn-node-make-binding (fn-node-stage-msgid (fn-node-stage s))
                                               (fn-node-stage-subject (fn-node-stage s))
                                               (fn-node-stage-id (fn-node-stage s)))
                         (fn-node-bindings s)))))
  :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons fn-node-complete)
                                             (theory 'minimal-theory)))))
(defthm fn-bprv-durable-accept-complete-installs
  (implies (and (fn-statep s)
                (not (equal (fn-state-fenced s) t))
                (fn-pending-matchesp (fn-state-pending s) txid generation))
           (equal (fn-accept-complete s txid generation :durable) (fn-install-pending s)))
  :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons fn-accept-complete)
                                             (theory 'minimal-theory)))))
(defthm fn-bprv-install-pending-facts
  (and (implies (equal (fn-pending-msgid (fn-state-pending s)) m)
                (equal (fn-find-article m (fn-state-articles (fn-install-pending s)))
                       (fn-article-from-pending (fn-state-pending s))))
       (equal (fn-state-pending (fn-install-pending s)) nil))
  :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons fn-install-pending fn-find-article fn-article-from-pending
                                fn-make-article fn-article-msgid fn-make-state
                                fn-state-articles fn-state-pending)
                              (theory 'minimal-theory)))))
(defthm fn-bprv-article-from-pending-fields
  (and (consp (fn-article-from-pending p))
       (equal (fn-article-payload (fn-article-from-pending p)) (fn-pending-payload p))
       (equal (fn-article-groups (fn-article-from-pending p)) (fn-pending-groups p)))
  :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons fn-article-from-pending fn-make-article
                                fn-article-payload fn-article-groups)
                              (theory 'minimal-theory)))))
(defthm fn-bprv-find-binding-of-new
  (equal (fn-node-find-binding msgid (cons (fn-node-make-binding msgid subject id) rest))
         (fn-node-make-binding msgid subject id))
  :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons fn-node-find-binding fn-node-make-binding fn-node-binding-msgid)
                              (theory 'minimal-theory)))))

(defthm fn-bprv-node-make-state-fields
  (and (equal (fn-node-acceptance (fn-node-make-state a r s b)) a)
       (equal (fn-node-stage (fn-node-make-state a r s b)) s)
       (equal (fn-node-bindings (fn-node-make-state a r s b)) b)
       (equal (fn-bprv-node-idlep (fn-node-make-state a r s b)) (null s)))
  :hints (("Goal" :in-theory (union-theories
                              '(car-cons cdr-cons fn-node-make-state fn-node-acceptance
                                fn-node-stage fn-node-bindings fn-bprv-node-idlep)
                              (theory 'minimal-theory)))))
(defthm fn-bprv-make-pending-fields
  (and (equal (fn-pending-msgid (fn-make-pending txid generation msgid payload groups
                                                 memberships pin stamp))
              msgid)
       (equal (fn-pending-payload (fn-make-pending txid generation msgid payload groups
                                                   memberships pin stamp))
              payload)
       (equal (fn-pending-groups (fn-make-pending txid generation msgid payload groups
                                                  memberships pin stamp))
              groups))
  :hints (("Goal" :in-theory (union-theories
                              '(car-cons cdr-cons fn-make-pending fn-pending-msgid
                                fn-pending-payload fn-pending-groups)
                              (theory 'minimal-theory)))))
(defthm fn-bprv-make-binding-fields
  (and (consp (fn-node-make-binding msgid subject id))
       (equal (fn-node-binding-subject (fn-node-make-binding msgid subject id)) subject)
       (equal (fn-node-binding-id (fn-node-make-binding msgid subject id)) id))
  :hints (("Goal" :in-theory (union-theories
                              '(car-cons cdr-cons fn-node-make-binding
                                fn-node-binding-subject fn-node-binding-id)
                              (theory 'minimal-theory)))))

(defthm fn-bprv-apply-record-installs-record
  (implies (and (fn-node-statep node) (fn-bprv-node-idlep node) (fn-record-p record)
                (consp (fn-replay-apply-record node record)))
           (and (fn-bpi-node-record-committedp (fn-replay-apply-record node record) record)
                (fn-bprv-node-idlep (fn-replay-apply-record node record))))
  :hints (("Goal"
           :use ((:instance fn-replay-advance-preserves-node-statep
                            (recorded-txid (fn-record-txid record)))
                 fn-replay-apply-record-non-nil-is-node-state)
           :in-theory (union-theories
                       '(car-cons cdr-cons fn-replay-apply-record fn-node-pending-matchesp
                         fn-snt-an-article-record-is-no-other-store-event fn-store-event-p fn-store-event-txid
                         fn-bpi-node-record-committedp
                         fn-bprv-node-make-state-fields fn-bprv-make-pending-fields
                         fn-bprv-make-binding-fields
                         fn-bprv-node-statep-acceptance fn-bprv-advance-keeps-idle
                         fn-bprv-staged-prepare-facts fn-bprv-changed-accept-prepare-facts
                         fn-bprv-durable-complete-unfolds
                         fn-bprv-durable-accept-complete-installs
                         fn-bprv-install-pending-facts fn-bprv-article-from-pending-fields
                         fn-bprv-find-binding-of-new fn-prepare-preserves-state)
                       (theory 'minimal-theory)))))

; Later steps: an installed article and binding survive every later record.
(defthm fn-bprv-find-article-implies-accepted
  (implies (consp (fn-find-article msgid xs)) (fn-acceptedp msgid xs))
  :hints (("Goal" :induct (fn-find-article msgid xs)
           :in-theory (union-theories '(car-cons cdr-cons fn-find-article fn-acceptedp)
                                      (theory 'minimal-theory)))))
(defthm fn-bprv-find-binding-implies-member-msgids
  (implies (consp (fn-node-find-binding msgid xs))
           (member-equal msgid (fn-node-binding-msgids xs)))
  :hints (("Goal" :induct (fn-node-find-binding msgid xs)
           :expand ((fn-node-binding-msgids xs)
                    (member-equal msgid (fn-node-binding-msgids xs)))
           :in-theory (union-theories '(car-cons cdr-cons fn-node-find-binding fn-node-binding-msgids member-equal)
                                      (theory 'minimal-theory)))))
(defthm fn-bprv-node-prepare-keeps-existing-article
  (implies (fn-node-statep s)
           (equal (fn-find-article
                   m (fn-state-articles
                      (fn-node-acceptance
                       (fn-node-prepare s generation msgid payload groups
                                        obligation-id subject evidence charge stamp))))
                  (fn-find-article m (fn-state-articles (fn-node-acceptance s)))))
  :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons fn-node-prepare fn-bprv-node-make-state-fields
                                fn-prepare-preserves-existing-message-id-binding
                                fn-bprv-node-statep-acceptance)
                              (theory 'minimal-theory)))))
(defthm fn-bprv-node-complete-keeps-existing-article
  (implies (and (fn-node-statep s)
                (consp (fn-find-article m (fn-state-articles (fn-node-acceptance s)))))
           (equal (fn-find-article
                   m (fn-state-articles
                      (fn-node-acceptance
                       (fn-node-complete s txid generation completion-status))))
                  (fn-find-article m (fn-state-articles (fn-node-acceptance s)))))
  :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons fn-node-complete fn-bprv-node-make-state-fields
                                fn-complete-preserves-existing-message-id-binding
                                fn-bprv-node-statep-acceptance
                                fn-bprv-find-article-implies-accepted)
                              (theory 'minimal-theory)))))
(defthm fn-bprv-apply-record-keeps-committed
  (implies (and (fn-bpi-node-record-committedp node record)
                (fn-record-p record2)
                (consp (fn-replay-apply-record node record2)))
           (fn-bpi-node-record-committedp (fn-replay-apply-record node record2) record))
  :hints (("Goal"
           :use ((:instance fn-replay-advance-preserves-node-statep
                            (recorded-txid (fn-record-txid record2)))
                 (:instance fn-node-prepare-preserves-state
                            (s (fn-replay-advance-txid node (fn-record-txid record2)))
                            (generation (fn-record-generation record2))
                            (msgid (fn-record-msgid record2))
                            (payload (fn-record-payload record2))
                            (groups (fn-record-groups record2))
                            (obligation-id (fn-record-obligation-id record2))
                            (subject (fn-record-content-subject record2))
                            (evidence (fn-record-release-evidence record2))
                            (charge (fn-record-charge record2))
                            (stamp (fn-record-stamp record2)))
                 (:instance fn-replay-apply-record-non-nil-is-node-state (record record2))
                 (:instance fn-node-complete-preserves-existing-binding
                            (s (fn-node-prepare
                                (fn-replay-advance-txid node (fn-record-txid record2))
                                (fn-record-generation record2) (fn-record-msgid record2)
                                (fn-record-payload record2) (fn-record-groups record2)
                                (fn-record-obligation-id record2)
                                (fn-record-content-subject record2)
                                (fn-record-release-evidence record2)
                                (fn-record-charge record2) (fn-record-stamp record2)))
                            (msgid (fn-record-msgid record))
                            (txid (fn-record-txid record2))
                            (generation (fn-record-generation record2))
                            (completion-status :durable)))
           :in-theory (union-theories '(car-cons cdr-cons fn-replay-apply-record fn-bpi-node-record-committedp
                         fn-snt-an-article-record-is-no-other-store-event fn-store-event-p fn-store-event-txid
                         fn-bprv-node-prepare-keeps-existing-article
                         fn-bprv-node-complete-keeps-existing-article
                         fn-node-prepare-preserves-bindings
                         fn-replay-advance-keeps-committed-articles
                         fn-replay-advance-keeps-committed-bindings
                         fn-bprv-find-binding-implies-member-msgids
                         fn-bprv-committed-implies-node-statep)
                       (theory 'minimal-theory)))))

;
; A Store history carries every Store event, not only article records: since
; 6ab2c783 (2026-09-21) `fn-replay-apply-record' dispatches a retention
; undertake/release to `fn-replay-apply-retention-event', and since 346a8f99
; a statement verdict or keyring snapshot to `fn-replay-apply-identity-neutral'
; and an accepted statement (`fn-stxa-p') to the article arm on its decoded
; composite record.  The loop lemmas below therefore need committedness and
; idleness across every arm.  Retention and identity events leave the
; published articles and archive bindings as they were; the article arm is
; the durable completion, for whatever record the arm installs.
(defthm fn-bprv-committed-carries-to-same-articles-and-bindings
  (implies (and (fn-bpi-node-record-committedp node record)
                (fn-node-statep node2)
                (equal (fn-state-articles (fn-node-acceptance node2))
                       (fn-state-articles (fn-node-acceptance node)))
                (equal (fn-node-bindings node2) (fn-node-bindings node)))
           (fn-bpi-node-record-committedp node2 record))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-bpi-node-record-committedp)
                                             (theory 'minimal-theory)))))
(defthm fn-bprv-retention-event-keeps-articles-and-bindings
  (implies (consp (fn-replay-apply-retention-event node event))
           (and (equal (fn-state-articles
                        (fn-node-acceptance (fn-replay-apply-retention-event node event)))
                       (fn-state-articles (fn-node-acceptance node)))
                (equal (fn-node-bindings (fn-replay-apply-retention-event node event))
                       (fn-node-bindings node))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-replay-apply-retention-event fn-replay-complete-retention
                                fn-replay-node-with-retention fn-bprv-node-make-state-fields
                                fn-replay-advance-keeps-committed-articles
                                fn-replay-advance-keeps-committed-bindings)
                              (theory 'minimal-theory)))))
(defthm fn-bprv-identity-neutral-keeps-articles-and-bindings
  (implies (consp (fn-replay-apply-identity-neutral node event))
           (and (equal (fn-state-articles
                        (fn-node-acceptance (fn-replay-apply-identity-neutral node event)))
                       (fn-state-articles (fn-node-acceptance node)))
                (equal (fn-node-bindings (fn-replay-apply-identity-neutral node event))
                       (fn-node-bindings node))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-replay-apply-identity-neutral
                                fn-replay-advance-keeps-committed-articles
                                fn-replay-advance-keeps-committed-bindings)
                              (theory 'minimal-theory)))))
(defthm fn-bprv-article-arm-keeps-committed
  (let ((prepared (fn-node-prepare (fn-replay-advance-txid node txid)
                                   (fn-record-generation article) (fn-record-msgid article)
                                   (fn-record-payload article) (fn-record-groups article)
                                   (fn-record-obligation-id article)
                                   (fn-record-content-subject article)
                                   (fn-record-release-evidence article)
                                   (fn-record-charge article) (fn-record-stamp article))))
    (implies (and (fn-bpi-node-record-committedp node record)
                  (fn-node-statep (fn-node-complete prepared (fn-record-txid article)
                                                    (fn-record-generation article) :durable)))
             (fn-bpi-node-record-committedp
              (fn-node-complete prepared (fn-record-txid article)
                                (fn-record-generation article) :durable)
              record)))
  :hints (("Goal"
           :use ((:instance fn-replay-advance-preserves-node-statep (recorded-txid txid))
                 (:instance fn-node-prepare-preserves-state
                            (s (fn-replay-advance-txid node txid))
                            (generation (fn-record-generation article))
                            (msgid (fn-record-msgid article))
                            (payload (fn-record-payload article))
                            (groups (fn-record-groups article))
                            (obligation-id (fn-record-obligation-id article))
                            (subject (fn-record-content-subject article))
                            (evidence (fn-record-release-evidence article))
                            (charge (fn-record-charge article))
                            (stamp (fn-record-stamp article)))
                 (:instance fn-node-complete-preserves-existing-binding
                            (s (fn-node-prepare
                                (fn-replay-advance-txid node txid)
                                (fn-record-generation article) (fn-record-msgid article)
                                (fn-record-payload article) (fn-record-groups article)
                                (fn-record-obligation-id article)
                                (fn-record-content-subject article)
                                (fn-record-release-evidence article)
                                (fn-record-charge article) (fn-record-stamp article)))
                            (msgid (fn-record-msgid record))
                            (txid (fn-record-txid article))
                            (generation (fn-record-generation article))
                            (completion-status :durable)))
           :in-theory (union-theories '(car-cons cdr-cons fn-bpi-node-record-committedp
                         fn-bprv-node-prepare-keeps-existing-article
                         fn-bprv-node-complete-keeps-existing-article
                         fn-node-prepare-preserves-bindings
                         fn-replay-advance-keeps-committed-articles
                         fn-replay-advance-keeps-committed-bindings
                         fn-bprv-find-binding-implies-member-msgids
                         fn-bprv-committed-implies-node-statep)
                       (theory 'minimal-theory)))))
(defthm fn-bprv-apply-store-event-keeps-committed
  (implies (and (fn-bpi-node-record-committedp node record)
                (fn-store-event-p event)
                (consp (fn-replay-apply-record node event)))
           (fn-bpi-node-record-committedp (fn-replay-apply-record node event) record))
  :hints (("Goal"
           :use ((:instance fn-replay-apply-record-non-nil-is-node-state (record event))
                 (:instance fn-bprv-committed-carries-to-same-articles-and-bindings
                            (node2 (fn-replay-apply-record node event))))
           :in-theory (union-theories '(fn-replay-apply-record
                         fn-bprv-committed-implies-node-statep
                         fn-bprv-retention-event-keeps-articles-and-bindings
                         fn-bprv-identity-neutral-keeps-articles-and-bindings
                         fn-bprv-article-arm-keeps-committed)
                       (theory 'minimal-theory)))))
(defthm fn-bprv-apply-store-event-keeps-idle
  (implies (and (fn-bprv-node-idlep node)
                (consp (fn-replay-apply-record node event)))
           (fn-bprv-node-idlep (fn-replay-apply-record node event)))
  :hints (("Goal"
           :in-theory (union-theories '(fn-replay-apply-record
                         fn-replay-apply-retention-event fn-replay-complete-retention
                         fn-replay-node-with-retention fn-replay-apply-identity-neutral
                         fn-bprv-advance-keeps-idle fn-bprv-node-make-state-fields
                         fn-bprv-durable-complete-unfolds)
                       (theory 'minimal-theory)))))

; The replay loop: an installed record stays committed, and every record of a
; successfully replayed list is committed in the result node.
(defthm fn-bprv-replay-fault-is-not-ok
  (not (fn-replay-okp (fn-replay-fault node sequence reason)))
  :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons fn-replay-okp fn-replay-fault fn-replay-result-kind)
                              (theory 'minimal-theory)))))
(defthm fn-bprv-replay-ok-node
  (equal (fn-replay-result-node (fn-replay-ok node sequence)) node)
  :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons fn-replay-ok fn-replay-result-node)
                                             (theory 'minimal-theory)))))
(defthm fn-bprv-replay-loop-keeps-committed
  (implies (and (fn-bpi-node-record-committedp node record)
                (fn-replay-okp (fn-replay-loop node records sequence)))
           (fn-bpi-node-record-committedp
            (fn-replay-result-node (fn-replay-loop node records sequence)) record))
  :hints (("Goal" :induct (fn-replay-loop node records sequence)
           :in-theory (union-theories '(car-cons cdr-cons fn-replay-loop fn-bprv-replay-fault-is-not-ok fn-bprv-replay-ok-node
                         fn-bprv-apply-store-event-keeps-committed fn-bprv-node-statep-consp
                         fn-bprv-committed-implies-node-statep)
                       (theory 'minimal-theory)))))
; `record' is an article record (`fn-record-p').  The history also carries
; retention and statement events, which install no article under their own
; name, so the conclusion is false of them: the hypothesis restates what the
; theorem always meant, and it is registered with PRF-007 (planning/proofs.json).
(defthm fn-bprv-replay-loop-installs-every-record
  (implies (and (fn-bprv-node-idlep node)
                (fn-replay-okp (fn-replay-loop node records sequence))
                (fn-record-p record)
                (member-equal record records))
           (fn-bpi-node-record-committedp
            (fn-replay-result-node (fn-replay-loop node records sequence)) record))
  :hints (("Goal" :induct (fn-replay-loop node records sequence)
           :in-theory (union-theories '(car-cons cdr-cons fn-replay-loop member-equal fn-bprv-replay-fault-is-not-ok
                         fn-bprv-replay-ok-node fn-bprv-apply-record-installs-record
                         fn-bprv-apply-store-event-keeps-idle
                         fn-bprv-replay-loop-keeps-committed fn-bprv-node-statep-consp
                         fn-bprv-committed-implies-node-statep)
                       (theory 'minimal-theory)))))

(defthm fn-bprv-node-initial-idle
  (fn-bprv-node-idlep (fn-node-initial-state groups capacity))
  :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons fn-bprv-node-idlep fn-node-initial-state
                                fn-node-make-state fn-node-stage)
                              (theory 'minimal-theory)))))
(defthm fn-bprv-advance-keeps-committed
  (implies (fn-bpi-node-record-committedp node record)
           (fn-bpi-node-record-committedp (fn-replay-advance-txid node recorded-txid) record))
  :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons fn-bpi-node-record-committedp
                                fn-replay-advance-keeps-committed-articles
                                fn-replay-advance-keeps-committed-bindings
                                fn-replay-advance-preserves-node-statep
                                fn-bprv-committed-implies-node-statep)
                              (theory 'minimal-theory)))))
(defthm fn-bprv-replay-node-commits-history-record
  (implies (and (consp (fn-sf-replay-node groups capacity history frontier))
                (fn-record-p record)
                (member-equal record history))
           (fn-bpi-node-record-committedp
            (fn-sf-replay-node groups capacity history frontier) record))
  :hints (("Goal"
           :use ((:instance fn-bprv-replay-loop-installs-every-record
                            (node (fn-node-initial-state groups capacity))
                            (records history) (sequence 0)))
           :in-theory (union-theories '(car-cons cdr-cons fn-sf-replay-node fn-replay fn-bprv-node-initial-idle
                         fn-bprv-advance-keeps-committed
                         ; fn-replay now tests the initial node once and returns a fault otherwise
                         ; (core, 2026-09-19); that branch closes by the record lemma
                         ; fn-replay-result-kind-of-fn-replay-fault under the opened recognizer.
                         fn-replay-okp fn-replay-result-kind-of-fn-replay-fault)
                       (theory 'minimal-theory)))))

(defthm fn-bprv-history-record-is-node-committed-when-idle
  (implies (and (fn-snt-relation store)
                (member-equal (fn-bprv-phase store) '(:ready :recovering :fenced-recovery))
                (fn-record-p record)
                (member-equal record (fn-bprv-history store)))
           (fn-bpi-node-record-committedp (fn-sn-node store) record))
  :hints (("Goal"
           :use ((:instance fn-snt-relation-implies-structural-state (s store))
                 (:instance fn-snt-typed-store-components (s store)))
           :in-theory (union-theories '(car-cons cdr-cons fn-bprv-phase fn-bprv-history
                         fn-snt-ready-or-recovered-node-is-exact-replay
                         fn-bprv-node-statep-consp
                         fn-bprv-replay-node-commits-history-record)
                       (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; The original node conclusion, under the relation the Store maintains instead
; of a :ready hypothesis on a positional argument (L20).

(defthm fn-bprv-evolving-output-is-node-grounded-when-idle
  (implies (and (fn-bprv-evolving-invariantp store st journal)
                (fn-snt-relation store)
                (member-equal (fn-bprv-phase store) '(:ready :recovering :fenced-recovery))
                (fn-bpr-receipt-adu st request))
           (fn-bpi-node-record-committedp
            (fn-sn-node store)
            (fn-bprv-find-grounding-record
             (fn-bpr-state-config st)
             (fn-bpr-find-context (fn-bpa-request-work-id request)
                                  (fn-bpr-state-contexts st))
             (fn-bprv-history store))))
  :hints (("Goal"
           :use (fn-bprv-evolving-output-is-history-grounded
                 (:instance fn-bprv-history-record-is-node-committed-when-idle
                            (record (fn-bprv-find-grounding-record
                                     (fn-bpr-state-config st)
                                     (fn-bpr-find-context (fn-bpa-request-work-id request)
                                                          (fn-bpr-state-contexts st))
                                     (fn-bprv-history store)))))
           :in-theory (theory 'minimal-theory))))

; -----------------------------------------------------------------------------
; The live gate carries to every ready related Store whose history extends the
; one it inspected.  This is what lets journal replay after a restart reproduce
; a decision taken against an earlier Store.

(defthm fn-bprv-acceptable-at-ready-extension
  (implies (and (fn-bpr-request-acceptablep s1 config record request authorized)
                (fn-sf-prefixp (fn-bprv-history s1) (fn-bprv-history s2))
                (fn-snt-relation s2)
                (equal (fn-bprv-phase s2) :ready))
           (fn-bpr-request-acceptablep s2 config record request authorized))
  :hints (("Goal"
           :use ((:instance fn-bprv-history-record-is-node-committed-when-idle (store s2))
                 (:instance fn-snt-relation-implies-structural-state (s s2))
                 (:instance fn-bprv-prefix-preserves-member
                            (h1 (fn-bprv-history s1)) (h2 (fn-bprv-history s2)) (x record)))
           :in-theory (union-theories '(car-cons cdr-cons fn-bpr-request-acceptablep fn-bpr-store-record-acceptedp
                         fn-bprv-history fn-bprv-phase member-equal)
                       (theory 'minimal-theory)))))
