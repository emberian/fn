; The receiver relation through Store evolution: every fn-sn-* transition,
; any interleaving with receiver steps, process restart through the observed
; reopen entry, and the live receiver trace the host runs
; (tools/run_bp_receive.py), whose state is the replay of its journal.
(in-package "ACL2")
(include-book "bp-receiver-evolving-node-invariants")
(include-book "store-observed-traces")
; codecs withdrew the record and cbor proof vocabularies at export (2026-09-19);
; this book reasons under them, so open them here, locally.
(local (in-theory (enable fn-record-record-vocabulary fn-record-codec-vocabulary fn-record-guard-vocabulary
                          fn-record-invariants-vocabulary fn-cbor-record-vocabulary
                          fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary)))
; withdrawn at the core export (2026-09-19); this book opened them before.
(local (in-theory (enable fn-node-statep fn-statep)))
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
(local (in-theory (disable fn-snt-relation fn-snt-step fn-snt-run fn-snrt-step fn-snrt-run
                           fn-sf-prefixp fn-sf-crash-imagep fn-sn-open-observed
                           fn-sn-open-okp fn-sn-open-state fn-sf-replay-node
                           fn-sf-history-recoverablep fn-node-statep fn-statep
                           fn-bprv-history fn-bprv-phase fn-bprv-history-relationalp
                           fn-bprv-evolving-invariantp fn-bprv-entries-decidedp
                           fn-bprv-contexts-groundedp fn-bprv-context-groundedp
                           fn-bpi-node-record-committedp
                           fn-sn-observed-configurationp fn-sn-observed-historyp)))

; -----------------------------------------------------------------------------
; Store-side monotonicity (L1, L2, L7).  fn-snrt-step covers every fn-sn-*
; transition the host runs between receiver calls: prepare, io, finish, crash,
; recover, refuse-reservation and known-abort (store-node-resolution-traces).

(defun fn-bprv-extendsp (old new)
  (fn-sf-prefixp (fn-bprv-history old) (fn-bprv-history new)))

(defthm fn-bprv-prefixp-reflexive
  (implies (true-listp h) (fn-sf-prefixp h h))
  :hints (("Goal" :in-theory (enable fn-sf-prefixp))))
(defthm fn-bprv-prefixp-of-append
  (implies (true-listp h) (fn-sf-prefixp h (append h more)))
  :hints (("Goal" :in-theory (enable fn-sf-prefixp))))
(defthm fn-bprv-related-history-true-list
  (implies (fn-snt-relation s) (true-listp (fn-bprv-history s)))
  :hints (("Goal" :use fn-snt-related-records-true-list
           :in-theory (e/d (fn-bprv-history) (fn-snt-related-records-true-list)))))
(defthm fn-bprv-snrt-step-extends-history
  (implies (fn-snt-relation s)
           (fn-bprv-extendsp s (fn-snrt-step s event)))
  :hints (("Goal" :use fn-snrt-step-records-prefix
           :in-theory (e/d (fn-bprv-history) (fn-snrt-step-records-prefix)))))
(defthm fn-bprv-snrt-run-extends-history
  (implies (fn-snt-relation s)
           (fn-bprv-extendsp s (fn-snrt-run s events)))
  :hints (("Goal" :use fn-snrt-mixed-trace-records-prefix
           :in-theory (e/d (fn-bprv-history) (fn-snrt-mixed-trace-records-prefix)))))
(defthm fn-bprv-extendsp-transitive
  (implies (and (fn-bprv-extendsp a b) (fn-bprv-extendsp b c))
           (fn-bprv-extendsp a c))
  :rule-classes ((:rewrite :match-free :all))
  :hints (("Goal" :use ((:instance fn-sf-prefixp-transitive
                                   (xs (fn-bprv-history a)) (ys (fn-bprv-history b))
                                   (zs (fn-bprv-history c)))))))
(local (in-theory (disable fn-bprv-extendsp)))

(defthm fn-bprv-store-step-preserves-evolving-invariant
  (implies (and (fn-snt-relation store)
                (fn-bprv-evolving-invariantp store st journal))
           (fn-bprv-evolving-invariantp (fn-snrt-step store event) st journal))
  :hints (("Goal" :use ((:instance fn-bprv-snrt-step-extends-history (s store))
                        (:instance fn-bprv-history-relational-monotone
                                   (h1 (fn-bprv-history store))
                                   (h2 (fn-bprv-history (fn-snrt-step store event)))))
           :in-theory (e/d (fn-bprv-evolving-invariantp fn-bprv-extendsp)
                           (fn-bprv-snrt-step-extends-history
                            fn-bprv-history-relational-monotone)))))
(defthm fn-bprv-store-run-preserves-evolving-invariant
  (implies (and (fn-snt-relation store)
                (fn-bprv-evolving-invariantp store st journal))
           (fn-bprv-evolving-invariantp (fn-snrt-run store events) st journal))
  :hints (("Goal" :use ((:instance fn-bprv-snrt-run-extends-history (s store))
                        (:instance fn-bprv-history-relational-monotone
                                   (h1 (fn-bprv-history store))
                                   (h2 (fn-bprv-history (fn-snrt-run store events)))))
           :in-theory (e/d (fn-bprv-evolving-invariantp fn-bprv-extendsp)
                           (fn-bprv-snrt-run-extends-history
                            fn-bprv-history-relational-monotone)))))
(defthm fn-bprv-grounding-record-survives-store-run
  (implies (and (fn-snt-relation store)
                (member-equal record (fn-bprv-history store)))
           (member-equal record (fn-bprv-history (fn-snrt-run store events))))
  :hints (("Goal" :use ((:instance fn-bprv-snrt-run-extends-history (s store))
                        (:instance fn-bprv-prefix-preserves-member
                                   (h1 (fn-bprv-history store))
                                   (h2 (fn-bprv-history (fn-snrt-run store events)))
                                   (x record)))
           :in-theory (e/d (fn-bprv-extendsp)
                           (fn-bprv-snrt-run-extends-history
                            fn-bprv-prefix-preserves-member)))))

; -----------------------------------------------------------------------------
; Interleaving (L13, L14).  A system state is (store st); an event is a Store
; event or a receiver journal record.  fn-bprv-system-invariantp carries the
; Store's own live-history relation alongside the receiver relation.

(defun fn-bprv-system-step (store st event)
  (case (car event)
    (:store (list (fn-snrt-step store (cadr event)) st))
    (:receiver (list store (cadr (fn-bprr-apply-record st store (cadr event)))))
    (otherwise (list store st))))
(defun fn-bprv-system-run (store st events)
  (if (consp events)
      (let ((next (fn-bprv-system-step store st (car events))))
        (fn-bprv-system-run (car next) (cadr next) (cdr events)))
    (list store st)))
(defun fn-bprv-system-events-journaledp (events journal)
  (if (consp events)
      (and (or (not (equal (car (car events)) :receiver))
               (member-equal (cadr (car events)) journal))
           (fn-bprv-system-events-journaledp (cdr events) journal))
    t))
(defun fn-bprv-system-invariantp (store st journal)
  (and (fn-snt-relation store)
       (fn-bprv-evolving-invariantp store st journal)))

(defthm fn-bprv-system-step-preserves-invariant
  (implies (and (fn-bprv-system-invariantp store st journal)
                (or (not (equal (car event) :receiver))
                    (member-equal (cadr event) journal)))
           (let ((next (fn-bprv-system-step store st event)))
             (fn-bprv-system-invariantp (car next) (cadr next) journal)))
  :hints (("Goal" :in-theory (disable fn-bprr-apply-record))))
(defthm fn-bprv-system-run-preserves-invariant
  (implies (and (fn-bprv-system-invariantp store st journal)
                (fn-bprv-system-events-journaledp events journal))
           (let ((final (fn-bprv-system-run store st events)))
             (fn-bprv-system-invariantp (car final) (cadr final) journal)))
  :hints (("Goal" :induct (fn-bprv-system-run store st events)
           :in-theory (disable fn-bprv-system-invariantp fn-bprv-system-step))))

; -----------------------------------------------------------------------------
; Process restart (L22).  The host reopens through fn-sn-open-observed
; (host/store-node-host.lisp:27); A-DURABILITY enters as fn-sf-crash-imagep,
; exactly as in store-observed-traces (D5).  The receiver state is whatever
; the next fn-bprj-install replays; here it is the pre-crash state, and the
; theorem below says the invariant still holds against the reopened Store.

(defthm fn-bprv-crash-image-extends-history
  (implies (fn-sf-crash-imagep (fn-sn-files s) frontier records)
           (fn-sf-prefixp (fn-bprv-history s) records))
  :hints (("Goal" :use ((:instance fn-sf-admissible-image-facts (s (fn-sn-files s)))
                        (:instance fn-sf-state-records-are-true-list (s (fn-sn-files s))))
           :in-theory (e/d (fn-sf-crash-imagep fn-bprv-history)
                           (fn-sf-admissible-image-facts fn-sf-state-records-are-true-list
                            fn-sf-statep fn-sf-frontier-new-visiblep
                            fn-sf-record-present-visiblep)))))

(defthm fn-bprv-observed-reopen-facts
  (implies (and (fn-snt-relation s)
                (fn-sf-crash-imagep (fn-sn-files s) frontier records))
           (let ((opened (fn-sn-open-observed (fn-sn-groups s) (fn-sn-capacity s)
                                              frontier records)))
             (and (fn-sn-open-okp opened)
                  (fn-snt-relation (fn-sn-open-state opened))
                  (equal (fn-bprv-history (fn-sn-open-state opened)) records)
                  (fn-bprv-extendsp s (fn-sn-open-state opened)))))
  :hints (("Goal"
           :use (fn-snt-relation-implies-observed-configuration
                 fn-snt-admissible-crash-image-is-recoverable
                 fn-bprv-crash-image-extends-history
                 (:instance fn-sf-admissible-image-facts (s (fn-sn-files s)))
                 (:instance fn-sn-open-observed-succeeds-on-recoverable-image
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s)))
                 (:instance fn-sn-open-observed-success-has-live-history-relation
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s)))
                 (:instance fn-sn-open-observed-success-exact-history
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))))
           :in-theory (e/d (fn-sn-observed-historyp fn-bprv-extendsp fn-bprv-history)
                           (fn-snt-relation-implies-observed-configuration
                            fn-snt-admissible-crash-image-is-recoverable
                            fn-bprv-crash-image-extends-history
                            fn-sf-admissible-image-facts
                            fn-sn-open-observed-succeeds-on-recoverable-image
                            fn-sn-open-observed-success-has-live-history-relation
                            fn-sn-open-observed-success-exact-history
                            fn-sf-statep fn-sf-record-listp fn-sf-records)))))

(defthm fn-bprv-evolving-invariant-survives-observed-reopen
  (implies (and (fn-bprv-system-invariantp store st journal)
                (fn-sf-crash-imagep (fn-sn-files store) frontier records))
           (let ((opened (fn-sn-open-observed (fn-sn-groups store) (fn-sn-capacity store)
                                              frontier records)))
             (and (fn-sn-open-okp opened)
                  (fn-bprv-system-invariantp (fn-sn-open-state opened) st journal))))
  :hints (("Goal" :use ((:instance fn-bprv-observed-reopen-facts (s store))
                        (:instance fn-bprv-history-relational-monotone
                                   (h1 (fn-bprv-history store))
                                   (h2 (fn-bprv-history
                                        (fn-sn-open-state
                                         (fn-sn-open-observed (fn-sn-groups store)
                                                              (fn-sn-capacity store)
                                                              frontier records))))))
           :in-theory (e/d (fn-bprv-evolving-invariantp fn-bprv-extendsp)
                           (fn-bprv-observed-reopen-facts
                            fn-bprv-history-relational-monotone)))))

; -----------------------------------------------------------------------------
; The live receiver trace (tools/run_bp_receive.py).  A live state is
; (store st journal): the Store global fn-store-sn, the receiver global
; fn-bprj-state, and the receiver journal on disk.  The host's calls, in
; order: open_live_bp_store (line 134; fn-sn-open-observed then barriers),
; receipt_journal.open (line 138; fn-bprj-install, host line 12, replays the
; journal against the current Store), Store ingress (lines 210-217; fn-sn-io,
; fn-sn-prepare, fn-sn-finish through the bridge), accept_request (line 218)
; and _durably_decide (lines 92-95), each a fn-bprj-apply (host line 22) of
; one record after fn-bprj-preflight (host line 18) against the same Store and
; state (tools/receipt_journal.py lines 56-79: preflight, durable write,
; apply).  The journal therefore holds exactly the records fn-bprj-apply
; accepted; fn-bprj-receipt-adu (host line 38) is a query of fn-bprj-state.

(defun fn-bpr-live-store (live) (car live))
(defun fn-bpr-live-state (live) (cadr live))
(defun fn-bpr-live-journal (live) (caddr live))
(defun fn-bpr-live-step (live event)
  (let ((store (car live)) (st (cadr live)) (journal (caddr live)))
    (case (car event)
      (:store (list (fn-snrt-step store (cadr event)) st journal))
      (:apply (let ((answer (fn-bprr-apply-record st store (cadr event))))
                (if (car answer)
                    (list store (cadr answer) (append journal (list (cadr event))))
                  (list store st journal))))
      (otherwise (list store st journal)))))
(defun fn-bpr-live-run (live events)
  (if (consp events)
      (fn-bpr-live-run (fn-bpr-live-step live (car events)) (cdr events))
    live))
; fn-bprj-install: the receiver state is the replay of the journal against the
; Store the process holds.
(defun fn-bpr-live-install (store journal)
  (list store (cadr (fn-bprr-replay store journal)) journal))

(defthm fn-bpr-live-step-preserves-store-relation
  (implies (fn-snt-relation (car live))
           (fn-snt-relation (car (fn-bpr-live-step live event))))
  :hints (("Goal" :in-theory (disable fn-bprr-apply-record))))
(defthm fn-bpr-live-step-extends-history
  (implies (fn-snt-relation (car live))
           (fn-bprv-extendsp (car live) (car (fn-bpr-live-step live event))))
  :hints (("Goal" :use ((:instance fn-bprv-snrt-step-extends-history (s (car live))
                                   (event (cadr event))))
           :in-theory (e/d (fn-bprv-extendsp) (fn-bprr-apply-record
                                               fn-bprv-snrt-step-extends-history)))))
(defthm fn-bpr-live-run-preserves-store-relation
  (implies (fn-snt-relation (car live))
           (fn-snt-relation (car (fn-bpr-live-run live events))))
  :hints (("Goal" :induct (fn-bpr-live-run live events)
           :in-theory (disable fn-bpr-live-step))))
(defthm fn-bpr-live-run-extends-from
  (implies (and (fn-snt-relation (car live))
                (fn-bprv-extendsp base (car live)))
           (fn-bprv-extendsp base (car (fn-bpr-live-run live events))))
  :hints (("Goal" :induct (fn-bpr-live-run live events)
           :in-theory (disable fn-bpr-live-step))))
(defthm fn-bpr-live-run-extends-history
  (implies (fn-snt-relation (car live))
           (fn-bprv-extendsp (car live) (car (fn-bpr-live-run live events))))
  :hints (("Goal" :use ((:instance fn-bpr-live-run-extends-from (base (car live))))
           :in-theory (e/d (fn-bprv-extendsp)
                           (fn-bpr-live-run-extends-from fn-bpr-live-run)))))

; Replay of an appended journal is replay of the prefix continued.
(defthm fn-bprv-replay-rest-nil
  (equal (fn-bprr-replay-rest st store nil) (list t st))
  :hints (("Goal" :in-theory (enable fn-bprr-replay-rest))))
(defthm fn-bprv-replay-rest-single
  (equal (fn-bprr-replay-rest st store (list r))
         (let ((answer (fn-bprr-apply-record st store r)))
           (if (car answer) (list t (cadr answer)) (list nil st))))
  :hints (("Goal" :in-theory (enable fn-bprr-replay-rest))))
(defthm fn-bprv-replay-rest-append
  (equal (fn-bprr-replay-rest st store (append a b))
         (let ((answer (fn-bprr-replay-rest st store a)))
           (if (car answer) (fn-bprr-replay-rest (cadr answer) store b) answer)))
  :hints (("Goal" :induct (fn-bprr-replay-rest st store a)
           :in-theory (enable fn-bprr-replay-rest))))

; A receiver step taken against the live Store is the step replay takes
; against any ready related Store whose history extends the live one.
(defthm fn-bprv-apply-record-agrees-at-ready-extension
  (implies (and (car (fn-bprr-apply-record st s1 r))
                (fn-sf-prefixp (fn-bprv-history s1) (fn-bprv-history s2))
                (fn-snt-relation s2)
                (equal (fn-bprv-phase s2) :ready))
           (equal (fn-bprr-apply-record st s2 r) (fn-bprr-apply-record st s1 r)))
  :hints (("Goal" :in-theory (enable fn-bprr-apply-record fn-bpr-accept-request))))

(defthm fn-bpr-live-step-replays
  (implies (and (fn-snt-relation (car live))
                (equal (fn-bprr-replay probe (caddr live)) (list t (cadr live)))
                (fn-snt-relation probe)
                (equal (fn-bprv-phase probe) :ready)
                (fn-bprv-extendsp (car live) probe))
           (equal (fn-bprr-replay probe (caddr (fn-bpr-live-step live event)))
                  (list t (cadr (fn-bpr-live-step live event)))))
  :hints (("Goal"
           :use ((:instance fn-bprv-apply-record-agrees-at-ready-extension
                            (st (cadr live)) (s1 (car live)) (s2 probe) (r (cadr event))))
           :in-theory (e/d (fn-bprr-replay fn-bprv-extendsp)
                           (fn-bprv-apply-record-agrees-at-ready-extension
                            fn-bprr-apply-record)))))

; The live receiver state is the replay of its journal against every ready
; related Store whose history extends the final live Store: a restart that
; reopens such a Store and runs fn-bprj-install recovers the live state.
(defthm fn-bpr-live-state-is-replay-of-journal
  (let ((final (fn-bpr-live-run live events)))
    (implies (and (fn-snt-relation (car live))
                  (equal (fn-bprr-replay probe (caddr live)) (list t (cadr live)))
                  (fn-snt-relation probe)
                  (equal (fn-bprv-phase probe) :ready)
                  (fn-bprv-extendsp (car final) probe))
             (equal (fn-bprr-replay probe (caddr final)) (list t (cadr final)))))
  :hints (("Goal" :induct (fn-bpr-live-run live events)
           :in-theory (disable fn-bpr-live-step fn-bpr-live-step-replays
                               fn-bprv-extendsp-transitive
                               fn-bpr-live-run-extends-history))
          ("Subgoal *1/2" :use ((:instance fn-bpr-live-step-replays (event (car events)))
                 (:instance fn-bpr-live-run-extends-history
                            (live (fn-bpr-live-step live (car events)))
                            (events (cdr events)))
                 (:instance fn-bprv-extendsp-transitive
                            (a (car (fn-bpr-live-step live (car events))))
                            (b (car (fn-bpr-live-run (fn-bpr-live-step live (car events))
                                                     (cdr events))))
                            (c probe))
                 (:instance fn-bprv-extendsp-transitive
                            (a (car live))
                            (b (car (fn-bpr-live-step live (car events))))
                            (c probe)))
           :in-theory (disable fn-bpr-live-step fn-bpr-live-step-replays
                               fn-bprv-extendsp-transitive
                               fn-bpr-live-run-extends-history))
          ("Subgoal *1/1" :use ((:instance fn-bpr-live-step-replays (event (car events)))
                 (:instance fn-bpr-live-run-extends-history
                            (live (fn-bpr-live-step live (car events)))
                            (events (cdr events)))
                 (:instance fn-bprv-extendsp-transitive
                            (a (car (fn-bpr-live-step live (car events))))
                            (b (car (fn-bpr-live-run (fn-bpr-live-step live (car events))
                                                     (cdr events))))
                            (c probe))
                 (:instance fn-bprv-extendsp-transitive
                            (a (car live))
                            (b (car (fn-bpr-live-step live (car events))))
                            (c probe)))
           :in-theory (disable fn-bpr-live-step fn-bpr-live-step-replays
                               fn-bprv-extendsp-transitive
                               fn-bpr-live-run-extends-history))))

; A successful replay against one Store is the same replay against every ready
; related Store whose history extends it: the journal fn-bprj-install reads
; after a restart reproduces the state a live process held.
(defthm fn-bprv-replay-rest-agrees-at-ready-extension
  (implies (and (car (fn-bprr-replay-rest st s1 records))
                (fn-sf-prefixp (fn-bprv-history s1) (fn-bprv-history s2))
                (fn-snt-relation s2)
                (equal (fn-bprv-phase s2) :ready))
           (equal (fn-bprr-replay-rest st s2 records)
                  (fn-bprr-replay-rest st s1 records)))
  :hints (("Goal" :induct (fn-bprr-replay-rest st s1 records)
           :in-theory (e/d (fn-bprr-replay-rest) (fn-bprr-apply-record)))))
(defthm fn-bprv-replay-agrees-at-ready-extension
  (implies (and (car (fn-bprr-replay s1 records))
                (fn-sf-prefixp (fn-bprv-history s1) (fn-bprv-history s2))
                (fn-snt-relation s2)
                (equal (fn-bprv-phase s2) :ready))
           (equal (fn-bprr-replay s2 records) (fn-bprr-replay s1 records)))
  :hints (("Goal" :in-theory (e/d (fn-bprr-replay)
                                  (fn-bprr-apply-record fn-bprr-replay-rest)))))

; Byte-identical receipt after restart, as a theorem.  From a receiver whose
; state is the replay of its journal against the related Store it opened
; (fn-bprj-install), run any live trace; crash to any admissible image; reopen
; through the host's entry; run any further Store trace that reaches :ready
; (the recovery barriers); then fn-bprj-install replays the journal and the
; ADU fn-bprj-receipt-adu regenerates is the one the live receiver held.
(defthm fn-bpr-live-receipt-regenerated-after-restart
  (let* ((final (fn-bpr-live-run live events))
         (opened (fn-sn-open-observed (fn-sn-groups (car final)) (fn-sn-capacity (car final))
                                      frontier records))
         (probe (fn-snrt-run (fn-sn-open-state opened) recovery-events))
         (installed (fn-bpr-live-install probe (caddr final))))
    (implies (and (fn-snt-relation (car live))
                  (equal (fn-bprr-replay (car live) (caddr live)) (list t (cadr live)))
                  (fn-sf-crash-imagep (fn-sn-files (car final)) frontier records)
                  (equal (fn-bprv-phase probe) :ready))
             (and (fn-sn-open-okp opened)
                  (equal (cadr installed) (cadr final))
                  (equal (fn-bpr-receipt-adu (cadr installed) request)
                         (fn-bpr-receipt-adu (cadr final) request)))))
  :hints (("Goal"
           :use ((:instance fn-bprv-observed-reopen-facts (s (car (fn-bpr-live-run live events))))
                 (:instance fn-bprv-crash-image-extends-history
                            (s (car (fn-bpr-live-run live events))))
                 (:instance fn-sf-prefixp-transitive
                            (xs (fn-bprv-history (car (fn-bpr-live-run live events))))
                            (ys records)
                            (zs (fn-bprv-history (fn-snrt-run
                                 (fn-sn-open-state
                                  (fn-sn-open-observed
                                   (fn-sn-groups (car (fn-bpr-live-run live events)))
                                   (fn-sn-capacity (car (fn-bpr-live-run live events)))
                                   frontier records))
                                 recovery-events))))
                 (:instance fn-sf-prefixp-transitive
                            (xs (fn-bprv-history (car live)))
                            (ys (fn-bprv-history (car (fn-bpr-live-run live events))))
                            (zs (fn-bprv-history (fn-snrt-run
                                 (fn-sn-open-state
                                  (fn-sn-open-observed
                                   (fn-sn-groups (car (fn-bpr-live-run live events)))
                                   (fn-sn-capacity (car (fn-bpr-live-run live events)))
                                   frontier records))
                                 recovery-events))))
                 (:instance fn-bpr-live-run-preserves-store-relation)
                 (:instance fn-bpr-live-run-extends-history)
                 (:instance fn-bpr-live-state-is-replay-of-journal
                            (probe (fn-snrt-run
                                    (fn-sn-open-state
                                     (fn-sn-open-observed
                                      (fn-sn-groups (car (fn-bpr-live-run live events)))
                                      (fn-sn-capacity (car (fn-bpr-live-run live events)))
                                      frontier records))
                                    recovery-events)))
                 (:instance fn-bprv-replay-agrees-at-ready-extension
                            (s1 (car live))
                            (s2 (fn-snrt-run
                                 (fn-sn-open-state
                                  (fn-sn-open-observed
                                   (fn-sn-groups (car (fn-bpr-live-run live events)))
                                   (fn-sn-capacity (car (fn-bpr-live-run live events)))
                                   frontier records))
                                 recovery-events))
                            (records (caddr live)))
                 (:instance fn-bprv-extendsp-transitive
                            (a (car live))
                            (b (car (fn-bpr-live-run live events)))
                            (c (fn-snrt-run
                                (fn-sn-open-state
                                 (fn-sn-open-observed
                                  (fn-sn-groups (car (fn-bpr-live-run live events)))
                                  (fn-sn-capacity (car (fn-bpr-live-run live events)))
                                  frontier records))
                                recovery-events)))
                 (:instance fn-bprv-snrt-run-extends-history
                            (s (fn-sn-open-state
                                (fn-sn-open-observed
                                 (fn-sn-groups (car (fn-bpr-live-run live events)))
                                 (fn-sn-capacity (car (fn-bpr-live-run live events)))
                                 frontier records)))
                            (events recovery-events))
                 (:instance fn-snrt-mixed-trace-preserves-live-history-relation
                            (s (fn-sn-open-state
                                (fn-sn-open-observed
                                 (fn-sn-groups (car (fn-bpr-live-run live events)))
                                 (fn-sn-capacity (car (fn-bpr-live-run live events)))
                                 frontier records)))
                            (events recovery-events))
                 (:instance fn-bprv-extendsp-transitive
                            (a (car (fn-bpr-live-run live events)))
                            (b (fn-sn-open-state
                                (fn-sn-open-observed
                                 (fn-sn-groups (car (fn-bpr-live-run live events)))
                                 (fn-sn-capacity (car (fn-bpr-live-run live events)))
                                 frontier records)))
                            (c (fn-snrt-run
                                (fn-sn-open-state
                                 (fn-sn-open-observed
                                  (fn-sn-groups (car (fn-bpr-live-run live events)))
                                  (fn-sn-capacity (car (fn-bpr-live-run live events)))
                                  frontier records))
                                recovery-events))))
           :in-theory (e/d (fn-bprv-extendsp)
                           (fn-bprv-observed-reopen-facts
                            fn-bpr-live-run-preserves-store-relation
                            fn-bpr-live-run-extends-history
                            fn-bpr-live-state-is-replay-of-journal
                            fn-bprv-replay-agrees-at-ready-extension
                            fn-bprv-snrt-run-extends-history
                            fn-snrt-mixed-trace-preserves-live-history-relation
                            fn-bprv-extendsp-transitive fn-bpr-live-run
                            fn-bprv-crash-image-extends-history fn-sf-prefixp-transitive
                            fn-bprr-replay fn-bpr-receipt-adu)))))
