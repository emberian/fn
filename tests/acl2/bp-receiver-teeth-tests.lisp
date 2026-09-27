; Teeth for the receiver grounding keystone.
;
; The 2026-09-18 review §5: "`fn-bprv-replayed-receipt-is-grounded': one
; hypothesis, twelve conjuncts tying emitted receipt bytes to a ready Store
; record and node binding, with three separating witnesses."  One hypothesis,
; so one case -- but the conclusion is a twelve-way conjunction, so the case is
; written out in full rather than as the one conjunct that happens to break.
; Two different violations are given, breaking different conjuncts.

(in-package "ACL2")
(include-book "../../books/bp-receiver-retention-invariants")
(include-book "bp-receipt-records-tests")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/codec-attach")
; codecs withdrew the record and cbor proof vocabularies at export (2026-09-19);
; this book reasons under them, so open them here, locally.
(local (in-theory (enable fn-record-record-vocabulary fn-record-codec-vocabulary fn-record-guard-vocabulary
                          fn-record-invariants-vocabulary fn-cbor-record-vocabulary
                          fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary)))

; -----------------------------------------------------------------------------
; A reachable, non-degenerate witness.
;
; The Store is the one the host actually resumes from: crashed, recovered
; through all five barriers, and ready.  The journal is the full four-record
; sequence, so the receipt bytes are reconstructed from disk rather than from
; a live in-process decision.

(make-event `(defconst *bprt-journal* ',(list *bprr-config-record* *bprr-request-record*
        *bprr-intent-record* *bprr-decision-record*)))
(bpr-lift fn-bprr-replay 2)
(bpr-lift fn-bprv-find-record 4)

(make-event `(defconst *bprt-state* ',(cadr (in-arena-fn-bprr-replay *bpr-payloads* *bpr-recovered-ready-store* *bprt-journal*))))

(assert-event (car (in-arena-fn-bprr-replay *bpr-payloads* *bpr-recovered-ready-store* *bprt-journal*)))
(assert-event (fn-sn-statep *bpr-recovered-ready-store*))
(assert-event (equal (fn-sf-phase (fn-sn-files *bpr-recovered-ready-store*)) :ready))

; The receipt is emitted, and it is the same bytes the live receiver produced
; before the crash: replay is not a second, weaker path to the same claim.
(assert-event (fn-bpr-receipt-adu *bprt-state* *bpr-request*))
(assert-event (equal (fn-bpr-receipt-adu *bprt-state* *bpr-request*) *bpr-receipt-adu*))

; Non-degenerate: the context reconstructed from the journal is exactly the one
; derived from the stored record and the request, and the request's article and
; subject are the record's payload and content subject -- three distinct
; identities that a witness conflating them would not separate.
(make-event `(defconst *bprt-context* ',(fn-bpr-find-context (fn-bpa-request-work-id *bpr-request*)
                       (fn-bpr-state-contexts *bprt-state*))))
(make-event `(defconst *bprt-record* ',(in-arena-fn-bprv-find-record *bpr-payloads* *bpr-recovered-ready-store* (fn-bpr-state-config *bprt-state*) *bprt-context* (fn-sf-records (fn-sn-files *bpr-recovered-ready-store*)))))
(assert-event (fn-record-p *bprt-record*))
;; The found record is the WIRE form of the retained row (records-flip).
(bpr-lift fn-bpi-node-wire-committedp 2)
(bpr-lift fn-bpr-rows-stand-for 2)

(assert-event
 (in-arena-fn-bpr-rows-stand-for *bpr-payloads* *bprt-record* (fn-sf-records (fn-sn-files *bpr-recovered-ready-store*))))
(assert-event (equal *bprt-record* *bpr-record*))
(assert-event
 (in-arena-fn-bpi-node-wire-committedp *bpr-payloads* (fn-sn-node *bpr-recovered-ready-store*) *bprt-record*))
(assert-event
 (equal *bprt-context* (fn-bpr-context-from-request *bprt-record* *bpr-request*)))
(assert-event
 (equal (fn-bpa-request-article *bpr-request*) (fn-record-payload *bprt-record*)))
(assert-event
 (equal (fn-bpa-request-subject *bpr-request*)
        (fn-record-content-subject *bprt-record*)))
(assert-event
 (not (equal (fn-bpa-request-subject *bpr-request*)
             (fn-record-msgid *bprt-record*))))

; The context holds the request by REFERENCE (PKT-646): its reference is the
; request's, it holds no copy of the article, and it resolves over the
; grounding record's payload to exactly the request.
(assert-event
 (and (equal (fn-bpr-context-request-ref *bprt-context*)
             (fn-bpaj-request-ref *bpr-request*))
      (not (member-equal (fn-bpa-request-article *bpr-request*)
                         (fn-bpr-context-request-ref *bprt-context*)))
      (equal (fn-bpr-context-resolve *bprt-context* *bprt-record*)
             *bpr-request*)))

; -----------------------------------------------------------------------------
; Teeth for `fn-bprv-replayed-receipt-is-grounded'
;
; The sole hypothesis is `(fn-bpr-receipt-adu st request)'.  Both cases below
; violate it and state the whole twelve-conjunct conclusion, so nothing is
; hidden by picking a convenient conjunct.

; Case 1: the Store the journal is replayed against is still recovering.  No
; receipt is emitted, and the conclusion's ready-phase conjunct is false, which
; is the point -- receipt bytes may not be grounded in a Store that has not
; finished its barriers.
(assert-event
 (null (fn-bpr-receipt-adu
        (cadr (in-arena-fn-bprr-replay *bpr-payloads* *bpr-recovering-store* *bprt-journal*))
        *bpr-request*)))
(assert-event
 (not (equal (fn-sf-phase (fn-sn-files *bpr-recovering-store*)) :ready)))

(local
 (must-fail
  (defthm bprt-teeth-grounded-without-an-unready-store
    (let* ((store *bpr-recovering-store*)
           (records *bprt-journal*)
           (request *bpr-request*)
           (st (cadr (fn-bprr-replay store records fn-arena)))
           (context (fn-bpr-find-context (fn-bpa-request-work-id request)
                                         (fn-bpr-state-contexts st)))
           (entry (fn-bpr-find-receipt (fn-bpr-context-work-id context)
                                       (fn-bpr-state-receipts st)))
           (record (fn-bprv-find-record store (fn-bpr-state-config st) context
                                        (fn-sf-records (fn-sn-files store)) fn-arena)))
      (and (fn-sn-statep store)
           (equal (fn-sf-phase (fn-sn-files store)) :ready)
           (fn-record-p record)
           (member-equal record (fn-sf-records (fn-sn-files store)))
           (fn-bpi-node-record-committedp (fn-sn-node store) record)
           (equal (fn-bpaj-request-ref request)
                  (fn-bpr-context-request-ref context))
           (equal context (fn-bpr-context-from-request
                           record (fn-bpr-context-resolve context record)))
           (equal (fn-bpa-request-article (fn-bpr-context-resolve context record))
                  (fn-record-payload record))
           (equal (fn-bpa-request-subject (fn-bpr-context-resolve context record))
                  (fn-record-content-subject record))
           (member-equal entry (fn-bpr-state-receipts st))
           (fn-bprv-entry-decidedp entry records)
           (equal (fn-bpr-receipt-entry-receipt entry)
                  (fn-bpr-receipt-for context (fn-bpr-state-config st)
                                      (fn-bpa-receipt-id
                                       (fn-bpr-receipt-entry-receipt entry))))
           (equal (fn-bpr-receipt-adu st request)
                  (fn-bpa-encode (fn-bpr-receipt-entry-receipt entry))))))))
(assert-event (not (let* ((store *bpr-recovering-store*)
           (records *bprt-journal*)
           (request *bpr-request*)
           (st (cadr (in-arena-fn-bprr-replay *bpr-payloads* store records)))
           (context (fn-bpr-find-context (fn-bpa-request-work-id request)
                                         (fn-bpr-state-contexts st)))
           (entry (fn-bpr-find-receipt (fn-bpr-context-work-id context)
                                       (fn-bpr-state-receipts st)))
           (record (in-arena-fn-bprv-find-record *bpr-payloads* store (fn-bpr-state-config st) context (fn-sf-records (fn-sn-files store)))))
      (and (fn-sn-statep store)
           (equal (fn-sf-phase (fn-sn-files store)) :ready)
           (fn-record-p record)
           (member-equal record (fn-sf-records (fn-sn-files store)))
           (fn-bpi-node-record-committedp (fn-sn-node store) record)
           (equal (fn-bpaj-request-ref request)
                  (fn-bpr-context-request-ref context))
           (equal context (fn-bpr-context-from-request
                           record (fn-bpr-context-resolve context record)))
           (equal (fn-bpa-request-article (fn-bpr-context-resolve context record))
                  (fn-record-payload record))
           (equal (fn-bpa-request-subject (fn-bpr-context-resolve context record))
                  (fn-record-content-subject record))
           (member-equal entry (fn-bpr-state-receipts st))
           (fn-bprv-entry-decidedp entry records)
           (equal (fn-bpr-receipt-entry-receipt entry)
                  (fn-bpr-receipt-for context (fn-bpr-state-config st)
                                      (fn-bpa-receipt-id
                                       (fn-bpr-receipt-entry-receipt entry))))
           (equal (fn-bpr-receipt-adu st request)
                  (fn-bpa-encode (fn-bpr-receipt-entry-receipt entry))))))) ; evaluation witness for bprt-teeth-grounded-without-an-unready-store

; Case 2: a ready Store, but the journal stops after the receipt intent with no
; committed decision.  No receipt is emitted, and the conclusion's
; entry-decided conjunct is false: an intent is not a decision, and bytes may
; not be produced from one.
(make-event `(defconst *bprt-intent-only* ',(list *bprr-config-record* *bprr-request-record* *bprr-intent-record*)))
(assert-event
 (null (fn-bpr-receipt-adu
        (cadr (in-arena-fn-bprr-replay *bpr-payloads* *bpr-recovered-ready-store* *bprt-intent-only*))
        *bpr-request*)))

(local
 (must-fail
  (defthm bprt-teeth-grounded-without-a-committed-decision
    (let* ((store *bpr-recovered-ready-store*)
           (records *bprt-intent-only*)
           (request *bpr-request*)
           (st (cadr (fn-bprr-replay store records fn-arena)))
           (context (fn-bpr-find-context (fn-bpa-request-work-id request)
                                         (fn-bpr-state-contexts st)))
           (entry (fn-bpr-find-receipt (fn-bpr-context-work-id context)
                                       (fn-bpr-state-receipts st)))
           (record (fn-bprv-find-record store (fn-bpr-state-config st) context
                                        (fn-sf-records (fn-sn-files store)) fn-arena)))
      (and (fn-sn-statep store)
           (equal (fn-sf-phase (fn-sn-files store)) :ready)
           (fn-record-p record)
           (member-equal record (fn-sf-records (fn-sn-files store)))
           (fn-bpi-node-record-committedp (fn-sn-node store) record)
           (equal (fn-bpaj-request-ref request)
                  (fn-bpr-context-request-ref context))
           (equal context (fn-bpr-context-from-request
                           record (fn-bpr-context-resolve context record)))
           (equal (fn-bpa-request-article (fn-bpr-context-resolve context record))
                  (fn-record-payload record))
           (equal (fn-bpa-request-subject (fn-bpr-context-resolve context record))
                  (fn-record-content-subject record))
           (member-equal entry (fn-bpr-state-receipts st))
           (fn-bprv-entry-decidedp entry records)
           (equal (fn-bpr-receipt-entry-receipt entry)
                  (fn-bpr-receipt-for context (fn-bpr-state-config st)
                                      (fn-bpa-receipt-id
                                       (fn-bpr-receipt-entry-receipt entry))))
           (equal (fn-bpr-receipt-adu st request)
                  (fn-bpa-encode (fn-bpr-receipt-entry-receipt entry))))))))
(assert-event (not (let* ((store *bpr-recovered-ready-store*)
           (records *bprt-intent-only*)
           (request *bpr-request*)
           (st (cadr (in-arena-fn-bprr-replay *bpr-payloads* store records)))
           (context (fn-bpr-find-context (fn-bpa-request-work-id request)
                                         (fn-bpr-state-contexts st)))
           (entry (fn-bpr-find-receipt (fn-bpr-context-work-id context)
                                       (fn-bpr-state-receipts st)))
           (record (in-arena-fn-bprv-find-record *bpr-payloads* store (fn-bpr-state-config st) context (fn-sf-records (fn-sn-files store)))))
      (and (fn-sn-statep store)
           (equal (fn-sf-phase (fn-sn-files store)) :ready)
           (fn-record-p record)
           (member-equal record (fn-sf-records (fn-sn-files store)))
           (fn-bpi-node-record-committedp (fn-sn-node store) record)
           (equal (fn-bpaj-request-ref request)
                  (fn-bpr-context-request-ref context))
           (equal context (fn-bpr-context-from-request
                           record (fn-bpr-context-resolve context record)))
           (equal (fn-bpa-request-article (fn-bpr-context-resolve context record))
                  (fn-record-payload record))
           (equal (fn-bpa-request-subject (fn-bpr-context-resolve context record))
                  (fn-record-content-subject record))
           (member-equal entry (fn-bpr-state-receipts st))
           (fn-bprv-entry-decidedp entry records)
           (equal (fn-bpr-receipt-entry-receipt entry)
                  (fn-bpr-receipt-for context (fn-bpr-state-config st)
                                      (fn-bpa-receipt-id
                                       (fn-bpr-receipt-entry-receipt entry))))
           (equal (fn-bpr-receipt-adu st request)
                  (fn-bpa-encode (fn-bpr-receipt-entry-receipt entry))))))) ; evaluation witness for bprt-teeth-grounded-without-a-committed-decision
