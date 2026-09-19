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

(defconst *bprt-journal*
  (list *bprr-config-record* *bprr-request-record*
        *bprr-intent-record* *bprr-decision-record*))
(defconst *bprt-state*
  (cadr (fn-bprr-replay *bpr-recovered-ready-store* *bprt-journal*)))

(assert-event (car (fn-bprr-replay *bpr-recovered-ready-store* *bprt-journal*)))
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
(defconst *bprt-context*
  (fn-bpr-find-context (fn-bpa-request-work-id *bpr-request*)
                       (fn-bpr-state-contexts *bprt-state*)))
(defconst *bprt-record*
  (fn-bprv-find-record *bpr-recovered-ready-store*
                       (fn-bpr-state-config *bprt-state*) *bprt-context*
                       (fn-sf-records (fn-sn-files *bpr-recovered-ready-store*))))
(assert-event (fn-record-p *bprt-record*))
(assert-event
 (member-equal *bprt-record*
               (fn-sf-records (fn-sn-files *bpr-recovered-ready-store*))))
(assert-event
 (fn-bpi-node-record-committedp (fn-sn-node *bpr-recovered-ready-store*) *bprt-record*))
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
        (cadr (fn-bprr-replay *bpr-recovering-store* *bprt-journal*))
        *bpr-request*)))
(assert-event
 (not (equal (fn-sf-phase (fn-sn-files *bpr-recovering-store*)) :ready)))

(local
 (must-fail
  (defthm bprt-teeth-grounded-without-an-unready-store
    (let* ((store *bpr-recovering-store*)
           (records *bprt-journal*)
           (request *bpr-request*)
           (st (cadr (fn-bprr-replay store records)))
           (context (fn-bpr-find-context (fn-bpa-request-work-id request)
                                         (fn-bpr-state-contexts st)))
           (entry (fn-bpr-find-receipt (fn-bpr-context-work-id context)
                                       (fn-bpr-state-receipts st)))
           (record (fn-bprv-find-record store (fn-bpr-state-config st) context
                                        (fn-sf-records (fn-sn-files store)))))
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
                                      (fn-bpa-receipt-id
                                       (fn-bpr-receipt-entry-receipt entry))))
           (equal (fn-bpr-receipt-adu st request)
                  (fn-bpa-encode (fn-bpr-receipt-entry-receipt entry))))))))

; Case 2: a ready Store, but the journal stops after the receipt intent with no
; committed decision.  No receipt is emitted, and the conclusion's
; entry-decided conjunct is false: an intent is not a decision, and bytes may
; not be produced from one.
(defconst *bprt-intent-only*
  (list *bprr-config-record* *bprr-request-record* *bprr-intent-record*))
(assert-event
 (null (fn-bpr-receipt-adu
        (cadr (fn-bprr-replay *bpr-recovered-ready-store* *bprt-intent-only*))
        *bpr-request*)))

(local
 (must-fail
  (defthm bprt-teeth-grounded-without-a-committed-decision
    (let* ((store *bpr-recovered-ready-store*)
           (records *bprt-intent-only*)
           (request *bpr-request*)
           (st (cadr (fn-bprr-replay store records)))
           (context (fn-bpr-find-context (fn-bpa-request-work-id request)
                                         (fn-bpr-state-contexts st)))
           (entry (fn-bpr-find-receipt (fn-bpr-context-work-id context)
                                       (fn-bpr-state-receipts st)))
           (record (fn-bprv-find-record store (fn-bpr-state-config st) context
                                        (fn-sf-records (fn-sn-files store)))))
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
                                      (fn-bpa-receipt-id
                                       (fn-bpr-receipt-entry-receipt entry))))
           (equal (fn-bpr-receipt-adu st request)
                  (fn-bpa-encode (fn-bpr-receipt-entry-receipt entry))))))))
