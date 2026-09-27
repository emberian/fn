(in-package "ACL2")
(include-book "../../books/bp-native-app-fast")
(include-book "bp-native-app-tests")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")

; Recovery is the one deep validation boundary.  Its successful result carries
; the invariant used by every subsequent served projection.
(assert-event
 (fn-bpaj-statep (fn-bpaj-nth 1 *bpaj-context-replay*)))
(assert-event (fn-sn-statep *bpr-store*))

(assert-event
 (equal (fn-bpaj-request-status-fast
         (fn-bpaj-nth 1 *bpaj-context-replay*) *bpaj-request-octets*)
        (fn-bpaj-request-status
         (fn-bpaj-nth 1 *bpaj-context-replay*) *bpaj-request-octets*)))
(include-book "arena-hist-lift")
(bpr-lift-hist fn-bpaj-apply-record-fast 3 (fn-sf-records (fn-sn-files x2)))
(bpr-lift fn-bpaj-dispatch 4)
(bpr-lift-hist fn-bpaj-dispatch-fast 4 (fn-sf-records (fn-sn-files x2)))
(bpr-lift-hist fn-bpaj-record-lookup-fast 2 (fn-sf-records (fn-sn-files x1)))
(bpr-lift fn-bpaj-transit-record-lookup 3)
(bpr-lift-hist fn-bpaj-transit-record-lookup-fast 3 (fn-sf-records (fn-sn-files x1)))
(bpr-lift fn-bpr-store-record-acceptedp 2)

(assert-event
 (equal (in-arena-fn-bpaj-dispatch-fast *bpr-payloads* (fn-bpaj-nth 1 *bpaj-intent-replay*) *bpr-store* *bpaj-request-octets* 7)
        (in-arena-fn-bpaj-dispatch *bpr-payloads* (fn-bpaj-nth 1 *bpaj-intent-replay*) *bpr-store* *bpaj-request-octets* 7)))
(assert-event
 (equal (in-arena-fn-bpaj-transit-record-lookup-fast *bpr-payloads* *bpr-store* *bpaj-request* *bpaj-intent*)
        (in-arena-fn-bpaj-transit-record-lookup *bpr-payloads* *bpr-store* *bpaj-request* *bpaj-intent*)))
(assert-event
 (equal (fn-bpaj-config-status-fast
         (fn-bpaj-nth 1 *bpaj-context-replay*)
         "dtn://b.lab/fn" "policy-v1" "node-b")
        (fn-bpaj-config-status
         (fn-bpaj-nth 1 *bpaj-context-replay*)
         "dtn://b.lab/fn" "policy-v1" "node-b")))

; An actual live receipt-intent transition succeeds and retains the joined
; invariant through the fast apply function called by the host.
(defconst *bpaj-fast-receipt-intent*
  (let* ((st (fn-bpaj-receiver (fn-bpaj-nth 1 *bpaj-context-replay*)))
         (next (fn-bpaj-bpr-prepare-receipt-fast
                st "work-native" "receipt:work-native" t))
         (pending (fn-bpr-state-pending next)))
    (list :receipt-intent "work-native" "receipt:work-native"
          (fn-bpa-encode (fn-bpr-receipt-entry-receipt pending)) t)))
(make-event `(defconst *bpaj-fast-receipt-answer* ',(in-arena-fn-bpaj-apply-record-fast *bpr-payloads* (fn-bpaj-nth 1 *bpaj-context-replay*) *bpr-store* *bpaj-fast-receipt-intent*)))
(assert-event (car *bpaj-fast-receipt-answer*))
(assert-event
 (fn-bpaj-statep (fn-bpaj-nth 1 *bpaj-fast-receipt-answer*)))
(assert-event
 (equal (fn-bpaj-pending-receipt-resolution-fast
         (fn-bpaj-nth 1 *bpaj-fast-receipt-answer*))
        (list :receipt-decision "work-native" "receipt:work-native" :absent)))

; The invariant hypothesis has teeth.  This is still a four-field joined
; object with a valid receiver, valid current intent, valid facts and boolean
; strict flag.  Its nonempty older history record also has the exact intent
; list shape and scalar fields, but its ADU encodes a receipt rather than a
; request.  The current request is the distinct work-native request.  Deep
; validation therefore rejects the joined history; the fast projection can
; answer only because it deliberately assumes successful replay established
; the invariant.
(defconst *bpaj-not-a-request-adu*
  (fn-bpa-encode
   (fn-bpa-make-receipt "old-receipt" "work-old"
                        "old-subject" "old-issuer" "dtn://old.lab"
                        "old-policy" "old-incarnation" "old-auth"
                        "old-terms")))
; PKT-646: an intent carries the request's reference.  This one's HEAD
; names the live request's work id, but its article DIGEST is no digest (two
; octets), so it is no intent.
(defconst *bpaj-semantically-invalid-old-intent*
  (update-nth 10 '(1 2) (update-nth 1 "bundle-old" *bpaj-intent*)))
(defconst *bpaj-fast-hypothesis-counterexample*
  (fn-bpaj-make-state
   (fn-bpaj-receiver (fn-bpaj-nth 1 *bpaj-intent-replay*))
   (append (fn-bpaj-intents (fn-bpaj-nth 1 *bpaj-intent-replay*))
           (list *bpaj-semantically-invalid-old-intent*))
   (fn-bpaj-facts (fn-bpaj-nth 1 *bpaj-intent-replay*)) t))
(assert-event
 (and (true-listp *bpaj-fast-hypothesis-counterexample*)
      (equal (len *bpaj-fast-hypothesis-counterexample*) 4)
      (fn-bpr-statep
       (fn-bpaj-receiver *bpaj-fast-hypothesis-counterexample*))
      (consp (fn-bpaj-intents *bpaj-fast-hypothesis-counterexample*))
      (not (fn-bpaj-transit-intentp *bpaj-semantically-invalid-old-intent*))))
(assert-event (not (fn-bpaj-statep *bpaj-fast-hypothesis-counterexample*)))
(assert-event
 (equal (fn-bpaj-request-status
         *bpaj-fast-hypothesis-counterexample* *bpaj-request-octets*)
        :malformed))
(assert-event
 (equal (fn-bpaj-request-status-fast
         *bpaj-fast-hypothesis-counterexample* *bpaj-request-octets*)
        :intent))
(assert-event
 (not (equal (fn-bpaj-request-status-fast
              *bpaj-fast-hypothesis-counterexample* *bpaj-request-octets*)
             (fn-bpaj-request-status
              *bpaj-fast-hypothesis-counterexample* *bpaj-request-octets*))))
(assert-event
 (equal (fn-bpaj-config-status
         *bpaj-fast-hypothesis-counterexample*
         "dtn://b.lab/fn" "policy-v1" "node-b")
        :absent))
(assert-event
 (not (equal (fn-bpaj-config-status-fast
              *bpaj-fast-hypothesis-counterexample*
              "dtn://b.lab/fn" "policy-v1" "node-b")
             :absent)))

; Fresh native FNRJ open calls fn-bprj-reset, which installs exactly NIL.
; It must permit configuration publication before the joined invariant exists.
(assert-event
 (equal (fn-bpaj-config-status-fast nil "dtn://b.lab/fn" "policy-v1" "node-b")
        :absent))
(assert-event
 (equal (fn-bpaj-config-status-fast nil "dtn://b.lab/fn" "policy-v1" "node-b")
        (fn-bpaj-config-status nil "dtn://b.lab/fn" "policy-v1" "node-b")))

; -----------------------------------------------------------------------------
; PRF-220.
; fn-bpaj-record-lookup-fast-found-is-an-accepted-match (books/bp-native-app-fast.lisp).
; Positive witness: the receiver fixture's Store finds the request's record for the request.
(defconst *bpaj-lookup* (in-arena-fn-bpaj-record-lookup-fast *bpr-payloads* *bpr-store* *bpaj-request*))

(assert-event
 (let ((record (cadr *bpaj-lookup*)))
   (and (fn-record-p record)
        (equal (fn-record-payload record) (fn-bpa-request-article *bpaj-request*))
        (equal (fn-record-content-subject record)
               (fn-bpa-request-subject *bpaj-request*))
        (in-arena-fn-bpr-store-record-acceptedp *bpr-payloads* *bpr-store* record))))
; Without fn-sn-statep (a CORRUPTED node: the Store's node with a junk binding after its real
; ones, which no host transition builds): the index still finds the
; record and the carried check accepts it; the checked Store predicate does
; not, so the conclusion fails.
(defconst *bpaj-live-node* (fn-sn-node *bpr-store*))
(defconst *bpaj-bad-node*
  (fn-node-make-state (fn-node-acceptance *bpaj-live-node*)
                      (fn-node-retention *bpaj-live-node*)
                      (fn-node-stage *bpaj-live-node*)
                      (append (fn-node-bindings *bpaj-live-node*) (list 'junk))))
(defconst *bpaj-bad-store* (update-nth 3 *bpaj-bad-node* *bpr-store*))


; Without fn-ceis-indexedp (a STALE index, a state no host transition
; reaches): the Store with its history intact and an index built from the
; same record at another transaction id.  The Store recognizer holds; the
; lookup finds that record (the node's article and binding agree with it);
; it is not in the history, so the checked predicate refuses it.  After the
; records flip the index holds retained rows: the stale entry is the Store's
; held row at another sequence.
(defconst *bpaj-stale-record* (update-nth 0 99 *bpr-row*))
(assert-event (fn-held-p *bpaj-stale-record*))



