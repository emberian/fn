(in-package "ACL2")
(include-book "../../books/bp-native-app-fast")
(include-book "bp-native-app-tests")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

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
(assert-event
 (equal (fn-bpaj-dispatch-fast
         (fn-bpaj-nth 1 *bpaj-intent-replay*)
         *bpr-store* *bpaj-request-octets* 7)
        (fn-bpaj-dispatch
         (fn-bpaj-nth 1 *bpaj-intent-replay*)
         *bpr-store* *bpaj-request-octets* 7)))
(assert-event
 (equal (fn-bpaj-record-lookup-fast *bpr-store* *bpaj-request*)
        (fn-bpaj-record-lookup *bpr-store* *bpaj-request*)))
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
(make-event `(defconst *bpaj-fast-receipt-answer* ',(fn-bpaj-apply-record-fast
   (fn-bpaj-nth 1 *bpaj-context-replay*)
   *bpr-store* *bpaj-fast-receipt-intent*)))
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
(defconst *bpaj-semantically-invalid-old-intent*
  (list :request-intent "bundle-old" *bpaj-not-a-request-adu*
        3 4 :accepted))
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
      (not (fn-bpaj-intentp *bpaj-semantically-invalid-old-intent*))))
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
(defconst *bpaj-lookup* (fn-bpaj-record-lookup-fast *bpr-store* *bpaj-request*))
(assert-event (and (fn-sn-statep *bpr-store*) (fn-ceis-indexedp *bpr-store*)
                   (equal (car *bpaj-lookup*) :found)))
(assert-event
 (let ((record (cadr *bpaj-lookup*)))
   (and (fn-record-p record)
        (equal (fn-record-payload record) (fn-bpa-request-article *bpaj-request*))
        (equal (fn-record-content-subject record)
               (fn-bpa-request-subject *bpaj-request*))
        (fn-bpr-store-record-acceptedp *bpr-store* record))))
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
(assert-event (and (not (fn-sn-statep *bpaj-bad-store*))
                   (fn-ceis-indexedp *bpaj-bad-store*)
                   (equal (car (fn-bpaj-record-lookup-fast *bpaj-bad-store* *bpaj-request*))
                          :found)
                   (not (fn-bpr-store-record-acceptedp
                         *bpaj-bad-store*
                         (cadr (fn-bpaj-record-lookup-fast *bpaj-bad-store*
                                                           *bpaj-request*))))))
(must-fail
 (thm (implies (and (fn-ceis-indexedp store)
                    (equal (car (fn-bpaj-record-lookup-fast store request)) :found))
               (fn-bpr-store-record-acceptedp
                store (cadr (fn-bpaj-record-lookup-fast store request))))))
; Without fn-ceis-indexedp (a STALE index, a state no host transition
; reaches): the Store with its history intact and an index built from the
; same record at another transaction id.  The Store recognizer holds; the
; lookup finds that record (the node's article and binding agree with it);
; it is not in the history, so the checked predicate refuses it.
(defconst *bpaj-stale-record* (update-nth 0 99 (cadr *bpaj-lookup*)))
(defconst *bpaj-cut-store*
  (update-nth 13 (fn-cei-build (list *bpaj-stale-record*)) *bpr-store*))
(assert-event (and (fn-sn-statep *bpaj-cut-store*)
                   (not (fn-ceis-indexedp *bpaj-cut-store*))
                   (equal (car (fn-bpaj-record-lookup-fast *bpaj-cut-store* *bpaj-request*))
                          :found)
                   (not (fn-bpr-store-record-acceptedp
                         *bpaj-cut-store*
                         (cadr (fn-bpaj-record-lookup-fast *bpaj-cut-store*
                                                           *bpaj-request*))))))
(must-fail
 (thm (implies (and (fn-sn-statep store)
                    (equal (car (fn-bpaj-record-lookup-fast store request)) :found))
               (fn-bpr-store-record-acceptedp
                store (cadr (fn-bpaj-record-lookup-fast store request))))))
