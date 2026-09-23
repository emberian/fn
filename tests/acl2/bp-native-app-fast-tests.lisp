(in-package "ACL2")
(include-book "../../books/bp-native-app-fast")
(include-book "bp-native-app-tests")
(include-book "../../books/codec-attach")

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
