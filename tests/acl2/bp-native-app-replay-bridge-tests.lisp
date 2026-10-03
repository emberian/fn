(in-package "ACL2")
(include-book "../../books/bp-native-app-replay-bridge")
(include-book "bp-native-app-tests")
(include-book "must-fail-checked")

; fn-bpaj-replay-receiver-is-receiver-replay: complete positive antecedent
; and conclusion, with an accepted request AND committed receipt.  These
; are the actual journal entries of the receiver fixture, not an empty run.
(defconst *bpaj-bridge-records*
  (list *bprr-config-record* *bprr-request-record*
        *bprr-intent-record* *bprr-decision-record*))
(make-event
 `(defconst *bpaj-bridge-actual*
    ',(in-arena-fn-bpaj-replay *bpr-payloads* *bpr-store*
                              *bpaj-bridge-records*)))
(assert-event
 (and (consp (cdr *bpaj-bridge-records*))
      (fn-bpaj-receiver-only-recordsp *bpaj-bridge-records*)
      (car *bpaj-bridge-actual*)
      (equal (fn-bpaj-receiver-result *bpaj-bridge-actual*) *bprr-full*)
      (equal (fn-bpr-receipt-adu
              (fn-bpaj-receiver (cadr *bpaj-bridge-actual*)) *bpr-request*)
             (fn-bpa-encode *bprr-receipt*))))

; Hypothesis removal: the valid reachable transit intent succeeds in the
; actual join, while the receiver-only replay refuses it.  No retained
; hypothesis remains.  This is a valid-state separation, not corruption.
(defconst *bpaj-bridge-transit-records* (list *bpaj-config* *bpaj-intent*))
(make-event
 `(defconst *bpaj-bridge-transit-model*
    ',(in-arena-fn-bprr-replay *bpr-payloads* *bpr-store*
                              *bpaj-bridge-transit-records*)))
(assert-event
 (and (fn-bpaj-transit-intentp *bpaj-intent*)
      (not (fn-bpaj-receiver-only-recordsp *bpaj-bridge-transit-records*))
      (car *bpaj-intent-replay*)
      (not (car *bpaj-bridge-transit-model*))
      (not (equal (fn-bpaj-receiver-result *bpaj-intent-replay*)
                  *bpaj-bridge-transit-model*))))
(must-fail-checked
 (assert-event
  (equal (fn-bpaj-receiver-result *bpaj-intent-replay*)
         *bpaj-bridge-transit-model*)))

; A duplicate request faults both interpreters and preserves their same
; accepted prefix.  The equation covers unsuccessful replay too.
(defconst *bpaj-bridge-refused-records*
  (list *bprr-config-record* *bprr-request-record* *bprr-request-record*))
(make-event
 `(defconst *bpaj-bridge-refused-actual*
    ',(in-arena-fn-bpaj-replay *bpr-payloads* *bpr-store*
                              *bpaj-bridge-refused-records*)))
(make-event
 `(defconst *bpaj-bridge-refused-model*
    ',(in-arena-fn-bprr-replay *bpr-payloads* *bpr-store*
                              *bpaj-bridge-refused-records*)))
(assert-event
 (and (fn-bpaj-receiver-only-recordsp *bpaj-bridge-refused-records*)
      (not (car *bpaj-bridge-refused-actual*))
      (equal (fn-bpaj-receiver-result *bpaj-bridge-refused-actual*)
             *bpaj-bridge-refused-model*)))

(bpr-lift fn-bpaj-replay-rest 3)
(bpr-lift fn-bprr-replay-rest 3)
(defconst *bpaj-bridge-initial* (fn-bpaj-make-state *bpr-initial* nil nil nil))

; fn-bpaj-replay-rest-receiver-is-receiver-replay-rest: all hypotheses
; and the full conclusion for the nonempty request/receipt suffix.
(make-event
 `(defconst *bpaj-bridge-rest-actual*
    ',(in-arena-fn-bpaj-replay-rest
       *bpr-payloads* *bpaj-bridge-initial* *bpr-store*
       (cdr *bpaj-bridge-records*))))
(make-event
 `(defconst *bpaj-bridge-rest-model*
    ',(in-arena-fn-bprr-replay-rest
       *bpr-payloads* (fn-bpaj-receiver *bpaj-bridge-initial*) *bpr-store*
       (cdr *bpaj-bridge-records*))))
(assert-event
 (and (fn-bpaj-context-firstp *bpaj-bridge-initial*)
      (fn-bpaj-receiver-only-recordsp (cdr *bpaj-bridge-records*))
      (car *bpaj-bridge-rest-actual*)
      (equal (fn-bpaj-receiver-result *bpaj-bridge-rest-actual*)
             *bpaj-bridge-rest-model*)))

; Remove context-firstp: the actually replayed transit intent has switched
; the join to strict. A context-first request succeeds in the receiver model
; and is refused in the actual join. Retained no-transit hypothesis holds.
(make-event
 `(defconst *bpaj-bridge-strict-actual*
    ',(in-arena-fn-bpaj-replay-rest
       *bpr-payloads* (cadr *bpaj-intent-replay*) *bpr-store*
       (list *bprr-request-record*))))
(make-event
 `(defconst *bpaj-bridge-strict-model*
    ',(in-arena-fn-bprr-replay-rest
       *bpr-payloads* (fn-bpaj-receiver (cadr *bpaj-intent-replay*))
       *bpr-store* (list *bprr-request-record*))))
(assert-event
 (and (fn-bpaj-statep (cadr *bpaj-intent-replay*))
      (not (fn-bpaj-context-firstp (cadr *bpaj-intent-replay*)))
      (fn-bpaj-receiver-only-recordsp (list *bprr-request-record*))
      (not (car *bpaj-bridge-strict-actual*))
      (car *bpaj-bridge-strict-model*)
      (not (equal (fn-bpaj-receiver-result *bpaj-bridge-strict-actual*)
                  *bpaj-bridge-strict-model*))))
(must-fail-checked
 (assert-event
  (equal (fn-bpaj-receiver-result *bpaj-bridge-strict-actual*)
         *bpaj-bridge-strict-model*)))

; Remove receiver-only-recordsp: retain context-firstp, then replay a valid
; transit intent. Actual replay succeeds and the receiver model refuses.
(make-event
 `(defconst *bpaj-bridge-rest-transit-actual*
    ',(in-arena-fn-bpaj-replay-rest
       *bpr-payloads* *bpaj-bridge-initial* *bpr-store* (list *bpaj-intent*))))
(make-event
 `(defconst *bpaj-bridge-rest-transit-model*
    ',(in-arena-fn-bprr-replay-rest
       *bpr-payloads* (fn-bpaj-receiver *bpaj-bridge-initial*) *bpr-store*
       (list *bpaj-intent*))))
(assert-event
 (and (fn-bpaj-context-firstp *bpaj-bridge-initial*)
      (not (fn-bpaj-receiver-only-recordsp (list *bpaj-intent*)))
      (fn-bpaj-transit-intentp *bpaj-intent*)
      (car *bpaj-bridge-rest-transit-actual*)
      (not (car *bpaj-bridge-rest-transit-model*))
      (not (equal (fn-bpaj-receiver-result *bpaj-bridge-rest-transit-actual*)
                  *bpaj-bridge-rest-transit-model*))))
(must-fail-checked
 (assert-event
  (equal (fn-bpaj-receiver-result *bpaj-bridge-rest-transit-actual*)
         *bpaj-bridge-rest-transit-model*)))
