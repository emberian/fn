(in-package "ACL2")
(include-book "../../books/bp-native-app-replay-bridge")
(include-book "bp-native-app-tests")
(include-book "std/testing/must-fail" :dir :system)

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
(must-fail
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
