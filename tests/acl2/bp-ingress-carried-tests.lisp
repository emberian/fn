; fn: witnesses and teeth for books/bp-ingress-carried.lisp's keystone,
; fn-bpi-ingress-prepare-carried-is-prepare (the BP ingress prepare,
; host/bp-ingress-host.lisp fn-bpi-host-prepare).
;
; The stores are bp-ingress-tests': *bpi-reserved* is fn-sn-initial after the
; frontier reservation; *bpi-done* holds the ADU's article durably and
; (bpi-reserve *bpi-done*) reserves again.  *bpic-stale* is that store with
; its node replaced by an empty one (a CORRUPTED state, labelled).
(in-package "ACL2")
(include-book "../../books/bp-ingress-carried")
(include-book "std/testing/must-fail" :dir :system)
(include-book "bp-ingress-tests")

; Reachable POSITIVE witness.  Antecedent: the store is related.
; Conclusion: the carried prepare is the specification's, and it prepares
; (the store stages the ADU's row at handle 0).
(assert-event (fn-snt-relation *bpi-reserved*))
(defconst *bpic-prepared*
  (fn-bpi-ingress-prepare-carried *bpi-reserved* *bpi-policy* *bpi-context* *bpi-adu* 0))
(assert-event (equal *bpic-prepared* *bpi-prepared*))
(assert-event (equal (fn-bpi-result-kind *bpic-prepared*) :prepared))
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-bpi-result-store *bpic-prepared*)))
                     :record-staged))

; A related REFUSAL: the same ADU again after its durable acceptance.  Both
; refuse at the store (the duplicate Message-ID).
(defconst *bpic-again* (bpi-reserve *bpi-done*))
(assert-event (fn-snt-relation *bpic-again*))
(defconst *bpic-dup*
  (fn-bpi-ingress-prepare-carried *bpic-again* *bpi-policy* *bpi-context* *bpi-adu* 1))
(assert-event (equal *bpic-dup*
                     (fn-bpi-ingress-prepare *bpic-again* *bpi-policy* *bpi-context* *bpi-adu* 1)))
(assert-event (equal *bpic-dup* '(:rejected :store-refused)))

; HYPOTHESIS REMOVAL (CORRUPTED state).  *bpic-stale* keeps *bpic-again*'s
; files (the durable history holds the ADU's article) but takes the node and
; index of a store whose first reservation was REFUSED and reserved again
; (the same counters, no article).  The retained structure holds
; (fn-sn-statep, the guard), the omitted hypothesis fails (not
; fn-snt-relation), and the conclusion fails: the node never saw the
; Message-ID, so the carried prepare stages the duplicate while the
; specification's replay of the durable history refuses it.
(defconst *bpic-refused*
  (bpi-reserve (fn-sn-refuse-reservation
                *bpi-reserved* (1- (fn-sf-frontier (fn-sn-files *bpi-reserved*))))))
(defconst *bpic-stale*
  (fn-sn-update-indexed *bpic-again* (fn-sn-files *bpic-again*)
                        (fn-sn-node *bpic-refused*) (fn-sn-index *bpic-refused*)))
(assert-event (fn-sn-statep *bpic-stale*))
(assert-event (not (fn-snt-relation *bpic-stale*)))
(defconst *bpic-stale-carried*
  (fn-bpi-ingress-prepare-carried *bpic-stale* *bpi-policy* *bpi-context* *bpi-adu* 1))
(defconst *bpic-stale-spec*
  (fn-bpi-ingress-prepare *bpic-stale* *bpi-policy* *bpi-context* *bpi-adu* 1))
(assert-event (equal (fn-bpi-result-kind *bpic-stale-carried*) :prepared))
(assert-event (equal *bpic-stale-spec* '(:rejected :store-refused)))
(must-fail
 (assert-event (equal *bpic-stale-carried* *bpic-stale-spec*)))
