; The BP request's immutable article and the NNTP transit Store projection
; are distinct on a reachable Path-bearing request.  The same peer table and
; transfer decision are used; a BP-only boundary grants no inbound scope.
(in-package "ACL2")
(include-book "../../books/bp-transit-join")
(include-book "../../books/codec-attach")
(include-book "peer-inbound-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *btj-peer*
  (fn-cfg-peer-make "dtnB" "dtnb.example" '(:bp "dtn://b/")
                    '("fn.letters" 32768 16) nil
                    '(:principal "bp-only-no-nntp-principal")))
(defconst *btj-boundary-rows*
  (list (fn-cfg-row-make "dtnB" "bp-trust" "network" 0)
        (fn-cfg-row-make "dtnB" "bp-boundary-listener" "127.0.0.1" 4556)
        (fn-cfg-row-make "dtnB" "bp-boundary-source" "127.0.0.1" 0)
        (fn-cfg-row-make "dtnB" "bp-boundary-translation" "none" 0)
        (fn-cfg-row-make "dtnB" "bp-boundary-originators"
                         "all-co-resident" 0)))
(defconst *btj-cfg*
  (fn-cfg-make 1
    (fn-cfg-apply-delta
      (fn-cfg-value *pt-cfg*) 1 *fn-cfg-default-stamp*
      (fn-cfg-set-peer "dtnB"
        (append (fn-cfg-peer-rows *btj-peer*) *btj-boundary-rows*)))))
(defconst *btj-ingress*
  (list :cl (cons 1 1) 1 (cons :dtn (pt-o "//b/"))
        (pt-o "dtnB") 1))
(make-event
 `(defconst *btj-subject*
    ',(fn-record-octets-string (fn-id-text (fn-id-subject-of-payload *pt-a1*)))))
(defconst *btj-request*
  (fn-bpa-make-request "work-btj" *btj-subject* "dtn://b/" "dtn://local/"
                       "policy" "incarnation" "auth" "terms" *pt-a1*))
(defconst *btj-request-octets* (fn-bpa-encode *btj-request*))
(make-event
 `(defconst *btj-plan*
    ',(fn-bpaj-transit-plan *pt-node0* *btj-cfg* *btj-ingress* "dtn://b/"
                              *btj-request-octets* *pt-obs*)))

(assert-event (fn-cfgp *btj-cfg*))
(assert-event (fn-bpa-requestp *btj-request*))
(assert-event (equal (car *btj-plan*) :submit))
(assert-event (equal (fn-bpaj-nth 1 *btj-plan*) "dtnB"))
(assert-event (equal (fn-bpaj-nth 3 *btj-plan*) *pt-a1*))
(assert-event (equal (fn-bpaj-transit-stored-octets *btj-plan*)
                     (fn-peer-relayed-octets *btj-cfg* "dtnB" *pt-a1*)))
(assert-event (not (equal (fn-bpaj-transit-stored-octets *btj-plan*)
                          *pt-a1*)))
(must-fail
 (assert-event (equal (fn-bpaj-transit-stored-octets *btj-plan*)
                      *pt-a1*)))
(make-event
 `(defconst *btj-intent*
    ',(fn-bpaj-transit-intent-from-plan
       *btj-cfg* "bundle-btj" *btj-request-octets* 1 0
       :accepted *btj-plan*)))
(assert-event (fn-bpaj-transit-intentp *btj-intent*))
(assert-event (equal (fn-bpaj-nth 2 *btj-intent*) *btj-request-octets*))
(assert-event (equal (fn-bpaj-nth 9 *btj-intent*)
                     (fn-bpaj-transit-stored-octets *btj-plan*)))
(assert-event (not (fn-bpaj-transit-intentp
                    (update-nth 9 *pt-a1* *btj-intent*))))
(must-fail
 (assert-event (fn-bpaj-transit-intentp
                (update-nth 9 *pt-a1* *btj-intent*))))
(assert-event
 (equal (fn-bpaj-transit-plan
         *pt-node0* *btj-cfg*
         (update-nth 4 nil *btj-ingress*) "dtn://b/"
         *btj-request-octets* *pt-obs*)
        '(:refused :no-principal)))
(defconst *btj-no-inbound-peer*
  (fn-cfg-peer-make "dtnB" "dtnb.example" '(:bp "dtn://b/") nil nil
                    '(:principal "bp-only-no-nntp-principal")))
(defconst *btj-no-inbound-cfg*
  (fn-cfg-make 1
    (fn-cfg-apply-delta
      (fn-cfg-value *pt-cfg*) 1 *fn-cfg-default-stamp*
      (fn-cfg-set-peer "dtnB"
        (append (fn-cfg-peer-rows *btj-no-inbound-peer*)
                *btj-boundary-rows*)))))
(assert-event
 (equal (fn-bpaj-transit-plan
         *pt-node0* *btj-no-inbound-cfg* *btj-ingress* "dtn://b/"
         *btj-request-octets* *pt-obs*)
        '(:refused :no-inbound)))

; The BP-origin event enters the real owner transit queue without inventing
; an NNTP connection.  A premature :durable word is still uncertain.
(defconst *btj-owner*
  (fn-own-observe (fn-own-start
                   (fn-sn-initial '("fn.letters" "fn.test") 10) 4)
                  *pt-obs*))
(assert-event
 (equal (fn-own-bp-transit-submit-result
         *btj-owner* *btj-cfg* "dtnB" *pt-id1* *pt-a1*
         (fn-bpaj-nth 8 *btj-plan*) (fn-bpaj-nth 9 *btj-plan*))
        :submitted))
(defconst *btj-queued*
  (fn-own-bp-transit-submit
   *btj-owner* *btj-cfg* "dtnB" *pt-id1* *pt-a1*
   (fn-bpaj-nth 8 *btj-plan*) (fn-bpaj-nth 9 *btj-plan*)))
(assert-event (fn-own-bp-transit-submissionp
               (car (fn-own-queue *btj-queued*))))
(defconst *btj-taken* (fn-own-take-submission *btj-queued*))
(assert-event (fn-own-bp-transit-submissionp
               (fn-own-inflight *btj-taken*)))
(assert-event
 (equal (fn-own-bp-transit-outcome-result *btj-taken* :durable)
        :uncertain))
(assert-event
 (not (fn-own-inflight
       (fn-own-bp-transit-outcome *btj-taken* :uncertain))))
(must-fail
 (assert-event
  (equal (fn-own-bp-transit-outcome-result *btj-taken* :durable)
         :accepted)))
