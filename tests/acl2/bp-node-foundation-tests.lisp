; Reachable foundation witnesses, with explicit positive and negative checks.
(in-package "ACL2")
(include-book "../../books/bp-node-foundation")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpnf-local* (cons :dtn '(47 47 102 110 45 97 47)))
(defconst *bpnf-peer* (cons :dtn '(47 47 102 110 45 98 47)))
(defconst *bpnf-config* (fn-bpn-config *bpnf-local* 3600000 2 32 1048576))
(defconst *bpnf-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *bpnf-bundle*
  (fn-bpn-send-bundle *bpnf-config* *bpnf-peer* '(1 2 3 4) 7 *bpnf-obs*))
(defconst *bpnf-changed*
  (fn-bpb-make-bundle
   (fn-bpb-bundle-primary *bpnf-bundle*)
   (fn-bpb-bundle-blocks *bpnf-bundle*)
   (fn-bpb-payload-block (fn-bpn-config-crc-type *bpnf-config*) '(9 2 3 4))))
(defconst *bpnf-wire* (fn-bpb-encode *bpnf-bundle*))
(defconst *bpnf-ingress-p* (list :cl 1 1 *bpnf-peer* '(112) 0))
(defconst *bpnf-ingress-q* (list :cl 2 1 *bpnf-peer* '(113) 0))
(defconst *bpnf-base* (fn-bpn-initial-machine-state *bpnf-config* 4 1048576))
(defconst *bpnf-s0* (fn-bpnf-state *bpnf-base* nil nil nil nil nil nil 3 0))

(assert-event (fn-bpb-bundlep *bpnf-bundle*))
(assert-event (fn-bpb-bundlep *bpnf-changed*))
(assert-event (equal (fn-bpb-bundle-id *bpnf-bundle*)
                     (fn-bpb-bundle-id *bpnf-changed*)))
(assert-event (not (equal (fn-bpnf-immutable *bpnf-bundle*)
                          (fn-bpnf-immutable *bpnf-changed*))))
(assert-event (equal (fn-bpnf-receive-decision nil *bpnf-ingress-p* *bpnf-bundle*)
                     :fresh))
(assert-event
 (equal (third (car (fn-bpnf-answer-effects
                     (fn-bpnf-step *bpnf-s0*
                                    (list :receive-bundle *bpnf-bundle* '(1 2)
                                          *bpnf-ingress-p*)))))
        '(:refused :invalid-bundle)))

; A receive issues publication but cannot accept before the matched result.
(defconst *bpnf-proposal*
  (fn-bpnf-step *bpnf-s0*
                 (list :receive-bundle *bpnf-bundle* *bpnf-wire*
                       *bpnf-ingress-p*)))
(defconst *bpnf-pending* (fn-bpnf-answer-state *bpnf-proposal*))
(assert-event (equal (car (car (fn-bpnf-answer-effects *bpnf-proposal*))) :persist))
(assert-event (null (fn-bpnf-held-list *bpnf-pending*)))
(assert-event (fn-bpnf-operation-matchp (fn-bpnf-issued *bpnf-pending*) 3 0))
(assert-event (equal (fn-bpnf-next-op *bpnf-pending*) 1))
(assert-event (equal (nth 2 (car (fn-bpnf-answer-effects *bpnf-proposal*))) 0))
(assert-event (fn-bpnf-operationp (fn-bpnf-issued *bpnf-pending*)))
(assert-event (equal (fn-bpnf-answer-state
                      (fn-bpnf-step *bpnf-pending* '(:base (:clock :bad))))
                     *bpnf-pending*))
(assert-event (equal (fn-bpnf-base
                      (fn-bpnf-answer-state
                       (fn-bpnf-step *bpnf-s0* '(:base (:clock :bad)))))
                     (fn-bpn-answer-state
                      (fn-bpn-step *bpnf-base* '(:clock :bad)))))

; The same op id in an old process epoch and another op id in this epoch
; cannot install an entry or release a receive answer.
(defconst *bpnf-stale-epoch*
  (fn-bpnf-step *bpnf-pending* '(:persist-result 2 0 :durable)))
(defconst *bpnf-stale-op*
  (fn-bpnf-step *bpnf-pending* '(:persist-result 3 1 :durable)))
(assert-event (equal (fn-bpnf-answer-state *bpnf-stale-epoch*) *bpnf-pending*))
(assert-event (equal (fn-bpnf-answer-state *bpnf-stale-op*) *bpnf-pending*))
(assert-event (null (fn-bpnf-answer-effects *bpnf-stale-epoch*)))
(assert-event (not (fn-bpnf-operation-matchp
                    (fn-bpnf-issued *bpnf-pending*) 2 0)))
(assert-event (not (fn-bpnf-operation-matchp
                    (fn-bpnf-issued *bpnf-pending*) 3 1)))
(must-fail
 (assert-event (not (fn-bpnf-operation-matchp
                     (fn-bpnf-issued *bpnf-pending*) 3 0))))

(defconst *bpnf-accepted*
  (fn-bpnf-step *bpnf-pending* '(:persist-result 3 0 :durable)))
(defconst *bpnf-s1* (fn-bpnf-answer-state *bpnf-accepted*))
(assert-event (equal (len (fn-bpnf-held-list *bpnf-s1*)) 1))
(assert-event (not (equal (fn-bpnf-held-list *bpnf-s1*)
                          (fn-bpnf-held-list *bpnf-pending*))))
(assert-event (equal (nth 5 (fn-bpnf-issued *bpnf-pending*)) :pending))
(assert-event (equal (fn-bpnf-next-op *bpnf-s1*) 1))
(assert-event (fn-bpnf-heldp (car (fn-bpnf-held-list *bpnf-s1*))))
(assert-event (equal (third (car (fn-bpnf-answer-effects *bpnf-accepted*)))
                     :stored))
(defconst *bpnf-capacity-state*
  (fn-bpnf-state (fn-bpn-initial-machine-state *bpnf-config* 1 1048576)
                 (fn-bpnf-held-list *bpnf-s1*) nil nil nil nil nil 3 1))
(assert-event
 (equal (third (car (fn-bpnf-answer-effects
                     (fn-bpnf-step *bpnf-capacity-state*
                                    (list :receive-bundle *bpnf-bundle*
                                          *bpnf-wire* *bpnf-ingress-q*)))))
        '(:refused :capacity)))
(assert-event (equal (fn-bpnf-receive-decision
                      (fn-bpnf-held-list *bpnf-s1*) *bpnf-ingress-p* *bpnf-bundle*)
                     :duplicate))
(assert-event (equal (fn-bpnf-receive-decision
                      (fn-bpnf-held-list *bpnf-s1*) *bpnf-ingress-p* *bpnf-changed*)
                     :identity-conflict))

; Both the exact duplicate and a conflicting bundle from Q are fresh in Q's
; partition, despite P occupying the same RFC identity in the held list.
(assert-event (equal (fn-bpnf-receive-decision
                      (fn-bpnf-held-list *bpnf-s1*) *bpnf-ingress-q* *bpnf-bundle*)
                     :fresh))
(assert-event (equal (fn-bpnf-receive-decision
                      (fn-bpnf-held-list *bpnf-s1*) *bpnf-ingress-q* *bpnf-changed*)
                     :fresh))
(defconst *bpnf-q-proposal*
  (fn-bpnf-step *bpnf-s1*
                 (list :receive-bundle *bpnf-bundle* *bpnf-wire*
                       *bpnf-ingress-q*)))
(assert-event (fn-bpnf-operation-matchp
               (fn-bpnf-issued (fn-bpnf-answer-state *bpnf-q-proposal*)) 3 1))
(assert-event (null (fn-bpnf-answer-effects
                     (fn-bpnf-step (fn-bpnf-answer-state *bpnf-q-proposal*)
                                    '(:persist-result 2 1 :durable)))))
(assert-event (null (fn-bpnf-answer-effects
                     (fn-bpnf-step (fn-bpnf-answer-state *bpnf-q-proposal*)
                                    '(:persist-result 3 0 :durable)))))
(defconst *bpnf-q-accepted*
  (fn-bpnf-step (fn-bpnf-answer-state *bpnf-q-proposal*)
                 '(:persist-result 3 1 :durable)))
(assert-event (equal (len (fn-bpnf-held-list
                           (fn-bpnf-answer-state *bpnf-q-accepted*))) 2))
(assert-event (not (equal (fn-bpnf-held-principal
                            (first (fn-bpnf-held-list
                                    (fn-bpnf-answer-state *bpnf-q-accepted*))))
                          (fn-bpnf-held-principal
                           (second (fn-bpnf-held-list
                                    (fn-bpnf-answer-state *bpnf-q-accepted*)))))))
(assert-event (not (equal (fn-bpnf-held-principal (car (fn-bpnf-held-list *bpnf-s1*)))
                          (fn-bpnf-ingress-principal *bpnf-ingress-q*))))
; Dropping the distinct-principal hypothesis has a genuine counterexample.
(assert-event (not (equal (fn-bpnf-receive-decision
                           (fn-bpnf-held-list *bpnf-s1*) *bpnf-ingress-p* *bpnf-bundle*)
                          :fresh)))
(must-fail
 (assert-event
  (equal (fn-bpnf-receive-decision
          (fn-bpnf-held-list *bpnf-s1*) *bpnf-ingress-p* *bpnf-bundle*)
         :fresh)))
(must-fail
 (assert-event
  (equal (fn-bpnf-held-list *bpnf-s1*)
         (fn-bpnf-held-list *bpnf-pending*))))

; A callback uncertain outcome retains its issued operation as recovery
; evidence, blocks a second proposal, and never installs acceptance.
(defconst *bpnf-uncertain*
  (fn-bpnf-step *bpnf-pending* '(:persist-result 3 0 :uncertain)))
(assert-event (null (fn-bpnf-held-list (fn-bpnf-answer-state *bpnf-uncertain*))))
(assert-event (equal (nth 5 (fn-bpnf-issued (fn-bpnf-answer-state *bpnf-uncertain*)))
                     :uncertain))
(defconst *bpnf-uncertain-state* (fn-bpnf-answer-state *bpnf-uncertain*))
(defconst *bpnf-late-refused*
  (fn-bpnf-step *bpnf-uncertain-state* '(:persist-result 3 0 :refused)))
(defconst *bpnf-late-durable*
  (fn-bpnf-step *bpnf-uncertain-state* '(:persist-result 3 0 :durable)))
(assert-event (equal (fn-bpnf-answer-state *bpnf-late-refused*)
                     *bpnf-uncertain-state*))
(assert-event (equal (fn-bpnf-answer-state *bpnf-late-durable*)
                     *bpnf-uncertain-state*))
(assert-event (null (fn-bpnf-answer-effects *bpnf-late-refused*)))
(assert-event (null (fn-bpnf-answer-effects *bpnf-late-durable*)))
(assert-event (not (equal (nth 5 (fn-bpnf-issued *bpnf-pending*))
                          :uncertain)))
(assert-event
 (not (equal (fn-bpnf-answer-state
              (fn-bpnf-step *bpnf-pending* '(:persist-result 3 0 :refused)))
             *bpnf-pending*)))
(must-fail
 (assert-event
  (equal (fn-bpnf-answer-state
          (fn-bpnf-step *bpnf-pending* '(:persist-result 3 0 :refused)))
         *bpnf-pending*)))
(assert-event
 (equal (fn-bpnf-answer-state
         (fn-bpnf-step (fn-bpnf-answer-state *bpnf-late-refused*)
                        (list :receive-bundle *bpnf-bundle* *bpnf-wire*
                              *bpnf-ingress-q*)))
        *bpnf-uncertain-state*))
(assert-event
 (equal (third (car (fn-bpnf-answer-effects
                     (fn-bpnf-step (fn-bpnf-answer-state *bpnf-uncertain*)
                                    (list :receive-bundle *bpnf-bundle* *bpnf-wire*
                                          *bpnf-ingress-q*)))))
        '(:refused :busy)))

; A definite refusal releases the slot, but the following proposal receives
; a larger state-owned id.  A callback for the refused operation is stale.
(defconst *bpnf-refused*
  (fn-bpnf-step *bpnf-pending* '(:persist-result 3 0 :refused)))
(defconst *bpnf-after-refusal* (fn-bpnf-answer-state *bpnf-refused*))
(assert-event (null (fn-bpnf-issued *bpnf-after-refusal*)))
(assert-event (equal (fn-bpnf-next-op *bpnf-after-refusal*) 1))
(defconst *bpnf-second-proposal*
  (fn-bpnf-step *bpnf-after-refusal*
                 (list :receive-bundle *bpnf-bundle* *bpnf-wire*
                       *bpnf-ingress-q*)))
(assert-event (fn-bpnf-operation-matchp
               (fn-bpnf-issued (fn-bpnf-answer-state *bpnf-second-proposal*)) 3 1))
(assert-event
 (equal (fn-bpnf-answer-state
         (fn-bpnf-step (fn-bpnf-answer-state *bpnf-second-proposal*)
                        '(:persist-result 3 0 :durable)))
        (fn-bpnf-answer-state *bpnf-second-proposal*)))
(must-fail
 (assert-event
  (fn-bpnf-operation-matchp
   (fn-bpnf-issued (fn-bpnf-answer-state *bpnf-second-proposal*)) 3 0)))
(assert-event (equal (fn-bpnf-next-op
                      (fn-bpnf-answer-state *bpnf-second-proposal*)) 2))
(assert-event
 (not (equal (car (car (fn-bpnf-answer-effects
                        (fn-bpnf-step *bpnf-s0*
                                       (list :receive-bundle *bpnf-bundle* '(1 2)
                                             *bpnf-ingress-p*)))))
             :persist)))
(must-fail
 (assert-event
  (equal (fn-bpnf-next-op
          (fn-bpnf-answer-state
           (fn-bpnf-step *bpnf-s0*
                          (list :receive-bundle *bpnf-bundle* '(1 2)
                                *bpnf-ingress-p*))))
         (1+ (fn-bpnf-next-op *bpnf-s0*)))))

; A wait belongs to one obligation/action and wakes on the named dependency
; version.  Equal cardinality of two fragment sets is immaterial here.
(defconst *bpnf-wait* (fn-bpnf-wait '(:bundle 1) :dispatch :route 4 :no-route))
(assert-event (not (fn-bpnf-wait-wakes-p *bpnf-wait* '((:route . 4)))))
(assert-event (fn-bpnf-wait-wakes-p *bpnf-wait* '((:route . 5))))
(assert-event (equal (nth 1 *bpnf-wait*) '(:bundle 1)))
(assert-event (fn-bpnf-waitp *bpnf-wait*))
(must-fail (assert-event (fn-bpnf-wait-wakes-p *bpnf-wait* '((:route . 4)))))
