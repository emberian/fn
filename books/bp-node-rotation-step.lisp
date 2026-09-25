; The served step on N16's two rotation events (spec bp-node-machine 3.6,
; slice E).  The host calls fn-bpnp-step (host/native/bp-service.lisp
; fnn-bps-foundation-step; the `bp-node checkpoint' verb issues the
; (:rotate g ck) event and the (:persist-result e op r) answer of the
; publication through it).  The rotation behaviour is defined, and its
; properties stated, over fn-bpnp-rotate-step and
; fn-bpnp-rotation-persist-step; the two equations here make those facts
; about the called subject.  Each opens only fn-bpnp-step's dispatch, in a
; theory of its own, so the step's other forty arms never expand.
(in-package "ACL2")
(include-book "bp-node-progress")

(local
 (defthm fn-bpnrs-event-fields
   (and (equal (fn-cbor-ag-car (cons k x)) k)
        (equal (fn-bpn-nth 1 (list k a b)) a)
        (equal (fn-bpn-nth 2 (list k a b)) b)
        (equal (fn-bpn-nth 1 (list k a b c)) a)
        (equal (fn-bpn-nth 2 (list k a b c)) b)
        (equal (fn-bpn-nth 3 (list k a b c)) c))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-cbor-ag-car fn-bpn-nth car-cons cdr-cons
                                 (:e natp) (:e zp) (:e binary-+) (:e not))
                               (theory 'minimal-theory))))))

(local
 (defthm fn-bpnrs-not-domain-recover
   (implies (not (equal (fn-cbor-ag-car event) :recover-fnbs))
            (not (fn-bpnp-domain-recover-eventp event)))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnp-domain-recover-eventp)
                               (theory 'minimal-theory))))))

(local
 (defthm fn-bpnrs-answer-state
   (equal (fn-bpnf-answer-state (fn-bpnf-answer x e)) x)
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnf-answer fn-bpnf-answer-state
                                 fn-bpnrs-event-fields)
                               (theory 'minimal-theory))))))

;; A checkpoint whose publication is already uncertain answers nothing,
;; exactly as the step's uncertainty fence does.
(local
 (defthm fn-bpnrs-persist-step-when-uncertain
   (implies (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :uncertain)
            (equal (fn-bpnp-rotation-persist-step st epoch op result)
                   (fn-bpnf-answer st nil)))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnp-rotation-persist-step (:e equal))
                               (theory 'minimal-theory))))))

;; BRIDGE.  On (:rotate g ck) the served step is the rotation proposal,
;; behind the uncertainty fence every event other than recovery meets.
(defthm fn-bpnp-step-rotate-is-rotate-step
  (equal (fn-bpnp-step st (list :rotate generation ck))
         (if (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :uncertain)
             (fn-bpnf-answer st nil)
           (fn-bpnp-rotate-step st generation ck)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnp-step fn-bpnrs-event-fields
                         fn-bpnrs-not-domain-recover (:e equal) (:e not))
                       (theory 'minimal-theory)))))

;; BRIDGE.  On a publication answer while the issued operation is a
;; checkpoint, the served step is the rotation's persist arm (an uncertain
;; checkpoint answers nothing in both).
(defthm fn-bpnp-step-rotation-result-is-rotation-result
  (implies (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :checkpoint)
           (equal (fn-bpnp-step st (list :persist-result epoch op result))
                  (fn-bpnp-rotation-persist-step st epoch op result)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnp-step fn-bpnrs-event-fields
                         fn-bpnrs-not-domain-recover
                         fn-bpnrs-persist-step-when-uncertain
                         (:e equal) (:e not))
                       (theory 'minimal-theory)))))

;; The record count of the served step after a checkpoint's answer: 0 on
;; the matching durable answer, unchanged on every other one.
(defthm fn-bpnp-step-rotation-resets-credit-only-on-durable
  (implies (and (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :checkpoint)
                (true-listp st))
           (equal (fn-bpnp-used
                   (fn-bpnf-answer-state
                    (fn-bpnp-step st (list :persist-result epoch op result))))
                  (if (and (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :pending)
                           (fn-bpnf-operation-matchp (fn-bpnf-issued st) epoch op)
                           (equal result :durable))
                      0
                    (fn-bpnp-used st))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnp-step-rotation-result-is-rotation-result
                         fn-bpnp-rotation-persist-step fn-bpnp-used
                         fn-bpnrs-answer-state
                         fn-bpn-nth-is-nth-on-true-lists
                         nth-update-nth true-listp-update-nth
                         car-cons cdr-cons
                         (:e equal) (:e natp) (:e nfix) (:e zp) (:e not))
                       (theory 'minimal-theory)))))
