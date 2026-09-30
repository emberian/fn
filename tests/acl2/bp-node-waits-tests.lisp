; PRF-1116 / PKT-064. Every state in the positive trace comes from the
; actual host subject, fn-bpnj-step. Two independent kind-5 receptions:
; a busy local delivery and a transit row for a different destination.
(in-package "ACL2")
(include-book "../../books/bp-node-waits")
(include-book "../../books/bp-node-job-offer-guards")
(include-book "../../books/bp-node-receive-boundary")
(include-book "../../books/codec-attach")

(defmacro bpw-defc (name form)
  `(make-event (list 'defconst ',name (list 'quote ,form))))
(defconst *bpw-local* (cons :dtn '(47 47 108 111 99 97 108 47)))
(defconst *bpw-peer* (cons :dtn '(47 47 112 101 101 114 47)))
(defconst *bpw-config* (fn-bpn-config *bpw-local* 3600000 2 32 1048576))
(defconst *bpw-peer-config* (fn-bpn-config *bpw-peer* 3600000 2 32 1048576))
(defconst *bpw-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *bpw-session* '(1 . 1))
(defconst *bpw-ingress* (list :cl '(0 . 1) 1 *bpw-peer* '(112) 0))
(defconst *bpw-via*
  (list :via "relay" (fn-record-string-octets "dtn://relay/")
        (list (fn-bprt-route 100 "dtn://peer/" "relay" "dtn://relay/" 4556))))
(defconst *bpw-request*
  (fn-bpa-encode
   (fn-bpa-make-request "w" "s" "dtn://peer/" "dtn://local/"
                        "p" "i" "c" "t" '(88 13 10))))
(defun bpw-receive (destination sequence)
  (fn-bpnf-receive-wire-event-value
   (fn-bpnf-receive-wire-event
    *bpw-config*
    (fn-bpb-encode
     (fn-bpn-send-bundle *bpw-peer-config* destination
                         (if (equal destination *bpw-local*)
                             *bpw-request* '(1 2 3))
                         sequence *bpw-obs*))
    *bpw-obs* *bpw-ingress*)))
(defun bpw-callback (answer result)
  (let ((effect (car (fn-bpnf-answer-effects answer))))
    (list :persist-result (fn-bpn-nth 1 effect) (fn-bpn-nth 2 effect) result)))
(defun bpw-settle (answer result)
  (fn-bpnj-step (fn-bpnf-answer-state answer) (bpw-callback answer result)))
(defconst *bpw-raw* (fn-bpnf-initial-state *bpw-config* 8 1048576))
(defconst *bpw-boot* (fn-bpnf-family-recover-auto-event *bpw-raw* nil :ready nil))
(bpw-defc *bpw-s0* (fn-bpnf-answer-state (fn-bpnj-step *bpw-raw* *bpw-boot*)))
(bpw-defc *bpw-local-proposal* (fn-bpnj-step *bpw-s0* (bpw-receive *bpw-local* 7)))
(bpw-defc *bpw-s1* (fn-bpnf-answer-state (bpw-settle *bpw-local-proposal* :durable)))
(bpw-defc *bpw-transit-proposal* (fn-bpnj-step *bpw-s1* (bpw-receive *bpw-peer* 8)))
(bpw-defc *bpw-s2* (fn-bpnf-answer-state (bpw-settle *bpw-transit-proposal* :durable)))
(defconst *bpw-tick* (list :progress *bpw-local* *bpw-obs* (list (list *bpw-peer* *bpw-peer*)) 1))
(bpw-defc *bpw-deliver* (fn-bpnj-step *bpw-s2* *bpw-tick*))
(bpw-defc *bpw-busy-event*
  (let ((effect (car (fn-bpnf-answer-effects *bpw-deliver*))))
    (list :deliver-result (fn-bpn-nth 1 effect) (fn-bpn-nth 2 effect)
          (fn-bpn-nth 3 effect) :busy '(0) *bpw-obs*)))
(bpw-defc *bpw-busy-proposal*
  (fn-bpnj-step (fn-bpnf-answer-state *bpw-deliver*) *bpw-busy-event*))
(bpw-defc *bpw-deferred* (fn-bpnf-answer-state (bpw-settle *bpw-busy-proposal* :durable)))
(bpw-defc *bpw-waits* (fn-bpnp-waits *bpw-deferred*))
(bpw-defc *bpw-dispatch* (fn-bpnj-step *bpw-deferred* *bpw-tick*))
(bpw-defc *bpw-dispatched* (fn-bpnf-answer-state (bpw-settle *bpw-dispatch* :durable)))
(defconst *bpw-open-event*
  (list :session *bpw-peer* *bpw-session* t 32768 *bpw-obs* *bpw-via*))
(bpw-defc *bpw-attempt* (fn-bpnj-step *bpw-dispatched* *bpw-open-event*))
(bpw-defc *bpw-attempt-refused* (bpw-settle *bpw-attempt* :refused))
; A new session retries the refused publication, from the actual refused state.
(bpw-defc *bpw-attempt2*
  (fn-bpnj-step (fn-bpnf-answer-state *bpw-attempt-refused*) *bpw-open-event*))
(bpw-defc *bpw-sending* (fn-bpnf-answer-state (bpw-settle *bpw-attempt2* :durable)))
(bpw-defc *bpw-result-event*
  (let ((effect (car (fn-bpnf-answer-effects *bpw-attempt2*))))
    (list :forward-result (fn-bpn-nth 1 effect) (fn-bpn-nth 2 effect)
          *bpw-session* :sent *bpw-obs*)))
(bpw-defc *bpw-result* (fn-bpnj-step *bpw-sending* *bpw-result-event*))
(bpw-defc *bpw-result-refused* (bpw-settle *bpw-result* :refused))

; All observed transitions have the exact host guard antecedent, without
; installing held rows or waits by hand. Each pair is (state, event).
(defun bpw-host-pairsp (pairs)
  (if (endp pairs) t
    (let ((st (caar pairs)) (event (cadar pairs)))
      (and (fn-bpn-machine-statep (fn-bpnf-base st))
           (fn-bpnp-session-listp (fn-bpnp-sessions st))
           (true-listp (fn-bpnf-held-list st))
           (fn-bpnj-host-eventp event)
           (bpw-host-pairsp (cdr pairs))))))
(assert-event
 (bpw-host-pairsp
  (list (list *bpw-raw* *bpw-boot*)
        (list *bpw-s0* (bpw-receive *bpw-local* 7))
        (list (fn-bpnf-answer-state *bpw-local-proposal*) (bpw-callback *bpw-local-proposal* :durable))
        (list *bpw-s1* (bpw-receive *bpw-peer* 8))
        (list (fn-bpnf-answer-state *bpw-transit-proposal*) (bpw-callback *bpw-transit-proposal* :durable))
        (list *bpw-s2* *bpw-tick*)
        (list (fn-bpnf-answer-state *bpw-deliver*) *bpw-busy-event*)
        (list (fn-bpnf-answer-state *bpw-busy-proposal*) (bpw-callback *bpw-busy-proposal* :durable))
        (list *bpw-deferred* *bpw-tick*)
        (list (fn-bpnf-answer-state *bpw-dispatch*) (bpw-callback *bpw-dispatch* :durable))
        (list *bpw-dispatched* *bpw-open-event*)
        (list (fn-bpnf-answer-state *bpw-attempt*) (bpw-callback *bpw-attempt* :refused))
        (list (fn-bpnf-answer-state *bpw-attempt-refused*) *bpw-open-event*)
        (list (fn-bpnf-answer-state *bpw-attempt2*) (bpw-callback *bpw-attempt2* :durable))
        (list *bpw-sending* *bpw-result-event*)
        (list (fn-bpnf-answer-state *bpw-result*) (bpw-callback *bpw-result* :refused)))))

; Reachability evidence: every expected transition really took its branch.
(assert-event
 (let* ((local (fn-bpnf-find-arrival 0 (fn-bpnf-held-list *bpw-deferred*)))
        (transit (fn-bpnf-find-arrival 1 (fn-bpnf-held-list *bpw-deferred*)))
        (wait (fn-bpnp-wait-for (fn-bpnp-wait-key local) *bpw-waits*)))
   (and local transit
        (not (equal (fn-bpnp-wait-key local) (fn-bpnp-wait-key transit)))
        (equal (fn-bpn-nth 3 (fn-bpnp-primary local)) *bpw-local*)
        (equal (fn-bpn-nth 3 (fn-bpnp-primary transit)) *bpw-peer*)
        (equal (fn-bpn-nth 13 local) '(:busy 1))
        (equal (fn-bpn-nth 2 wait) :busy)
        (fn-bpnp-busy-blockedp local *bpw-waits* *bpw-obs* 3)
        (null (fn-bpnp-wait-for (fn-bpnp-wait-key transit) *bpw-waits*)))))
(assert-event
 (and (equal (len (fn-bpnf-held-list *bpw-s2*)) 2)
      (equal (caar (fn-bpnf-answer-effects *bpw-deliver*)) :deliver)
      (equal (caar (fn-bpnf-answer-effects *bpw-busy-proposal*)) :persist-deferral)
      (consp *bpw-waits*)
      (equal (caar (fn-bpnf-answer-effects *bpw-dispatch*)) :persist-dispatch)
      (equal (caar (fn-bpnf-answer-effects *bpw-attempt*)) :persist-attempt)
      (equal (caar (fn-bpnf-answer-effects *bpw-attempt2*)) :persist-attempt)
      (equal (caar (fn-bpnf-answer-effects (bpw-settle *bpw-attempt2* :durable))) :cl-send)
      (equal (caar (fn-bpnf-answer-effects *bpw-result*)) :persist-forward-result)))

; Reachable positive witness: fn-bpnj-forward-result-proposal-preserves-waits.
; The theorem has no hypotheses; its literal conclusion is asserted below.
(assert-event
 (and (consp (fn-bpnp-waits *bpw-sending*))
      (equal (len (fn-bpnf-held-list *bpw-sending*)) 2)
      (equal (fn-bpnp-waits
              (fn-bpnf-answer-state
               (fn-bpnj-step *bpw-sending*
                             (list :forward-result (nth 1 *bpw-result-event*)
                                   (nth 2 *bpw-result-event*) *bpw-session* :sent *bpw-obs*))))
             (fn-bpnp-waits *bpw-sending*))))

; Reachable positive witnesses for both literal kind cases of
; fn-bpnj-forward-publication-refusal-preserves-waits-and-class.
(defmacro bpw-refusal-witness (proposal)
  `(let* ((st (fn-bpnf-answer-state ,proposal))
          (event (bpw-callback ,proposal :refused))
          (epoch (nth 1 event)) (op (nth 2 event))
          (answer (fn-bpnj-step st (list :persist-result epoch op :refused))))
     (and (consp (fn-bpnp-waits st))
          (member-equal (fn-bpn-nth 3 (fn-bpnf-issued st)) '(:attempt :forward-result))
          (equal (fn-bpnp-waits (fn-bpnf-answer-state answer)) (fn-bpnp-waits st))
          (iff (equal (fn-bpnf-answer-effects answer) '((:forward-answer :refused)))
               (and (fn-bpnf-operation-matchp (fn-bpnf-issued st) epoch op)
                    (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :pending)))
          (equal (fn-bpnf-answer-effects answer) '((:forward-answer :refused))))))
(assert-event (bpw-refusal-witness *bpw-attempt*))
(assert-event (bpw-refusal-witness *bpw-result*))

; Stale named result and rejected overlapping proposal both retain the
; complete nonempty wait table. The latter has an actual issued kind 9.
(assert-event
 (let* ((event (list :forward-result (nth 1 *bpw-result-event*)
                     (nth 2 *bpw-result-event*) '(1 . 9) :sent *bpw-obs*))
        (answer (fn-bpnj-step *bpw-sending* event)))
   (and (bpw-host-pairsp (list (list *bpw-sending* event)))
        (consp (fn-bpnp-waits *bpw-sending*))
        (equal (fn-bpnf-answer-state answer) *bpw-sending*)
        (equal (fn-bpnf-answer-effects answer)
               (list (list :forward-stale (nth 1 event) (nth 2 event) '(1 . 9))))
        (equal (fn-bpnp-waits (fn-bpnf-answer-state answer))
               (fn-bpnp-waits *bpw-sending*)))))
(assert-event
 (let* ((st (fn-bpnf-answer-state *bpw-result*))
        (answer (fn-bpnj-step st *bpw-result-event*)))
   (and (bpw-host-pairsp (list (list st *bpw-result-event*)))
        (consp (fn-bpnp-waits st))
        (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :forward-result)
        (equal (fn-bpnf-answer-state answer) st)
        (equal (fn-bpnf-answer-effects answer) '((:forward-answer :uncertain)))
        (equal (fn-bpnp-waits (fn-bpnf-answer-state answer))
               (fn-bpnp-waits st)))))

; A late refused callback from the earlier attempt cannot resolve the
; newly issued result. All literal refusal-theorem hypotheses still hold.
(assert-event
 (let* ((st (fn-bpnf-answer-state *bpw-result*))
        (event (bpw-callback *bpw-attempt* :refused))
        (epoch (nth 1 event)) (op (nth 2 event))
        (answer (fn-bpnj-step st event)))
   (and (bpw-host-pairsp (list (list st event)))
        (consp (fn-bpnp-waits st))
        (member-equal (fn-bpn-nth 3 (fn-bpnf-issued st)) '(:attempt :forward-result))
        (not (fn-bpnf-operation-matchp (fn-bpnf-issued st) epoch op))
        (equal answer (fn-bpnf-answer st nil))
        (equal (fn-bpnp-waits (fn-bpnf-answer-state answer)) (fn-bpnp-waits st))
        (iff (equal (fn-bpnf-answer-effects answer) '((:forward-answer :refused)))
             (and (fn-bpnf-operation-matchp (fn-bpnf-issued st) epoch op)
                  (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :pending))))))

; Hypothesis-removal witness: remove the one kind hypothesis. A reachable
; receive publication matches and is pending, but its refusal is classified
; as reception, so the literal conjunction's classification clause fails.
(assert-event
 (let* ((st (fn-bpnf-answer-state *bpw-transit-proposal*))
        (event (bpw-callback *bpw-transit-proposal* :refused))
        (epoch (nth 1 event)) (op (nth 2 event))
        (answer (fn-bpnj-step st (list :persist-result epoch op :refused))))
   (and (not (member-equal (fn-bpn-nth 3 (fn-bpnf-issued st)) '(:attempt :forward-result)))
        (fn-bpnf-operation-matchp (fn-bpnf-issued st) epoch op)
        (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :pending)
        (not (and (equal (fn-bpnp-waits (fn-bpnf-answer-state answer)) (fn-bpnp-waits st))
                  (iff (equal (fn-bpnf-answer-effects answer) '((:forward-answer :refused)))
                       (and (fn-bpnf-operation-matchp (fn-bpnf-issued st) epoch op)
                            (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :pending))))))))

; All intervening transitions retain the unrelated local wait, not just
; the final observation. Its backoff deadline still suppresses redelivery.
(assert-event
 (let* ((states (list (fn-bpnf-answer-state *bpw-dispatch*) *bpw-dispatched*
                      (fn-bpnf-answer-state *bpw-attempt*)
                      (fn-bpnf-answer-state *bpw-attempt-refused*)
                      (fn-bpnf-answer-state *bpw-attempt2*) *bpw-sending*
                      (fn-bpnf-answer-state *bpw-result*)
                      (fn-bpnf-answer-state *bpw-result-refused*))))
   (equal (list (fn-bpnp-waits (nth 0 states)) (fn-bpnp-waits (nth 1 states))
                (fn-bpnp-waits (nth 2 states)) (fn-bpnp-waits (nth 3 states))
                (fn-bpnp-waits (nth 4 states)) (fn-bpnp-waits (nth 5 states))
                (fn-bpnp-waits (nth 6 states)) (fn-bpnp-waits (nth 7 states)))
          (make-list 8 :initial-element *bpw-waits*))))
(assert-event
 (let* ((st (fn-bpnf-answer-state *bpw-result-refused*))
        (local (fn-bpnf-find-arrival 0 (fn-bpnf-held-list st))))
   (and (equal (fn-bpn-nth 13 local) '(:busy 1))
        (fn-bpnp-busy-blockedp local (fn-bpnp-waits st) *bpw-obs* 3)
        (null (fn-bpnf-answer-effects (fn-bpnj-step st *bpw-tick*))))))

; Mutation witnesses: the old rebuilding constructor pads slot 11 with nil.
; These are deliberately labeled mutations, never reachable counterexamples.
(assert-event
 (let* ((st (fn-bpnf-answer-state *bpw-result*))
        (old-proposal-state
         (fn-bpnp-with-runtime
          (fn-bpnp-with-credit
           (fn-bpnf-state-with-arrival
            (fn-bpnf-base st) (fn-bpnf-held-list st)
            (fn-bpnf-outcomes st) (fn-bpnf-handoffs st)
            (fn-bpnf-correlation st) (fn-bpnf-issued st)
            (fn-bpnf-waits st) (fn-bpnf-epoch st)
            (fn-bpnf-next-op st) (fn-bpnf-next-arrival st))
           (fn-bpnp-used st) (fn-bpnp-debt st))
          (fn-bpnp-sessions st) nil)))
   (and (consp (fn-bpnp-waits st))
        (null (fn-bpnp-waits old-proposal-state))
        (not (equal (fn-bpnp-waits old-proposal-state) (fn-bpnp-waits st))))))
(assert-event
 (and (consp *bpw-waits*)
      (not (equal (fn-bpnp-waits (fn-bpnp-with-issued
                                  (fn-bpnf-answer-state *bpw-attempt*) nil))
                  *bpw-waits*))
      (not (equal (fn-bpnp-waits (fn-bpnp-with-issued
                                  (fn-bpnf-answer-state *bpw-result*) nil))
                  *bpw-waits*))))

; Uncertainty deliberately clears volatile waits and fences; the next
; refused callback cannot resume it. This is an outcome distinct from refusal.
(assert-event
 (let* ((answer (bpw-settle *bpw-attempt* :uncertain))
        (st (fn-bpnf-answer-state answer)))
   (and (equal (fn-bpnf-answer-effects answer) '((:forward-answer :uncertain)))
        (null (fn-bpnp-waits st))
        (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :uncertain)
        (equal (fn-bpnj-step st (bpw-callback *bpw-attempt* :refused))
               (fn-bpnf-answer st nil)))))

; Literal positive: progress-dispatch antecedent and complete conclusion.
(assert-event
 (let ((st *bpw-deferred*)
       (answer (fn-bpnj-step *bpw-deferred* *bpw-tick*)))
   (and (true-listp st) (consp (fn-bpnp-waits st))
        (equal (fn-bpn-nth 0 (car (fn-bpnf-answer-effects answer))) :persist-dispatch)
        (equal (fn-bpnp-waits (fn-bpnf-answer-state answer))
               (fn-bpnp-prune-waits (fn-bpnp-waits st) (fn-bpnf-held-list st))))))

; Both known outcomes on a reachable pending dispatch, all antecedents.
(assert-event
 (let* ((st (fn-bpnf-answer-state *bpw-dispatch*))
        (event (bpw-callback *bpw-dispatch* :durable))
        (epoch (nth 1 event)) (op (nth 2 event))
        (durable (fn-bpnj-step st (list :persist-result epoch op :durable)))
        (refused (fn-bpnj-step st (list :persist-result epoch op :refused))))
   (and (consp (fn-bpnp-waits st))
        (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :dispatch)
        (member-equal :durable '(:durable :refused))
        (member-equal :refused '(:durable :refused))
        (not (equal (fn-bpn-nth 1 (car (fn-bpnf-answer-effects durable))) :uncertain))
        (not (equal (fn-bpn-nth 1 (car (fn-bpnf-answer-effects refused))) :uncertain))
        (equal (fn-bpnf-answer-effects refused) '((:dispatch-answer :refused)))
        (equal (fn-bpnp-waits (fn-bpnf-answer-state durable)) (fn-bpnp-waits st))
        (equal (fn-bpnp-waits (fn-bpnf-answer-state refused)) (fn-bpnp-waits st)))))


; Hypothesis removal: dispatch uncertainty satisfies the kind condition,
; fails the non-uncertain condition, and clears a nonempty wait table.
(assert-event
 (let* ((st (fn-bpnf-answer-state *bpw-dispatch*))
        (answer (bpw-settle *bpw-dispatch* :uncertain)))
   (and (consp (fn-bpnp-waits st))
        (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :dispatch)
        (equal (fn-bpn-nth 1 (car (fn-bpnf-answer-effects answer))) :uncertain)
        (not (equal (fn-bpnp-waits (fn-bpnf-answer-state answer)) (fn-bpnp-waits st))))))

; Corrupted-state hypothesis removal: an improper extension prevents the
; pruning writer from running; dispatch keeps the stale extra wait instead.
(assert-event
 (let* ((st (append
             (fn-bpnp-with-waits *bpw-deferred*
                                (cons '(:bpnp-wait (:gone) :route 0) *bpw-waits*))
             :bad-tail))
        (answer (fn-bpnj-step st *bpw-tick*)))
   (and (not (true-listp st))
        (equal (fn-bpn-nth 0 (car (fn-bpnf-answer-effects answer))) :persist-dispatch)
        (not (equal (fn-bpnp-waits (fn-bpnf-answer-state answer))
                    (fn-bpnp-prune-waits (fn-bpnp-waits st) (fn-bpnf-held-list st)))))))

 ; Remove dispatch kind: a reachable operator resume publishes count zero
; and drops its busy wait. The retained non-uncertain hypothesis holds.
(assert-event
 (let* ((proposal (fn-bpnj-step *bpw-deferred*
                               (list :operator-resume 0 (fn-bpnp-budgets 5000 1))))
        (st (fn-bpnf-answer-state proposal))
        (answer (bpw-settle proposal :durable)))
   (and (equal (fn-bpn-nth 0 (car (fn-bpnf-answer-effects proposal))) :persist-deferral)
        (consp (fn-bpnp-waits st))
        (not (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :dispatch))
        (not (equal (fn-bpn-nth 1 (car (fn-bpnf-answer-effects answer))) :uncertain))
        (not (equal (fn-bpnp-waits (fn-bpnf-answer-state answer)) (fn-bpnp-waits st))))))

; Remove proposal branch: absent routes add a transit wait. All retained
; hypotheses hold; the complete proposed dispatch conclusion is false.
(assert-event
 (let* ((st *bpw-deferred*)
        (answer (fn-bpnj-step st (list :progress *bpw-local* *bpw-obs* nil 1))))
   (and (true-listp st)
        (not (equal (fn-bpn-nth 0 (car (fn-bpnf-answer-effects answer))) :persist-dispatch))
        (not (equal (fn-bpnp-waits (fn-bpnf-answer-state answer))
                    (fn-bpnp-prune-waits (fn-bpnp-waits st) (fn-bpnf-held-list st)))))))
