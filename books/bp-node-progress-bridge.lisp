; The served BP step, fn-bpnp-step, and the lower machine fn-bpn-step.
;
; host/native/bp-service.lisp:172 (fnn-bps-foundation-step) calls
; fn-bpnp-step; fnn-bps-step (:178-179) wraps a lower machine event E as
; (:base E).  The lifecycle, send-authorization and no-release keystones of
; bp-node-machine, bp-node-machine-invariants and bp-node-machine-authorization
; are stated over fn-bpn-step.  This book is the named equation that makes
; them facts about the called subject: on (:base E) the served step answers
; exactly fn-bpn-step's effects and base state, or (when an operation is
; issued or a delivery is uncertain) nothing at all with the base unchanged.
(in-package "ACL2")
(include-book "bp-node-progress-premises")
(include-book "bp-node-machine-authorization")

;; ---------------------------------------------------------------------
;; Local shape facts.

(local
 (defthm bpnpb-base-of-slot-writers
  (and (equal (fn-bpnf-base (fn-bpnp-with-waits st w)) (fn-bpnf-base st))
       (equal (fn-bpnf-base (fn-bpnp-with-credit st u d)) (fn-bpnf-base st))
       (equal (fn-bpnf-base (fn-bpnp-with-runtime st s p)) (fn-bpnf-base st))
       (equal (fn-bpnf-answer-state (fn-bpnf-answer x e)) x)
       (equal (fn-bpnf-answer-effects (fn-bpnf-answer x e)) e))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnp-with-waits fn-bpnp-with-credit
                                fn-bpnp-with-runtime fn-bpnf-base
                                fn-bpnf-answer fn-bpnf-answer-state
                                fn-bpnf-answer-effects
                                fn-bpn-nth-is-nth-on-true-lists
                                nth-update-nth true-listp-update-nth
                                nfix natp car-cons cdr-cons nth-0-cons nth-add1
                                (:e equal) (:e natp) (:e nfix) (:e zp) (:e nth))
                              (theory 'minimal-theory))))))

(local
 (defthm bpnpb-with-base-fields
  (and (equal (fn-bpnf-base (fn-bpnf-with-base st b)) b)
       (equal (fn-bpnf-issued (fn-bpnf-with-base st b)) (fn-bpnf-issued st)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnf-with-base fn-bpnf-state-with-arrival
                                fn-bpnf-base fn-bpnf-issued fn-bpn-nth
                                fn-cbor-ag-car car-cons cdr-cons
                                (:e equal) (:e natp) (:e zp) (:e binary-+)
                                (:e not))
                              (theory 'minimal-theory))))))

(local
 (defthm bpnpb-base-event-shape
  (and (equal (fn-cbor-ag-car (list :base e)) :base)
       (equal (fn-bpn-nth 1 (list :base e)) e))
  :hints (("Goal" :in-theory (enable fn-cbor-ag-car fn-bpn-nth)))))

;; ---------------------------------------------------------------------
;; KEYSTONE (bridge).  On a lower machine event (:base E) the host-called
;; step answers exactly fn-bpn-step's base state and effects when no FNBS
;; operation is issued and no delivery is uncertain; otherwise it answers no
;; effect and leaves the base unchanged.  The credit, wait and session slots
;; the served step adds never touch the base or the effects.

(defthm fn-bpnp-step-base-event-refines-fn-bpn-step
  (let ((ans (fn-bpnp-step st (list :base e)))
        (low (fn-bpn-step (fn-bpnf-base st) e)))
    (if (and (not (fn-bpnf-issued st))
             (not (fn-bpah-delivery-uncertainp st)))
        (and (equal (fn-bpnf-base (fn-bpnf-answer-state ans))
                    (fn-bpn-answer-state low))
             (equal (fn-bpnf-answer-effects ans)
                    (fn-bpn-answer-effects low)))
      (and (equal (fn-bpnf-base (fn-bpnf-answer-state ans))
                  (fn-bpnf-base st))
           (null (fn-bpnf-answer-effects ans)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnp-step fn-bpnp-delegate-with-credit
                         fn-bpn-report-author-step fn-bpn-report-step
                         fn-bpnf-fragment-step fn-bpnf-step
                         fn-bpnp-preserve-runtime-answer
                         fn-bpn-report-delete-issuedp fn-bpnf-family-issuedp
                         fn-bpnp-credit-proposal-kind
                         fn-bpnp-domain-recover-eventp fn-bpnp-conflict-held
                         bpnpb-base-of-slot-writers bpnpb-with-base-fields bpnpb-base-event-shape
                         (:e fn-cbor-ag-car) (:e fn-bpn-nth)
                         car-cons cdr-cons natp zp (:e zp) (:e natp))
                       (theory 'minimal-theory))))
  :rule-classes nil)

;; ---------------------------------------------------------------------
;; Confinement over every event of the served step.  One lemma per step,
;; each opening only that step; the lower machine's typed-effect keystones
;; close the fn-bpn-step, fn-bpn-propose and fn-bpn-restart-step arms.

(defun fn-bpnpb-effects-confinedp (effects)
  (declare (xargs :guard t :verify-guards nil))
  (and (not (fn-bpn-effect-kind-memberp :release effects))
       (not (fn-bpn-effect-kind-memberp :receipt-prepare effects))))

(local
 (defthm bpnpb-kind-memberp-cons
  (equal (fn-bpn-effect-kind-memberp k (cons a b))
         (or (equal k (car a)) (fn-bpn-effect-kind-memberp k b)))
  :hints (("Goal" :in-theory (enable fn-bpn-effect-kind-memberp)))))

(local
 (defthm bpnpb-kind-memberp-atom
  (implies (atom x) (not (fn-bpn-effect-kind-memberp k x)))
  :hints (("Goal" :in-theory (enable fn-bpn-effect-kind-memberp)))))

(local
 (defthm bpnpb-confined-of-typed
  (implies (fn-bpn-effect-listp effects)
           (fn-bpnpb-effects-confinedp effects))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnpb-effects-confinedp
                                fn-bpn-effect-listp-excludes-release
                                fn-bpn-effect-listp-excludes-receipt-prepare)
                              (theory 'minimal-theory))))))

(local
 (defthm bpnpb-propose-confined
  (implies (not (member-equal (fn-cbor-ag-car refusal) '(:release :receipt-prepare)))
           (fn-bpnpb-effects-confinedp
            (fn-bpn-answer-effects
             (fn-bpn-propose st record success refusal uncertain))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnpb-effects-confinedp fn-bpn-propose
                                fn-bpn-answer fn-bpn-answer-effects
                                fn-cbor-ag-car car-cons cdr-cons
                                (:e member-equal)
                                bpnpb-kind-memberp-cons
                                bpnpb-kind-memberp-atom)
                              (theory 'minimal-theory))))))

(local
 (defthm bpnpb-bpn-step-confined
  (fn-bpnpb-effects-confinedp (fn-bpn-answer-effects (fn-bpn-step st e)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnpb-effects-confinedp
                                fn-bpn-step-emits-no-release-from-actual-effects
                                fn-bpn-step-emits-no-receipt-prepare)
                              (theory 'minimal-theory))))))

(local
 (defthm bpnpb-restart-step-confined
  (fn-bpnpb-effects-confinedp
   (fn-bpn-answer-effects (fn-bpn-restart-step st records ready)))
  :hints (("Goal" :in-theory (union-theories
                              '(bpnpb-confined-of-typed
                                fn-bpn-restart-step-effects-are-typed)
                              (theory 'minimal-theory))))))

(local
 (defthm bpnpb-confined-of-literals
  (and (fn-bpnpb-effects-confinedp nil)
       (equal (fn-bpnpb-effects-confinedp (cons a b))
              (and (not (equal (car a) :release))
                   (not (equal (car a) :receipt-prepare))
                   (fn-bpnpb-effects-confinedp b))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnpb-effects-confinedp bpnpb-kind-memberp-cons
                                bpnpb-kind-memberp-atom (:e fn-bpnpb-effects-confinedp))
                              (theory 'minimal-theory))))))

(local
 (deftheory bpnpb-theory
  (union-theories
   '(bpnpb-base-of-slot-writers bpnpb-confined-of-literals
     bpnpb-propose-confined bpnpb-bpn-step-confined bpnpb-restart-step-confined
     car-cons cdr-cons (:e fn-cbor-ag-car) (:e member-equal) (:e car)
     (:e fn-bpnpb-effects-confinedp))
   (theory 'minimal-theory))))

(local
 (defmacro fn-bpnpb-defquiet (name call defs)
  `(defthm ,name
     (fn-bpnpb-effects-confinedp (fn-bpnf-answer-effects ,call))
     :hints (("Goal" :do-not-induct t
              :in-theory (union-theories ',defs (theory 'bpnpb-theory)))))))

(local
 (fn-bpnpb-defquiet bpnpb-deliver-step (fn-bpah-deliver-step st key node)
  (fn-bpah-deliver-step)))

(local
 (fn-bpnpb-defquiet bpnpb-deliver-result-step
  (fn-bpah-deliver-result-step st epoch marker-id key status detail)
  (fn-bpah-deliver-result-step)))

(local
 (fn-bpnpb-defquiet bpnpb-persist-delivery-step
  (fn-bpah-persist-delivery-step st epoch operation-id result)
  (fn-bpah-persist-delivery-step)))

(local
 (fn-bpnpb-defquiet bpnpb-recover-fnbs-step
  (fn-bpnf-recover-fnbs-step st new-epoch base-records sequence-ready replay-result)
  (fn-bpnf-recover-fnbs-step)))

(local
 (fn-bpnpb-defquiet bpnpb-foundation-step (fn-bpnf-step st event)
  (fn-bpnf-step bpnpb-deliver-step bpnpb-deliver-result-step
   bpnpb-persist-delivery-step bpnpb-recover-fnbs-step)))

(local
 (fn-bpnpb-defquiet bpnpb-family-propose-step
  (fn-bpnf-family-propose-step st anchor-arrival observation)
  (fn-bpnf-family-propose-step)))

(local
 (fn-bpnpb-defquiet bpnpb-family-persist-step
  (fn-bpnf-family-persist-step st epoch op result)
  (fn-bpnf-family-persist-step)))

(local
 (fn-bpnpb-defquiet bpnpb-fragment-step (fn-bpnf-fragment-step st event)
  (fn-bpnf-fragment-step bpnpb-foundation-step bpnpb-family-propose-step
   bpnpb-family-persist-step)))

(local
 (fn-bpnpb-defquiet bpnpb-delete-propose-step
  (fn-bpn-report-delete-propose-step st observation enabled)
  (fn-bpn-report-delete-propose-step)))

(local
 (fn-bpnpb-defquiet bpnpb-delete-persist-step
  (fn-bpn-report-delete-persist-step st epoch op result)
  (fn-bpn-report-delete-persist-step)))

(local
 (fn-bpnpb-defquiet bpnpb-report-step (fn-bpn-report-step st event)
  (fn-bpn-report-step bpnpb-fragment-step bpnpb-delete-propose-step
   bpnpb-delete-persist-step)))

(local
 (fn-bpnpb-defquiet bpnpb-queue-step
  (fn-bpn-report-queue-step st arrival sequence route observation)
  (fn-bpn-report-queue-step fn-cbor-ag-car (:e member-equal))))

(local
 (fn-bpnpb-defquiet bpnpb-report-author-step (fn-bpn-report-author-step st event)
  (fn-bpn-report-author-step bpnpb-report-step bpnpb-queue-step)))

(local
 (fn-bpnpb-defquiet bpnpb-credit-refusal (fn-bpnp-credit-refusal st event kind)
  (fn-bpnp-credit-refusal bpnpb-report-author-step)))

(local
 (fn-bpnpb-defquiet bpnpb-delegate-with-credit (fn-bpnp-delegate-with-credit st event)
  (fn-bpnp-delegate-with-credit bpnpb-report-author-step bpnpb-credit-refusal
   fn-bpnp-publication-fault-effect)))

(local
 (fn-bpnpb-defquiet bpnpb-transit-dispatch-step
  (fn-bpnp-transit-dispatch-step st h peer node)
  (fn-bpnp-transit-dispatch-step)))

(local
 (defthm bpnpb-busy-stranded-effects-confined
   (fn-bpnpb-effects-confinedp (fn-bpnp-busy-stranded-effects held budget))
   :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnp-busy-stranded-effects
                                fn-bpnpb-effects-confinedp
                                fn-bpn-effect-kind-memberp
                                car-cons cdr-cons
                                (:executable-counterpart equal)
                                (:executable-counterpart not)
                                (:executable-counterpart fn-bpn-effect-kind-memberp))
                              (theory 'minimal-theory))))))

(local
 (fn-bpnpb-defquiet bpnpb-progress-step
  (fn-bpnp-progress-step st node observation routes generation budget)
  (fn-bpnp-progress-step bpnpb-deliver-step bpnpb-transit-dispatch-step
   bpnpb-busy-stranded-effects-confined)))

(local
 (fn-bpnpb-defquiet bpnpb-dispatch-persist-step
  (fn-bpnp-dispatch-persist-step st epoch op result)
  (fn-bpnp-dispatch-persist-step)))

(local
 (fn-bpnpb-defquiet bpnpb-clock-domain-fence
  (fn-bpnp-clock-domain-fence st plan)
  (fn-bpnp-clock-domain-fence)))

(local
 (fn-bpnpb-defquiet bpnpb-conflict-propose-step
  (fn-bpnp-conflict-propose-step st event h)
  (fn-bpnp-conflict-propose-step fn-bpnp-conflict-refusal)))

(local
 (fn-bpnpb-defquiet bpnpb-conflict-persist-step
  (fn-bpnp-conflict-persist-step st epoch op result)
  (fn-bpnp-conflict-persist-step fn-bpnp-conflict-refusal)))

;; BP-R17's busy answer proposes the kind 20, or answers the credit wait or
;; the host's :delivery-answer; its persist arm answers the deferral, the
;; stranded or resumed report, or its own publication answer.
(local
 (fn-bpnpb-defquiet bpnpb-busy-delivery-step
  (fn-bpnp-busy-delivery-step st epoch op key observation budgets)
  (fn-bpnp-busy-delivery-step)))

(local
 (fn-bpnpb-defquiet bpnpb-deferral-persist-step
  (fn-bpnp-deferral-persist-step st epoch op result)
  (fn-bpnp-deferral-persist-step fn-bpnp-deferral-effects)))

(local
 (fn-bpnpb-defquiet bpnpb-busy-resume-step
  (fn-bpnp-busy-resume-step st arrival budget)
  (fn-bpnp-busy-resume-step)))
;; N16's rotation arms answer only their own publication effects
;; (:persist-checkpoint, :generation-selected, :rotation-refused,
;; :rotation-uncertain): a journal generation's selection discharges no
;; application obligation, so they sit inside the confined set.
(local
 (fn-bpnpb-defquiet bpnpb-rotate-step
  (fn-bpnp-rotate-step st generation ck)
  (fn-bpnp-rotate-step)))

(local
 (fn-bpnpb-defquiet bpnpb-rotation-persist-step
  (fn-bpnp-rotation-persist-step st epoch op result)
  (fn-bpnp-rotation-persist-step)))

;; The stranded report of the kind-8 retry policy is neither a release nor
;; a receipt preparation.
(local
 (defthm bpnpb-stranded-effects-confined
   (fn-bpnpb-effects-confinedp (fn-bpnp-stranded-effects held peer epoch budget))
   :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnp-stranded-effects
                                fn-bpnpb-effects-confinedp
                                fn-bpn-effect-kind-memberp
                                car-cons cdr-cons
                                (:executable-counterpart equal)
                                (:executable-counterpart not)
                                (:executable-counterpart fn-bpn-effect-kind-memberp))
                              (theory 'minimal-theory))))))

(local
 (fn-bpnpb-defquiet bpnpb-start-one
  (fn-bpnp-start-one st peer session mru observation budget)
  (fn-bpnp-start-one bpnpb-stranded-effects-confined)))

;; The routed :session arm (spec 4.6) answers start-one's effects or one
;; :forward-no-route report.
(local
 (defthm bpnpb-no-route-report-confined
   (fn-bpnpb-effects-confinedp (list (list :forward-no-route arrival hop decision)))
   :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnpb-effects-confinedp
                                fn-bpn-effect-kind-memberp
                                car-cons cdr-cons
                                (:executable-counterpart equal)
                                (:executable-counterpart not)
                                (:executable-counterpart fn-bpn-effect-kind-memberp))
                              (theory 'minimal-theory))))))

(local
 (fn-bpnpb-defquiet bpnpb-routed-start
  (fn-bpnp-routed-start st peer session mru observation via budget)
  (fn-bpnp-routed-start bpnpb-start-one bpnpb-no-route-report-confined)))

(local
 (fn-bpnpb-defquiet bpnpb-attempt-persist-step
  (fn-bpnp-attempt-persist-step st epoch op result)
  (fn-bpnp-attempt-persist-step)))

(local
 (fn-bpnpb-defquiet bpnpb-forward-result-propose-step
  (fn-bpnp-forward-result-propose-step st attempt-epoch attempt-op session outcome observation)
  (fn-bpnp-forward-result-propose-step)))

(local
 (fn-bpnpb-defquiet bpnpb-operator-resume-step
  (fn-bpnp-operator-resume-step st arrival budget)
  (fn-bpnp-operator-resume-step)))

(local
 (fn-bpnpb-defquiet bpnpb-forward-result-persist-step
  (fn-bpnp-forward-result-persist-step st epoch op result)
  (fn-bpnp-forward-result-persist-step)))

(local
 (defthm bpnpb-preserve-runtime-answer
  (equal (fn-bpnf-answer-effects (fn-bpnp-preserve-runtime-answer answer st recovery))
         (fn-bpnf-answer-effects answer))
  :hints (("Goal" :in-theory (union-theories '(fn-bpnp-preserve-runtime-answer)
                                             (theory 'bpnpb-theory))))))

(local
 (defthm bpnpb-step-confined-lemma
  (fn-bpnpb-effects-confinedp (fn-bpnf-answer-effects (fn-bpnp-step st event)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnp-step bpnpb-start-one bpnpb-routed-start
                         bpnpb-forward-result-propose-step bpnpb-progress-step
                         bpnpb-operator-resume-step
                         bpnpb-dispatch-persist-step bpnpb-attempt-persist-step
                         bpnpb-forward-result-persist-step
                         bpnpb-clock-domain-fence bpnpb-conflict-propose-step
                         bpnpb-conflict-persist-step bpnpb-busy-delivery-step
                         bpnpb-deferral-persist-step bpnpb-busy-resume-step
                         bpnpb-rotate-step bpnpb-rotation-persist-step
                         bpnpb-delegate-with-credit bpnpb-preserve-runtime-answer)
                       (theory 'bpnpb-theory))))
  :rule-classes nil))

;; KEYSTONE (confinement).  No event of the host-called step answers a
;; :release or a :receipt-prepare effect: transport completion, expiry,
;; delivery and recovery never discharge an application obligation here.
;; The one release path is the receipt join of bp-release, whose keystone is
;; fn-bprl-no-receipt-no-release-no-peer-reliance.

(defthm fn-bpnp-step-emits-no-release-and-no-receipt-prepare
  (let ((effects (fn-bpnf-answer-effects (fn-bpnp-step st event))))
    (and (not (fn-bpn-effect-kind-memberp :release effects))
         (not (fn-bpn-effect-kind-memberp :receipt-prepare effects))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance bpnpb-step-confined-lemma))
           :in-theory (union-theories '(fn-bpnpb-effects-confinedp)
                                      (theory 'minimal-theory)))))

;; Corollaries of the bridge, not registry keystones: the lower machine's
;; lifecycle and send-authorization keystones restated over the called step.

(defthm fn-bpnp-step-base-event-preserves-lifecycle-invariant-by-bridge
  (implies (and (fn-bpn-lifecycle-invariantp (fn-bpnf-base st))
                (fn-bpn-machine-eventp e))
           (fn-bpn-lifecycle-invariantp
            (fn-bpnf-base (fn-bpnf-answer-state (fn-bpnp-step st (list :base e))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-step-base-event-refines-fn-bpn-step)
                 (:instance fn-bpn-step-preserves-lifecycle-invariant
                            (st (fn-bpnf-base st)) (event e)))
           :in-theory (theory 'minimal-theory))))

(defthm fn-bpnp-step-base-event-cl-send-is-authorized-by-durable-attempt-record-by-bridge
  (implies
   (and (fn-bpn-lifecycle-invariantp (fn-bpnf-base st))
        (fn-bpn-effect-kind-memberp
         :cl-send (fn-bpnf-answer-effects (fn-bpnp-step st (list :base e)))))
   (let* ((pending (fn-bpn-machine-state-pending (fn-bpnf-base st)))
          (record (fn-bpn-pending-record pending)))
     (and (not (fn-bpnf-issued st))
          (not (fn-bpah-delivery-uncertainp st))
          pending
          (equal (car e) :persist-result)
          (equal (nth 1 e) (fn-bpn-pending-token pending))
          (equal (nth 2 e) :durable)
          (equal (fn-cbor-ag-car record) :attempting)
          (fn-bpn-record-applicablep (fn-bpnf-base st) record)
          (equal (fn-bpnf-answer-effects (fn-bpnp-step st (list :base e)))
                 (fn-bpn-pending-success-effects pending)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-step-base-event-refines-fn-bpn-step)
                 (:instance fn-bpn-step-cl-send-is-authorized-by-durable-attempt-record
                            (st (fn-bpnf-base st)) (event e)))
           :in-theory (union-theories '(bpnpb-kind-memberp-atom (:e atom))
                                      (theory 'minimal-theory)))))

