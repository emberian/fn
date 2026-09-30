; Actual registered dispatcher/recovery effects in a local concrete stobj.
; Unfunded storage fixture only: registration/runtime installation is absent.
(in-package "ACL2")
(include-book "../../books/bp-controller-dispatch")
(defconst *bpcd-initial*
  (fn-bpnf-initial-state
    (fn-bpn-config (cons :dtn '(47 47 98 112 45 108 111 99 97 108 47))
                   3600000 2 32 1048576) 8 1048576))
(defun bpcd-install (current fn-bp-controller-registry)
  (declare (xargs :stobjs fn-bp-controller-registry :guard t))
  (let ((fn-bp-controller-registry (update-fn-bpcr-highwater 1 fn-bp-controller-registry)))
    (stobj-let ((fn-bpc-node (fn-bpcr-root fn-bp-controller-registry)))
      (fn-bpc-node)
      (stobj-let ((fn-bpc-segment (fn-bpcn-children-get 'fn-bpc-segment fn-bpc-node (create-fn-bpc-segment))))
        (fn-bpc-segment)
        (update-fn-bpcs-rowsi 0 (list 7 :live current :unfunded-fixture nil) fn-bpc-segment)
        fn-bpc-node)
      fn-bp-controller-registry)))

(defconst *bpcd-recover* '(:recover-fnbs 1 nil :ready (:ready nil nil nil 0) 0 (:initialize)))
(defun bpcd-observe (old event fn-bp-controller-registry)
 (declare (xargs :stobjs fn-bp-controller-registry :verify-guards nil))
 (let* ((fn-bp-controller-registry (bpcd-install old fn-bp-controller-registry))
        (before (fn-bpc-registry-carryp fn-bp-controller-registry)))
  (mv-let (status effects fuel fn-bp-controller-registry)
    (fn-owner-bp-controller-step '(:bp-controller 7 0) event 6 fn-bp-controller-registry)
   (mv-let (read current left)
     (fn-bpc-current '(:bp-controller 7 0) 4 fn-bp-controller-registry)
    (declare (ignore left))
    (mv (list before (fn-bpnj-host-eventp event) status effects fuel
              (fn-bpc-registry-carryp fn-bp-controller-registry) read
              (true-listp current) (fn-bpnp-step-guard-premisesp current)
              (fn-bpnf-epoch current)) fn-bp-controller-registry)))))
(defun bpcd-fixture (old event)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-bp-controller-registry
  (mv-let (answer fn-bp-controller-registry)
   (bpcd-observe old event fn-bp-controller-registry) answer)))
; Complete carried antecedent and actual post-registry conclusion, plus
; actual recovery effects/installed epoch, never recording-core stubs.
(assert-event (equal (bpcd-fixture *bpcd-initial* *bpcd-recover*)
 '(t t :updated ((:restart-ready 0)) 4 t :current t t 1)))
; Actual dispatch preserves the same registered carry on an empty session.
(defconst *bpcd-session*
 (list :session (cons :dtn '(47 47 112 101 101 114 47)) (cons 1 1)
       t 4096 (fn-clock-observation 1000 0 0 nil)))
(assert-event (equal (bpcd-fixture *bpcd-initial* *bpcd-session*)
 '(t t :updated nil 4 t :current t t 0)))
; Invalid event is a named refusal and cannot expose effects.
(assert-event (equal (bpcd-fixture *bpcd-initial* '(:not-a-host-event))
 '(t nil :invalid-controller-event nil 5 t :current t t 0)))

(defun bpcd-corrupt-other-slot (fn-bp-controller-registry)
  (declare (xargs :stobjs fn-bp-controller-registry :guard t))
  (stobj-let ((fn-bpc-node (fn-bpcr-root fn-bp-controller-registry)))
    (fn-bpc-node)
    (stobj-let ((fn-bpc-segment (fn-bpcn-children-get 'fn-bpc-segment fn-bpc-node (create-fn-bpc-segment))))
      (fn-bpc-segment)
      (update-fn-bpcs-rowsi 1 '(9 :live (:bpnf-state) :corrupted-fixture nil) fn-bpc-segment)
      fn-bpc-node)
    fn-bp-controller-registry))

(defun bpcd-corrupt-other-fixture ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-bp-controller-registry
  (mv-let (answer fn-bp-controller-registry)
   (let ((fn-bp-controller-registry (bpcd-corrupt-other-slot fn-bp-controller-registry)))
    (bpcd-observe *bpcd-initial* *bpcd-session* fn-bp-controller-registry)) answer)))
; Logical corrupted-state hypothesis removal; executable guard correctly
; refuses this input. Guard checking is scoped to each logical
; counterexample expression. No served activation is tested.
; Hypothesis removal: unrelated corrupted slot keeps the whole registry
; carry false after an otherwise successful, proper guarded dispatch.
(assert-event (with-guard-checking :none (and (true-listp *bpcd-initial*)
 (fn-bpnp-step-guard-premisesp *bpcd-initial*)
 (fn-bpnj-host-eventp *bpcd-session*)
 (equal (bpcd-corrupt-other-fixture)
  '(nil t :updated nil 4 nil :current t t 0)))))
; Complete positive antecedent/conclusion for the structural job theorem.
(assert-event (and (true-listp *bpcd-initial*)
 (true-listp (fn-bpnf-answer-state (fn-bpnj-step *bpcd-initial* *bpcd-session*)))))
; Corrupted-state proper-list omission: stale job result returns the exact
; improper input, while its projected machine/session/held guard remains.
(defconst *bpcd-improper* (append *bpcd-initial* :improper-tail))
(assert-event (with-guard-checking :none (and (not (true-listp *bpcd-improper*))
 (fn-bpnp-step-guard-premisesp *bpcd-improper*)
 (not (true-listp (fn-bpnf-answer-state
  (fn-bpnj-step *bpcd-improper* '(:job-result nil nil :uncertain))))))))

; Literal progress-layer structural theorem has its own full positive and
; proper-list removal witness; the latter is logical corrupted-state data.
(assert-event (and (true-listp *bpcd-initial*)
 (true-listp (fn-bpnf-answer-state (fn-bpnp-step *bpcd-initial* *bpcd-session*)))))
(assert-event (with-guard-checking :none
 (and (not (true-listp *bpcd-improper*))
 (not (true-listp (fn-bpnf-answer-state (fn-bpnp-step *bpcd-improper* *bpcd-session*)))))))
