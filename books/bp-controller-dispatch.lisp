; Actual BP consumer composition over registered CURRENT.
; NOT READY / unhooked until the registry's maintained guard/cost contracts,
; canonical precharge and epoch/job publication gate have been admitted.
; No native caller receives or supplies CURRENT.
(in-package "ACL2")
(include-book "bp-controller-registry-carry-guards")
(include-book "bp-node-job-offer-guards")
(include-book "bp-controller-current-shape")
(local (include-book "arithmetic-5/top" :dir :system))

; Fuel facts are about the actual readonly registered lookup. They do not
; authorize allocation or turn a fuel quantum into a resource grant.
(defthm fn-bpc-node-current-keeps-natural-fuel
  (implies (and (natp depth) (natp fuel))
    (and (natp (mv-nth 2
                (fn-bpc-node-current nonce local-slot physical-segment depth fuel fn-bpc-node)))
         (<= (mv-nth 2
               (fn-bpc-node-current nonce local-slot physical-segment depth fuel fn-bpc-node)) fuel)))
  :hints (("Goal"
    :induct (fn-bpc-node-current nonce local-slot physical-segment depth fuel fn-bpc-node)
    :in-theory (e/d (fn-bpc-node-current)
                    (fn-bpc-row-livep fn-bpc-issued-fencep))))
  :rule-classes nil)

(defthm fn-bpc-current-keeps-natural-fuel
  (implies (and (natp fuel) (fn-bp-controller-registryp fn-bp-controller-registry))
    (natp (mv-nth 2 (fn-bpc-current controller fuel fn-bp-controller-registry))))
  :hints (("Goal"
    :use ((:instance fn-bpc-node-current-keeps-natural-fuel
            (nonce (cadr controller)) (local-slot (mod (caddr controller) 64))
            (physical-segment (floor (caddr controller) 64))
            (depth (fn-bpcr-depth fn-bp-controller-registry))
            (fn-bpc-node (fn-bpcr-root fn-bp-controller-registry))))
    :in-theory (e/d (fn-bpc-current fn-bpc-tokenp fn-bp-controller-registryp)
                    (fn-bpc-node-current))))
  :rule-classes nil)

(defun fn-owner-bp-controller-step (controller event fuel fn-bp-controller-registry)
  (declare (xargs :stobjs fn-bp-controller-registry
                  :guard (and (natp fuel)
                              (fn-bpc-registry-carryp fn-bp-controller-registry))
                  :verify-guards nil))
  (mv-let (status current left)
      (fn-bpc-current controller fuel fn-bp-controller-registry)
    (if (not (equal status :current))
        (mv status nil left fn-bp-controller-registry)
      (if (not (fn-bpnj-host-eventp event))
          (mv :invalid-controller-event nil left fn-bp-controller-registry)
        (let ((answer (fn-bpnj-step current event)))
          (mv-let (installed remaining fn-bp-controller-registry)
              (fn-bpc-current-replace controller (fn-bpnf-epoch current)
               (fn-bpnf-issued current) (fn-bpnf-answer-state answer) left
               fn-bp-controller-registry)
            (mv installed
                (if (equal installed :updated) (fn-bpnf-answer-effects answer) nil)
                remaining fn-bp-controller-registry)))))))

(verify-guards fn-owner-bp-controller-step
  :hints (("Goal"
    :use ((:instance fn-bpc-current-carries-registered-current (token controller))
          (:instance fn-bpc-current-keeps-natural-fuel))
    :in-theory (e/d (fn-bpnp-step-guard-premisesp)
                    (fn-bpc-current fn-bpc-current-replace fn-bpnj-step
                     fn-bpc-registry-carryp fn-bpn-machine-invariantp
                     fn-bpn-machine-statep fn-bpnp-session-listp)))))

; The actual registered consumer retains the carried shape across dispatch
; and recovery; no native snapshot or served whole-state validator is used.
(defthm fn-owner-bp-controller-step-preserves-registry-carry
 (implies (fn-bpc-registry-carryp fn-bp-controller-registry)
  (fn-bpc-registry-carryp
   (mv-nth 3 (fn-owner-bp-controller-step controller event fuel fn-bp-controller-registry))))
 :hints (("Goal"
  :use ((:instance fn-bpc-current-carries-registered-current (token controller))
        (:instance fn-bpnj-step-preserves-current-list
          (st (mv-nth 1 (fn-bpc-current controller fuel fn-bp-controller-registry))))
        (:instance fn-bpnj-step-preserves-guard-premises
          (st (mv-nth 1 (fn-bpc-current controller fuel fn-bp-controller-registry))))
        (:instance fn-bpc-current-replace-preserves-registry-carry
          (token controller)
          (expected-epoch (fn-bpnf-epoch (mv-nth 1 (fn-bpc-current controller fuel fn-bp-controller-registry))))
          (expected-issued (fn-bpnf-issued (mv-nth 1 (fn-bpc-current controller fuel fn-bp-controller-registry))))
          (next-current (fn-bpnf-answer-state (fn-bpnj-step
            (mv-nth 1 (fn-bpc-current controller fuel fn-bp-controller-registry)) event)))
          (fuel (mv-nth 2 (fn-bpc-current controller fuel fn-bp-controller-registry)))))
  :in-theory (union-theories '(fn-owner-bp-controller-step) (theory 'minimal-theory))))
 :rule-classes nil)
