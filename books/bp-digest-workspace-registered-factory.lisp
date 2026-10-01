; INTERNAL storage composition only. No native/public allocating entry.
; Genuine installed family/BODY carry is a separate required prerequisite;
; stored :constructing phase and opaque allowance shape do not establish it.
(in-package "ACL2")
(include-book "bp-digest-install-stored-plan")
(include-book "bp-digest-workspace-factory")
(set-verify-guards-eagerness 2)

(defun fn-bpd-registered-factory-turn
 (controller workspace-token fuel fn-bp-controller-registry)
 (declare (xargs :stobjs fn-bp-controller-registry :guard (natp fuel)
  :guard-hints (("Goal" :in-theory
   (disable fn-owner-bp-digest-install-plan fn-bpd-node-install-turn)))))
 (mv-let (word plan left fn-bp-controller-registry)
  (fn-owner-bp-digest-install-plan controller workspace-token fuel fn-bp-controller-registry)
  (cond
   ((not (eq word :stored-plan)) (mv word left fn-bp-controller-registry))
   ((not (and (natp left) (<= left fuel)
              (fn-bpc-tokenp controller) (fn-bpd-factory-planp plan)))
    (mv :invalid-install-carry fuel fn-bp-controller-registry))
   ((zp left) (mv :yield left fn-bp-controller-registry))
   (t
    (let ((address (caddr controller)))
     (stobj-let ((fn-bpc-node (fn-bpcr-root fn-bp-controller-registry)))
      (result remaining fn-bpc-node)
      (if (not (fn-bpcn-children-boundp 'fn-bpd-workspace-node fn-bpc-node))
       (stobj-let ((fn-bpd-workspace-node
         (fn-bpcn-children-get 'fn-bpd-workspace-node fn-bpc-node
                              (create-fn-bpd-workspace-node))))
        (result fn-bpd-workspace-node)
        (mv :root-created fn-bpd-workspace-node)
        (mv result (1- left) fn-bpc-node))
       (stobj-let ((fn-bpd-workspace-node
         (fn-bpcn-children-get 'fn-bpd-workspace-node fn-bpc-node
                              (create-fn-bpd-workspace-node))))
        (result remaining fn-bpd-workspace-node)
        (fn-bpd-node-install-turn plan address left fn-bpd-workspace-node)
        (mv result remaining fn-bpc-node)))
      (mv result remaining fn-bp-controller-registry)))))))

; Actual public step refuses BEFORE lookup, plan construction or child factory
; while the selected operation-family/BODY issuer is absent. No supplied flag.
(defun fn-owner-bp-digest-install-step
 (controller workspace-token fuel fn-bp-controller-registry fn-page-read-pool)
 (declare (xargs :stobjs (fn-bp-controller-registry fn-page-read-pool)
  :guard (natp fuel))
  (ignore controller workspace-token))
 (mv :bp-runtime-unavailable fuel fn-bp-controller-registry fn-page-read-pool))
