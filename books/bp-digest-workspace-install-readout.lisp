; BP storage readout for the SAME-pool publication consumer. Bound storage
; and exact captured identity do not by themselves authorize C->U transfer.
(in-package "ACL2")
(include-book "bp-digest-workspace-factory")
(include-book "bp-digest-install-stored-plan")
(set-verify-guards-eagerness 2)

(defun fn-bpd-install-readout-planp (plan)
 (declare (xargs :guard t))
 (let ((source (fn-bpn-nth 4 plan)))
  (and (fn-bpd-factory-planp plan)
       (consp source) (eq (car source) :bp-checkpoint-stage)
       (consp (cdr source)) (consp (cddr source)) (null (cdddr source))
       (equal (cadr source) (fn-bpn-nth 3 plan))
       (natp (caddr source)))))

; Fixed metadata only. In particular a new workspace nonce for the SAME job
; cannot adopt a prior carry simply because controller/job/revision match.
(defun fn-bpd-carry-install-readout (plan fn-bpd-workspace-carry)
 (declare (xargs :stobjs fn-bpd-workspace-carry :guard t))
 (let* ((token (fn-bpn-nth 1 plan)) (source (fn-bpn-nth 4 plan))
        (captured (fn-bpd-source fn-bpd-workspace-carry)))
  (cond
   ((not (fn-bpd-install-readout-planp plan)) :stale-install)
   ((not (and (equal (fn-bpn-nth 2 plan) (fn-bpd-controller fn-bpd-workspace-carry))
              (equal (fn-bpn-nth 3 plan) (fn-bpd-job fn-bpd-workspace-carry))
              (equal (fn-bpn-nth 1 token) (fn-bpd-nonce fn-bpd-workspace-carry))
              (equal (fn-bpn-nth 6 plan) (fn-bpd-revision fn-bpd-workspace-carry))
              (equal (fn-bpn-nth 0 source) (fn-bpn-nth 0 captured))
              (equal (fn-bpn-nth 1 source) (fn-bpn-nth 1 captured))
              (equal (fn-bpn-nth 2 source) (fn-bpn-nth 2 captured))))
    :stale-workspace)
   ((eq (fn-bpd-phase fn-bpd-workspace-carry) :constructing) :storage-ready)
   ((eq (fn-bpd-phase fn-bpd-workspace-carry) :installed) :already-installed)
   ((eq (fn-bpd-phase fn-bpd-workspace-carry) :fenced) :workspace-fenced)
   (t :workspace-unavailable))))

(local (defthm fn-bpd-readout-address-natural
 (implies (natp address) (natp (floor address 2)))
 :hints (("Goal" :in-theory (disable floor)))))

(defun fn-bpd-node-install-readout (plan address fuel fn-bpd-workspace-node)
 (declare (xargs :stobjs fn-bpd-workspace-node :measure (nfix fuel)
  :guard (and (natp address) (natp fuel))
  :guard-hints (("Goal" :in-theory (disable floor mod)))))
 (cond
  ((zp fuel) (mv :yield fuel))
  ((zp address)
   (if (not (and (fn-bpd-children-boundp 'pgs-digest-state fn-bpd-workspace-node)
                 (fn-bpd-children-boundp 'fn-bpd-workspace-carry fn-bpd-workspace-node)))
    (mv :workspace-unavailable (1- fuel))
    (stobj-let ((fn-bpd-workspace-carry
      (fn-bpd-children-get 'fn-bpd-workspace-carry fn-bpd-workspace-node
                          (create-fn-bpd-workspace-carry))))
     (word)
     (fn-bpd-carry-install-readout plan fn-bpd-workspace-carry)
     (mv word (1- fuel)))))
  ((equal (mod address 2) 0)
   (if (not (fn-bpd-children-boundp 'fn-bpd-workspace-left fn-bpd-workspace-node))
    (mv :workspace-unavailable (1- fuel))
    (stobj-let ((fn-bpd-workspace-left
      (fn-bpd-children-get 'fn-bpd-workspace-left fn-bpd-workspace-node
                          (create-fn-bpd-workspace-left))))
     (word left)
     (fn-bpd-node-install-readout plan (floor address 2) (1- fuel) fn-bpd-workspace-left)
     (mv word left))))
  (t
   (if (not (fn-bpd-children-boundp 'fn-bpd-workspace-right fn-bpd-workspace-node))
    (mv :workspace-unavailable (1- fuel))
    (stobj-let ((fn-bpd-workspace-right
      (fn-bpd-children-get 'fn-bpd-workspace-right fn-bpd-workspace-node
                          (create-fn-bpd-workspace-right))))
     (word left)
     (fn-bpd-node-install-readout plan (floor address 2) (1- fuel) fn-bpd-workspace-right)
     (mv word left))))))

; Publication consumes this actual registered readout, not the weaker
; controller/job-only storage status or a host-supplied row snapshot.
(defun fn-bpd-registered-install-readout
 (controller workspace-token fuel fn-bp-controller-registry)
 (declare (xargs :stobjs fn-bp-controller-registry :guard (natp fuel)
  :guard-hints (("Goal" :in-theory
   (disable fn-owner-bp-digest-install-plan fn-bpd-node-install-readout)))))
 (mv-let (word plan left fn-bp-controller-registry)
  (fn-owner-bp-digest-install-plan controller workspace-token fuel fn-bp-controller-registry)
  (cond
   ((not (eq word :stored-plan)) (mv word left fn-bp-controller-registry))
   ((not (and (natp left) (<= left fuel) (fn-bpc-tokenp controller)))
    (mv :invalid-install-carry fuel fn-bp-controller-registry))
   ((zp left) (mv :yield left fn-bp-controller-registry))
   (t
    (let ((address (caddr controller)))
     (stobj-let ((fn-bpc-node (fn-bpcr-root fn-bp-controller-registry)))
      (result remaining)
      (if (not (fn-bpcn-children-boundp 'fn-bpd-workspace-node fn-bpc-node))
       (mv :workspace-unavailable (1- left))
       (stobj-let ((fn-bpd-workspace-node
         (fn-bpcn-children-get 'fn-bpd-workspace-node fn-bpc-node
                              (create-fn-bpd-workspace-node))))
        (result remaining)
        (fn-bpd-node-install-readout plan address left fn-bpd-workspace-node)
        (mv result remaining)))
      (mv result remaining fn-bp-controller-registry)))))))
