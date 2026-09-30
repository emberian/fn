; Internal storage publication AFTER actual SAME-pool promotion. This is not
; a public allocator/transfer gate. The physical caller must establish genuine
; operation allowance and qualified successor domain before entry. Promoting
; cuts never retry C->U. Installed carry alone does not expose a workspace.
(in-package "ACL2")
(include-book "bp-digest-workspace-install-readout")
(set-verify-guards-eagerness 2)

(defun fn-bpd-carry-publication-identityp (plan fn-bpd-workspace-carry)
 (declare (xargs :stobjs fn-bpd-workspace-carry :guard t))
 (let ((token (fn-bpn-nth 1 plan)) (source (fn-bpn-nth 4 plan))
       (actual (fn-bpd-source fn-bpd-workspace-carry)))
  (and (fn-bpd-install-readout-planp plan)
       (equal (fn-bpn-nth 2 plan) (fn-bpd-controller fn-bpd-workspace-carry))
       (equal (fn-bpn-nth 3 plan) (fn-bpd-job fn-bpd-workspace-carry))
       (equal (fn-bpn-nth 1 token) (fn-bpd-nonce fn-bpd-workspace-carry))
       (equal (fn-bpn-nth 0 source) (fn-bpn-nth 0 actual))
       (equal (fn-bpn-nth 1 source) (fn-bpn-nth 1 actual))
       (equal (fn-bpn-nth 2 source) (fn-bpn-nth 2 actual)))))

(defun fn-bpd-carry-publish (original-plan final-revision fn-bpd-workspace-carry)
 (declare (xargs :stobjs fn-bpd-workspace-carry :guard (natp final-revision)))
 (cond
  ((not (fn-bpd-carry-publication-identityp original-plan fn-bpd-workspace-carry))
   (mv :stale-workspace fn-bpd-workspace-carry))
  ((eq (fn-bpd-phase fn-bpd-workspace-carry) :installed)
   (mv (if (equal (fn-bpd-revision fn-bpd-workspace-carry) final-revision)
           :carry-already-installed :stale-workspace) fn-bpd-workspace-carry))
  ((not (and (eq (fn-bpd-phase fn-bpd-workspace-carry) :constructing)
             (equal (fn-bpd-revision fn-bpd-workspace-carry)
                    (fn-bpn-nth 6 original-plan))))
   (mv :workspace-fenced fn-bpd-workspace-carry))
  (t
   (let ((fn-bpd-workspace-carry
           (update-fn-bpd-revision final-revision fn-bpd-workspace-carry)))
    ;; Installed is published last. Actual intent must independently publish
    ;; the SAME final revision before any registered read can expose it.
    (mv :carry-published (update-fn-bpd-phase :installed fn-bpd-workspace-carry))))))

(local (defthm fn-bpd-publication-address-natural
 (implies (natp address) (natp (floor address 2)))
 :hints (("Goal" :in-theory (disable floor)))))

(defun fn-bpd-node-publish (original-plan final-revision address fuel fn-bpd-workspace-node)
 (declare (xargs :stobjs fn-bpd-workspace-node :measure (nfix fuel)
  :guard (and (natp final-revision) (natp address) (natp fuel))
  :guard-hints (("Goal" :in-theory (disable floor mod)))))
 (cond
  ((zp fuel) (mv :yield fuel fn-bpd-workspace-node))
  ((zp address)
   (if (not (and (fn-bpd-children-boundp 'pgs-digest-state fn-bpd-workspace-node)
                 (fn-bpd-children-boundp 'fn-bpd-workspace-carry fn-bpd-workspace-node)))
    (mv :workspace-unavailable (1- fuel) fn-bpd-workspace-node)
    (stobj-let ((fn-bpd-workspace-carry
      (fn-bpd-children-get 'fn-bpd-workspace-carry fn-bpd-workspace-node
                           (create-fn-bpd-workspace-carry))))
     (word fn-bpd-workspace-carry)
     (fn-bpd-carry-publish original-plan final-revision fn-bpd-workspace-carry)
     (mv word (1- fuel) fn-bpd-workspace-node))))
  ((equal (mod address 2) 0)
   (if (not (fn-bpd-children-boundp 'fn-bpd-workspace-left fn-bpd-workspace-node))
    (mv :workspace-unavailable (1- fuel) fn-bpd-workspace-node)
    (stobj-let ((fn-bpd-workspace-left
      (fn-bpd-children-get 'fn-bpd-workspace-left fn-bpd-workspace-node
                           (create-fn-bpd-workspace-left))))
     (word left fn-bpd-workspace-left)
     (fn-bpd-node-publish original-plan final-revision (floor address 2) (1- fuel)
                          fn-bpd-workspace-left)
     (mv word left fn-bpd-workspace-node))))
  (t
   (if (not (fn-bpd-children-boundp 'fn-bpd-workspace-right fn-bpd-workspace-node))
    (mv :workspace-unavailable (1- fuel) fn-bpd-workspace-node)
    (stobj-let ((fn-bpd-workspace-right
      (fn-bpd-children-get 'fn-bpd-workspace-right fn-bpd-workspace-node
                           (create-fn-bpd-workspace-right))))
     (word left fn-bpd-workspace-right)
     (fn-bpd-node-publish original-plan final-revision (floor address 2) (1- fuel)
                          fn-bpd-workspace-right)
     (mv word left fn-bpd-workspace-node))))))

; Internal physical composition only. Native receives neither the plan nor
; a supplied final revision/boolean. No callback installation/export here.
(defun fn-bpd-registered-publish-carry
 (controller workspace-token fuel fn-bp-controller-registry)
 (declare (xargs :stobjs fn-bp-controller-registry :guard (natp fuel)
  :guard-hints (("Goal" :in-theory
   (disable fn-bpcc-pending-capture fn-bpd-node-publish
            fn-bpck-control-matches-current-p)))))
 (mv-let (word job current claim payload phase revision left)
  (fn-bpcc-pending-capture controller fuel fn-bp-controller-registry)
  (declare (ignore claim))
  (let* ((intent (fn-bpdi-payload-intent payload))
         (action (fn-bpck-control-action payload))
         (original-plan (fn-bpn-nth 1 action)))
   (cond
    ((not (eq word :checkpoint-current)) (mv word left fn-bp-controller-registry))
    ((not (and (natp left) (<= left fuel) (natp revision)
               (eq phase :running)
               (fn-bpck-control-matches-current-p job current payload)
               (fn-bpdi-token-matches-jobp workspace-token controller job)
               (equal (fn-bpdi-token intent) workspace-token)
               (eq (fn-bpdi-phase intent) :promoted)
               (eq (fn-bpn-nth 0 action) :bp-digest-publication)
               (eq (fn-bpn-nth 2 action) :promoting)
               (fn-bpd-install-readout-planp original-plan)
               (equal (fn-bpn-nth 1 original-plan) workspace-token)
               (equal (fn-bpdi-source intent) (fn-bpn-nth 4 original-plan))
               (natp (fn-bpn-nth 4 action))
               (equal (fn-bpn-nth 4 action) (1+ revision))))
     (mv :stale-publication left fn-bp-controller-registry))
    ((zp left) (mv :yield left fn-bp-controller-registry))
    (t
     (let ((address (caddr controller)) (final-revision (1+ revision)))
      (stobj-let ((fn-bpc-node (fn-bpcr-root fn-bp-controller-registry)))
       (result remaining fn-bpc-node)
       (if (not (fn-bpcn-children-boundp 'fn-bpd-workspace-node fn-bpc-node))
        (mv :workspace-unavailable (1- left) fn-bpc-node)
        (stobj-let ((fn-bpd-workspace-node
          (fn-bpcn-children-get 'fn-bpd-workspace-node fn-bpc-node
                               (create-fn-bpd-workspace-node))))
         (result remaining fn-bpd-workspace-node)
         (fn-bpd-node-publish original-plan final-revision address left fn-bpd-workspace-node)
         (mv result remaining fn-bpc-node)))
       (mv result remaining fn-bp-controller-registry))))))))

; Strong installed readout for the eventual actual consumer. The historical
; controller/job-only storage reader is not an installed workspace capability.
(defun fn-bpd-carry-installed-readout
 (controller job workspace-token source revision fn-bpd-workspace-carry)
 (declare (xargs :stobjs fn-bpd-workspace-carry :guard t))
 (cond
  ((not (and (fn-bpdi-token-matches-jobp workspace-token controller job)
             (equal (fn-bpd-controller fn-bpd-workspace-carry) controller)
             (equal (fn-bpd-job fn-bpd-workspace-carry) job)
             (equal (fn-bpd-nonce fn-bpd-workspace-carry) (fn-bpn-nth 1 workspace-token))
             (natp revision) (equal revision (fn-bpd-revision fn-bpd-workspace-carry))
             (eq (fn-bpn-nth 0 source) :bp-checkpoint-stage)
             (equal (fn-bpn-nth 1 source) job)
             (equal (fn-bpn-nth 0 source) (fn-bpn-nth 0 (fn-bpd-source fn-bpd-workspace-carry)))
             (equal (fn-bpn-nth 1 source) (fn-bpn-nth 1 (fn-bpd-source fn-bpd-workspace-carry)))
             (equal (fn-bpn-nth 2 source) (fn-bpn-nth 2 (fn-bpd-source fn-bpd-workspace-carry)))))
   :stale-workspace)
  ((eq (fn-bpd-phase fn-bpd-workspace-carry) :installed) :installed-storage-ready)
  (t :workspace-unpublished)))
(defun fn-bpd-node-installed-readout (controller job workspace-token source revision address fuel fn-bpd-workspace-node)
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
     (fn-bpd-carry-installed-readout controller job workspace-token source revision fn-bpd-workspace-carry)
     (mv word (1- fuel)))))
  ((equal (mod address 2) 0)
   (if (not (fn-bpd-children-boundp 'fn-bpd-workspace-left fn-bpd-workspace-node))
    (mv :workspace-unavailable (1- fuel))
    (stobj-let ((fn-bpd-workspace-left
      (fn-bpd-children-get 'fn-bpd-workspace-left fn-bpd-workspace-node
                          (create-fn-bpd-workspace-left))))
     (word left)
     (fn-bpd-node-installed-readout controller job workspace-token source revision (floor address 2) (1- fuel) fn-bpd-workspace-left)
     (mv word left))))
  (t
   (if (not (fn-bpd-children-boundp 'fn-bpd-workspace-right fn-bpd-workspace-node))
    (mv :workspace-unavailable (1- fuel))
    (stobj-let ((fn-bpd-workspace-right
      (fn-bpd-children-get 'fn-bpd-workspace-right fn-bpd-workspace-node
                          (create-fn-bpd-workspace-right))))
     (word left)
     (fn-bpd-node-installed-readout controller job workspace-token source revision (floor address 2) (1- fuel) fn-bpd-workspace-right)
     (mv word left))))))


(defun fn-bpd-registered-installed-readout
 (controller workspace-token fuel fn-bp-controller-registry)
 (declare (xargs :stobjs fn-bp-controller-registry :guard (natp fuel)
  :guard-hints (("Goal" :in-theory
   (disable fn-bpcc-pending-capture fn-bpd-node-installed-readout
            fn-bpck-control-matches-current-p)))))
 (mv-let (word job current claim payload phase revision left)
  (fn-bpcc-pending-capture controller fuel fn-bp-controller-registry)
  (declare (ignore claim))
  (let* ((intent (fn-bpdi-payload-intent payload))
         (source (fn-bpdi-source intent)))
   (cond
    ((not (eq word :checkpoint-current)) (mv word left fn-bp-controller-registry))
    ((not (and (natp left) (<= left fuel) (natp revision)
               (eq phase :running)
               (fn-bpck-control-matches-current-p job current payload)
               (fn-bpdi-token-matches-jobp workspace-token controller job)
               (equal (fn-bpdi-token intent) workspace-token)))
     (mv :stale-workspace left fn-bp-controller-registry))
    ((not (eq (fn-bpdi-phase intent) :installed))
     (mv :workspace-unpublished left fn-bp-controller-registry))
    ((not (and (eq (fn-bpn-nth 0 source) :bp-checkpoint-stage)
               (equal (fn-bpn-nth 1 source) job)
               (equal (fn-bpn-nth 2 source) (fn-bpn-nth 3 (fn-bpck-control-job payload)))))
     (mv :stale-workspace left fn-bp-controller-registry))
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
         (fn-bpd-node-installed-readout controller job workspace-token source revision
                                        address left fn-bpd-workspace-node)
         (mv result remaining)))
       (mv result remaining fn-bp-controller-registry))))))))
