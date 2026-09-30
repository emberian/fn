; Internal storage factory turn. This is NOT the public constructor gate.
; Its caller must obtain the actual stored :constructing plan and installed
; operation allowance in the same serialized core invocation. No native plan.
(in-package "ACL2")
(include-book "bp-digest-workspace-storage")
(include-book "bp-digest-install-intent")
(set-verify-guards-eagerness 2)

(defun fn-bpd-factory-planp (plan)
 (declare (xargs :guard t))
 (let* ((token (fn-bpn-nth 1 plan)) (controller (fn-bpn-nth 2 plan))
        (job (fn-bpn-nth 3 plan)))
  (and (equal (fn-bpn-nth 0 plan) :bp-digest-install)
       (fn-bpdi-token-matches-jobp token controller job)
       (equal (fn-bpn-nth 5 plan) :constructing)
       (natp (fn-bpn-nth 6 plan)))))

; A freshly created carry starts uninstalled. Publication is a separate
; actual SAME-pool transfer, so neither factory return nor shape installs it.
(defun fn-bpd-factory-initialize-carry (plan fn-bpd-workspace-carry)
 (declare (xargs :stobjs fn-bpd-workspace-carry :guard t))
 (if (not (fn-bpd-factory-planp plan)) fn-bpd-workspace-carry
  (let* ((token (fn-bpn-nth 1 plan))
         (fn-bpd-workspace-carry
           (update-fn-bpd-controller (fn-bpn-nth 2 plan) fn-bpd-workspace-carry))
         (fn-bpd-workspace-carry
           (update-fn-bpd-job (fn-bpn-nth 3 plan) fn-bpd-workspace-carry))
         (fn-bpd-workspace-carry
           (update-fn-bpd-nonce (fn-bpn-nth 1 token) fn-bpd-workspace-carry))
         (fn-bpd-workspace-carry
           (update-fn-bpd-source (fn-bpn-nth 4 plan) fn-bpd-workspace-carry))
         (fn-bpd-workspace-carry
           (update-fn-bpd-phase :constructing fn-bpd-workspace-carry)))
   (update-fn-bpd-revision (fn-bpn-nth 6 plan) fn-bpd-workspace-carry))))

(local (defthm fn-bpd-factory-address-natural
 (implies (natp address) (natp (floor address 2)))
 :hints (("Goal" :in-theory (disable floor)))))

; Traverse existing registered children with fuel. At the first missing child,
; construct that ONE child and return immediately without descending into it.
; Repeated turns retain the installed partial tree; no whole-path creator loop.
(defun fn-bpd-node-install-turn (plan address fuel fn-bpd-workspace-node)
 (declare (xargs :stobjs fn-bpd-workspace-node :measure (nfix fuel)
  :guard (and (natp address) (natp fuel))
  :guard-hints (("Goal" :in-theory (disable floor mod)))))
 (cond
  ((not (fn-bpd-factory-planp plan)) (mv :stale-install fuel fn-bpd-workspace-node))
  ((zp fuel) (mv :yield fuel fn-bpd-workspace-node))
  ((zp address)
   (cond
    ((not (fn-bpd-children-boundp 'pgs-digest-state fn-bpd-workspace-node))
     (stobj-let ((pgs-digest-state
       (fn-bpd-children-get 'pgs-digest-state fn-bpd-workspace-node
                           (create-pgs-digest-state))))
      (word pgs-digest-state)
      (mv :digest-created pgs-digest-state)
      (mv word (1- fuel) fn-bpd-workspace-node)))
    ((not (fn-bpd-children-boundp 'fn-bpd-workspace-carry fn-bpd-workspace-node))
     (stobj-let ((fn-bpd-workspace-carry
       (fn-bpd-children-get 'fn-bpd-workspace-carry fn-bpd-workspace-node
                           (create-fn-bpd-workspace-carry))))
      (word fn-bpd-workspace-carry)
      (let ((fn-bpd-workspace-carry
              (fn-bpd-factory-initialize-carry plan fn-bpd-workspace-carry)))
       (mv :carry-created fn-bpd-workspace-carry))
      (mv word (1- fuel) fn-bpd-workspace-node)))
    (t (mv :storage-present (1- fuel) fn-bpd-workspace-node))))
  ((equal (mod address 2) 0)
   (if (not (fn-bpd-children-boundp 'fn-bpd-workspace-left fn-bpd-workspace-node))
    (stobj-let ((fn-bpd-workspace-left
      (fn-bpd-children-get 'fn-bpd-workspace-left fn-bpd-workspace-node
                          (create-fn-bpd-workspace-left))))
     (word fn-bpd-workspace-left)
     (mv :node-created fn-bpd-workspace-left)
     (mv word (1- fuel) fn-bpd-workspace-node))
    (stobj-let ((fn-bpd-workspace-left
      (fn-bpd-children-get 'fn-bpd-workspace-left fn-bpd-workspace-node
                          (create-fn-bpd-workspace-left))))
     (word left fn-bpd-workspace-left)
     (fn-bpd-node-install-turn plan (floor address 2) (1- fuel) fn-bpd-workspace-left)
     (mv word left fn-bpd-workspace-node))))
  (t
   (if (not (fn-bpd-children-boundp 'fn-bpd-workspace-right fn-bpd-workspace-node))
    (stobj-let ((fn-bpd-workspace-right
      (fn-bpd-children-get 'fn-bpd-workspace-right fn-bpd-workspace-node
                          (create-fn-bpd-workspace-right))))
     (word fn-bpd-workspace-right)
     (mv :node-created fn-bpd-workspace-right)
     (mv word (1- fuel) fn-bpd-workspace-node))
    (stobj-let ((fn-bpd-workspace-right
      (fn-bpd-children-get 'fn-bpd-workspace-right fn-bpd-workspace-node
                          (create-fn-bpd-workspace-right))))
     (word left fn-bpd-workspace-right)
     (fn-bpd-node-install-turn plan (floor address 2) (1- fuel) fn-bpd-workspace-right)
     (mv word left fn-bpd-workspace-node))))))

; Proof support for the registered caller: returned fuel, not heap adequacy.
(defthm fn-bpd-node-install-turn-keeps-fuel-domain
 (implies (natp fuel)
  (and (natp (mv-nth 1 (fn-bpd-node-install-turn plan address fuel fn-bpd-workspace-node)))
       (<= (mv-nth 1 (fn-bpd-node-install-turn plan address fuel fn-bpd-workspace-node)) fuel)))
 :rule-classes nil
 :hints (("Goal"
  :induct (fn-bpd-node-install-turn plan address fuel fn-bpd-workspace-node)
  :in-theory (e/d (fn-bpd-node-install-turn)
   (floor mod fn-bpd-factory-planp fn-bpd-factory-initialize-carry
    fn-bpd-children-get fn-bpd-children-boundp
    create-fn-bpd-workspace-left create-fn-bpd-workspace-right
    create-fn-bpd-workspace-carry create-pgs-digest-state)))))
