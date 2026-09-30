; BP-private registered digest workspace representation. No constructor grant
; is inferred from these declarations. SAME-pool install must precede factories.
; Reads check BOUNDP first and never create a missing child. Actual controller
; physical-slot traversal is token-only in the eventual registered parent.
(in-package "ACL2")
(include-book "bp-controller-registry")
(include-book "bp-controller-checkpoint-current")
(include-book "bp-controller-checkpoint-payload-directory")
(include-book "pagestore-digest-byte-cursor")
(set-verify-guards-eagerness 2)

; Fixed carry retains no native pointer or full CURRENT snapshot. Source is
; the issued immutable stage/file incarnation, not its reusable pathname.
(defstobj fn-bpd-workspace-carry
 (fn-bpd-controller :initially nil)
 (fn-bpd-job :initially nil)
 (fn-bpd-nonce :type (integer 0 *) :initially 0)
 (fn-bpd-source :initially nil)
 (fn-bpd-phase :initially :uninstalled)
 (fn-bpd-revision :type (integer 0 *) :initially 0)
 :inline t)
(defstobj fn-bpd-workspace-node
 (fn-bpd-children :type (stobj-table 16))
 :inline t)
(defstobj fn-bpd-workspace-left
 (fn-bpdl-children :type (stobj-table 16))
 :congruent-to fn-bpd-workspace-node :inline t)
(defstobj fn-bpd-workspace-right
 (fn-bpdr-children :type (stobj-table 16))
 :congruent-to fn-bpd-workspace-node :inline t)

; Internal bounded fixed-field fence, not installed authority. No stage bytes,
; digest frames, graph predicate or native pointer is traversed here.
(defun fn-bpd-carry-status (controller job expected-revision fn-bpd-workspace-carry)
 (declare (xargs :stobjs fn-bpd-workspace-carry :guard t))
 (cond ((eq (fn-bpd-phase fn-bpd-workspace-carry) :uninstalled)
        :bp-runtime-unavailable)
       ((not (and (fn-bpc-tokenp controller) (fn-bpcc-job-tokenp job)
                  (equal (caddr job) controller)
                  (equal controller (fn-bpd-controller fn-bpd-workspace-carry))
                  (equal job (fn-bpd-job fn-bpd-workspace-carry))))
        :stale-workspace)
       ((not (and (natp expected-revision)
                  (equal expected-revision (fn-bpd-revision fn-bpd-workspace-carry))))
        :stale-workspace-revision)
       ((eq (fn-bpd-phase fn-bpd-workspace-carry) :fenced) :workspace-fenced)
       (t :workspace-current)))

(local (defthm fn-bpd-address-next-natural
 (implies (natp address) (natp (floor address 2)))
 :hints (("Goal" :in-theory (disable floor)))))

; Variable-depth address traversal is independent of controller-directory
; growth. Address0 owns this node's workspace; children own positive suffixes.
; No absent-path GET is evaluated, and no constructor is called by a read.
(defun fn-bpd-node-read (controller job expected-revision address fuel fn-bpd-workspace-node)
 (declare (xargs :stobjs fn-bpd-workspace-node :measure (nfix fuel)
  :guard (and (natp address) (natp fuel))
  :guard-hints (("Goal" :in-theory (disable floor mod)))))
 (cond
  ((zp fuel) (mv :yield nil fuel))
  ((zp address)
   (if (not (and (fn-bpd-children-boundp 'pgs-digest-state fn-bpd-workspace-node)
                 (fn-bpd-children-boundp 'fn-bpd-workspace-carry fn-bpd-workspace-node)))
    (mv :workspace-unavailable nil (1- fuel))
    (stobj-let ((fn-bpd-workspace-carry
      (fn-bpd-children-get 'fn-bpd-workspace-carry fn-bpd-workspace-node
                          (create-fn-bpd-workspace-carry))))
     (status revision)
     (mv (fn-bpd-carry-status controller job expected-revision fn-bpd-workspace-carry)
         (fn-bpd-revision fn-bpd-workspace-carry))
     (mv status revision (1- fuel)))))
  ((equal (mod address 2) 0)
   (if (not (fn-bpd-children-boundp 'fn-bpd-workspace-left fn-bpd-workspace-node))
    (mv :workspace-unavailable nil (1- fuel))
    (stobj-let ((fn-bpd-workspace-left
      (fn-bpd-children-get 'fn-bpd-workspace-left fn-bpd-workspace-node
                          (create-fn-bpd-workspace-left))))
     (status revision left)
     (fn-bpd-node-read controller job expected-revision (floor address 2)
                       (1- fuel) fn-bpd-workspace-left)
     (mv status revision left))))
  (t
   (if (not (fn-bpd-children-boundp 'fn-bpd-workspace-right fn-bpd-workspace-node))
    (mv :workspace-unavailable nil (1- fuel))
    (stobj-let ((fn-bpd-workspace-right
      (fn-bpd-children-get 'fn-bpd-workspace-right fn-bpd-workspace-node
                          (create-fn-bpd-workspace-right))))
     (status revision left)
     (fn-bpd-node-read controller job expected-revision (floor address 2)
                       (1- fuel) fn-bpd-workspace-right)
     (mv status revision left))))))

(local (defthm fn-bpd-node-payload-fuel-natural
 (implies (and (natp physical-segment) (natp depth) (natp fuel))
  (natp (mv-nth 6 (fn-bpcc-node-payload controller token operation slot
   physical-segment depth expected-revision expected-phase next-phase next-payload
   fuel fn-bpc-node))))
 :hints (("Goal"
  :induct (fn-bpcc-node-payload controller token operation slot physical-segment
   depth expected-revision expected-phase next-phase next-payload fuel fn-bpc-node)
  :in-theory (e/d (fn-bpcc-node-payload)
   (floor mod fn-bpcn-children-get fn-bpcn-children-boundp create-fn-bpc-left
    create-fn-bpc-right create-fn-bpc-segment fn-bpcc-segment-payload-action))))))
(local (defthm fn-bpd-directory-payload-fuel-natural
 (implies (and (fn-bp-controller-registryp fn-bp-controller-registry) (natp fuel))
  (natp (mv-nth 6 (fn-bpcc-directory-payload controller token operation
   expected-revision expected-phase next-phase next-payload fuel fn-bp-controller-registry))))
 :hints (("Goal" :in-theory (e/d (fn-bpcc-directory-payload)
                                 (fn-bpcc-node-payload))))))

; Token-only internal query. Verify the actual registered current job before
; selecting the independent workspace address. No CURRENT or child escapes.
(defun fn-bpd-registered-workspace-read
 (controller job expected-revision fuel fn-bp-controller-registry)
 (declare (xargs :stobjs fn-bp-controller-registry :guard (natp fuel)
  :guard-hints (("Goal" :in-theory (disable fn-bpcc-directory-payload
                                           fn-bpcc-node-payload)))))
 (mv-let (word current claim payload phase revision left fn-bp-controller-registry)
  (fn-bpcc-directory-payload controller job :read nil nil nil nil fuel
                            fn-bp-controller-registry)
  (declare (ignore current claim payload))
  (cond
   ((not (equal word :checkpoint-current))
    (mv word nil left fn-bp-controller-registry))
   ((not (and (fn-bpc-tokenp controller) (fn-bpcc-job-tokenp job)
              (equal (caddr job) controller)
              (member-eq phase '(:reserved :running))
              (natp expected-revision) (equal expected-revision revision)))
    (mv :stale-workspace nil left fn-bp-controller-registry))
   (t
    (stobj-let ((fn-bpc-node (fn-bpcr-root fn-bp-controller-registry)))
     (status workspace-revision remaining)
     (if (not (fn-bpcn-children-boundp 'fn-bpd-workspace-node fn-bpc-node))
      (mv :workspace-unavailable nil left)
      (stobj-let ((fn-bpd-workspace-node
        (fn-bpcn-children-get 'fn-bpd-workspace-node fn-bpc-node
                             (create-fn-bpd-workspace-node))))
       (status workspace-revision remaining)
       (fn-bpd-node-read controller job expected-revision (caddr controller)
                         left fn-bpd-workspace-node)
       (mv status workspace-revision remaining)))
     (mv status workspace-revision remaining fn-bp-controller-registry))))))
