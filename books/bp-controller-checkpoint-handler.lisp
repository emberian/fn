; Internal semantic continuation over actual registered CURRENT/job custody.
; No native state snapshot, runtime installation or allocation grant here.
(in-package "ACL2")
(include-book "bp-controller-checkpoint-payload-directory")
(include-book "bp-node-checkpoint-job")
(set-verify-guards-eagerness 2)

(defun fn-bpck-control-make (job io-control digest-binding pending-action)
 (declare (xargs :guard t))
 (list :bp-checkpoint-control job io-control digest-binding pending-action))
(defun fn-bpck-control-job (payload)
 (declare (xargs :guard t)) (fn-bpn-nth 1 payload))
(defun fn-bpck-control-io (payload)
 (declare (xargs :guard t)) (fn-bpn-nth 2 payload))
(defun fn-bpck-control-digest (payload)
 (declare (xargs :guard t)) (fn-bpn-nth 3 payload))
(defun fn-bpck-control-action (payload)
 (declare (xargs :guard t)) (fn-bpn-nth 4 payload))

; Fixed field fences only. The resident CK graph is borrowed from the
; registered frozen CURRENT; no whole checkpoint validator is invoked.
(defun fn-bpck-control-matches-current-p (token current payload)
 (declare (xargs :guard t))
 (let ((job (fn-bpck-control-job payload)))
  (and (equal (fn-bpn-nth 0 payload) :bp-checkpoint-control)
       (equal (fn-bpn-nth 0 job) :bp-checkpoint-job)
       (equal (fn-bpn-nth 1 job) token)
       (fn-bpco-checkpoint-operation-p current)
       (equal (fn-bpn-nth 2 job) (fn-bpco-checkpoint-epoch current))
       (equal (fn-bpn-nth 3 job) (fn-bpco-checkpoint-generation current)))))

(local (defthm fn-bpck-node-payload-fuel-natural
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
(local (defthm fn-bpck-directory-payload-fuel-natural
 (implies (and (fn-bp-controller-registryp fn-bp-controller-registry) (natp fuel))
  (natp (mv-nth 6 (fn-bpcc-directory-payload controller token operation
   expected-revision expected-phase next-phase next-payload fuel fn-bp-controller-registry))))
 :hints (("Goal" :in-theory (e/d (fn-bpcc-directory-payload)
                                 (fn-bpcc-node-payload))))))

; Internal source composition only, not a public funded entry. Revision
; refusal precedes census constructors. Persist the exact residual before
; returning; native cannot replace it with a separately supplied job.
(defun fn-bpck-registered-census-turn
 (controller token expected-revision quantum fuel fn-bp-controller-registry)
 (declare (xargs :stobjs fn-bp-controller-registry
                 :guard (and (natp quantum) (natp fuel))
                 :guard-hints (("Goal" :in-theory
                  (disable fn-bpcc-directory-payload fn-bpcc-node-payload
                           fn-bpck-census-step fn-bpck-control-matches-current-p)))))
 (if (< fuel (* 2 (+ 1 (fn-bpcr-depth fn-bp-controller-registry))))
  (mv :yield nil fuel fn-bp-controller-registry)
  (mv-let (word current claim payload phase revision left fn-bp-controller-registry)
  (fn-bpcc-directory-payload controller token :read nil nil nil nil fuel
                            fn-bp-controller-registry)
  (declare (ignore claim))
  (cond
   ((not (equal word :checkpoint-current))
    (mv word nil left fn-bp-controller-registry))
   ((not (and (member-eq phase '(:reserved :running))
              (natp revision) (natp expected-revision)
              (equal expected-revision revision)
              (fn-bpck-control-matches-current-p token current payload)
              (null (fn-bpck-control-action payload))
              (equal (fn-bpn-nth 6 (fn-bpck-control-job payload)) :census)))
    (mv :stale-checkpoint nil left fn-bp-controller-registry))
   (t
    (let* ((job (fn-bpck-census-step (fn-bpck-control-job payload) quantum))
           (next (fn-bpck-control-make job (fn-bpck-control-io payload)
                   (fn-bpck-control-digest payload) nil)))
     (mv-let (updated after-current after-claim after-payload after-phase
              after-revision remaining fn-bp-controller-registry)
      (fn-bpcc-directory-payload controller token :replace revision phase :running
                                next left fn-bp-controller-registry)
      (declare (ignore after-current after-claim after-phase))
      (if (equal updated :checkpoint-updated)
       (mv updated (list after-revision
                          (fn-bpn-nth 6 (fn-bpck-control-job after-payload)))
           remaining fn-bp-controller-registry)
       (mv updated nil remaining fn-bp-controller-registry)))))))))

; No installed canonical constructor/profile receipt exists yet. The public
; entry refuses before looking up a row or allocating any semantic job.
(defun fn-owner-bp-checkpoint-turn
 (controller token expected-revision operation quantum fuel fn-bp-controller-registry)
 (declare (xargs :stobjs fn-bp-controller-registry :guard (natp fuel)))
 (declare (ignore controller token expected-revision operation quantum))
 (mv :bp-runtime-unavailable nil fuel fn-bp-controller-registry))
