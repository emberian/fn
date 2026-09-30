; Actual registered prefix action/observation composition. Internal only;
; selected stage/runtime admission and native callback installation are OPEN.
(in-package "ACL2")
(include-book "bp-controller-checkpoint-capture")
(include-book "bp-checkpoint-prefix-io-control")
(set-verify-guards-eagerness 2)

(defun fn-bpck-registered-prefix-next
 (controller expected-revision fuel fn-bp-controller-registry)
 (declare (xargs :stobjs fn-bp-controller-registry :guard (natp fuel)
  :guard-hints (("Goal"
    :use ((:instance fn-bpcc-pending-capture-keeps-fuel-domain))
    :in-theory (disable fn-bpcc-pending-capture fn-bpcc-node-pending-capture
                       fn-bpcc-directory-payload fn-bpcc-node-payload
                       fn-bpck-prefix-prepare)))))
 (if (< fuel (* 2 (1+ (fn-bpcr-depth fn-bp-controller-registry))))
  (mv :yield nil fuel fn-bp-controller-registry)
  (mv-let (word token current claim payload phase revision left)
   (fn-bpcc-pending-capture controller fuel fn-bp-controller-registry)
   (declare (ignore claim))
   (cond
    ((not (eq word :checkpoint-current)) (mv word nil left fn-bp-controller-registry))
    ((not (and (natp revision) (natp expected-revision) (equal revision expected-revision)
               (member-eq phase '(:reserved :running))
               (fn-bpck-control-matches-current-p token current payload)))
     (mv :stale-checkpoint nil left fn-bp-controller-registry))
    (t
     (let* ((prepared (fn-bpck-prefix-prepare payload revision))
            (decision (fn-bpn-nth 0 prepared)))
      (if (not (member-eq decision '(:action-prepared :prefix-frozen)))
       (mv decision nil left fn-bp-controller-registry)
       (mv-let (updated ignored-current ignored-claim next-payload ignored-phase
                 next-revision remaining fn-bp-controller-registry)
        (fn-bpcc-directory-payload controller token :replace revision phase :running
                                  (fn-bpn-nth 1 prepared) left fn-bp-controller-registry)
        (declare (ignore ignored-current ignored-claim ignored-phase))
        (if (and (eq updated :checkpoint-updated) (equal next-revision (1+ revision)))
         (mv decision (fn-bpck-control-action next-payload) remaining fn-bp-controller-registry)
         (mv updated nil remaining fn-bp-controller-registry))))))))))

(defun fn-bpck-registered-prefix-observe
 (controller incoming-token expected-revision observation fuel fn-bp-controller-registry)
 (declare (xargs :stobjs fn-bp-controller-registry :guard (natp fuel)
  :guard-hints (("Goal"
    :use ((:instance fn-bpcc-pending-capture-keeps-fuel-domain))
    :in-theory (disable fn-bpcc-pending-capture fn-bpcc-node-pending-capture
                       fn-bpcc-directory-payload fn-bpcc-node-payload
                       fn-bpck-prefix-observe)))))
 (if (< fuel (* 2 (1+ (fn-bpcr-depth fn-bp-controller-registry))))
  (mv :yield fuel fn-bp-controller-registry)
  (mv-let (word token current claim payload phase revision left)
   (fn-bpcc-pending-capture controller fuel fn-bp-controller-registry)
   (declare (ignore claim))
   (cond
    ((not (eq word :checkpoint-current)) (mv word left fn-bp-controller-registry))
    ((not (and (fn-bpcc-job-tokenp incoming-token) (equal incoming-token token)
               (natp revision) (natp expected-revision) (equal revision expected-revision)
               (member-eq phase '(:reserved :running))
               (fn-bpck-control-matches-current-p token current payload)))
     (mv :stale-checkpoint-observation left fn-bp-controller-registry))
    (t
     (let* ((observed (fn-bpck-prefix-observe payload token revision observation))
            (decision (fn-bpn-nth 0 observed)))
      (if (eq decision :stale-checkpoint-observation)
       (mv decision left fn-bp-controller-registry)
       (mv-let (updated ignored-current ignored-claim ignored-payload ignored-phase
                ignored-revision remaining fn-bp-controller-registry)
        (fn-bpcc-directory-payload controller token :replace revision phase :running
                                  (fn-bpn-nth 1 observed) left fn-bp-controller-registry)
        (declare (ignore ignored-current ignored-claim ignored-payload ignored-phase ignored-revision))
        (mv (if (eq updated :checkpoint-updated) decision updated)
            remaining fn-bp-controller-registry)))))))))
