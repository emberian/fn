; Join the result of an already issued primitive after cancellation. This
; cannot issue another primitive, restore running, or release any resource.
(in-package "ACL2")
(include-book "bp-checkpoint-prefix-registered")
(set-verify-guards-eagerness 2)
(defun fn-bpck-cancelled-observe (payload token revision observation)
 (declare (xargs :guard t))
 (let* ((answer (fn-bpck-prefix-observe payload token revision observation))
        (word (fn-bpn-nth 0 answer)) (next (fn-bpn-nth 1 answer))
        (io (fn-bpck-control-io next)))
  (if (eq word :stale-checkpoint-observation) answer
   (list (if (eq word :observed) :cancelled-observed :cancelled-uncertain)
    (fn-bpck-control-make (fn-bpck-control-job next)
     (if (eq (fn-bpn-nth 0 io) :close) io (fn-bpck-io-step io :cancel))
     (fn-bpck-control-digest next) nil)))))
(defun fn-owner-bp-checkpoint-cancelled-observe
 (controller incoming-token expected-revision observation fuel fn-bp-controller-registry)
 (declare (xargs :stobjs fn-bp-controller-registry :guard (natp fuel)
  :guard-hints (("Goal"
    :use ((:instance fn-bpcc-pending-capture-keeps-fuel-domain))
    :in-theory (disable fn-bpcc-pending-capture fn-bpcc-node-pending-capture
                       fn-bpcc-directory-payload fn-bpcc-node-payload
                       fn-bpck-cancelled-observe)))))
 (if (< fuel (* 2 (1+ (fn-bpcr-depth fn-bp-controller-registry))))
  (mv :yield fuel fn-bp-controller-registry)
  (mv-let (word token current claim payload phase revision left)
   (fn-bpcc-pending-capture controller fuel fn-bp-controller-registry)
   (declare (ignore claim))
   (cond
    ((not (eq word :checkpoint-current)) (mv word left fn-bp-controller-registry))
    ((not (and (fn-bpcc-job-tokenp incoming-token) (equal incoming-token token)
               (natp revision) (natp expected-revision) (equal revision expected-revision)
               (eq phase :cancelled)
               (fn-bpck-control-matches-current-p token current payload)))
     (mv :stale-checkpoint-observation left fn-bp-controller-registry))
    (t
     (let* ((observed (fn-bpck-cancelled-observe payload token revision observation))
            (decision (fn-bpn-nth 0 observed)))
      (if (eq decision :stale-checkpoint-observation)
       (mv decision left fn-bp-controller-registry)
       (mv-let (updated ignored-current ignored-claim ignored-payload ignored-phase
                ignored-revision remaining fn-bp-controller-registry)
        (fn-bpcc-directory-payload controller token :replace revision phase phase
                                  (fn-bpn-nth 1 observed) left fn-bp-controller-registry)
        (declare (ignore ignored-current ignored-claim ignored-payload ignored-phase ignored-revision))
        (mv (if (eq updated :checkpoint-updated) decision updated)
            remaining fn-bp-controller-registry)))))))))
