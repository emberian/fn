; Definite close observation retains uncertain stage/debt. No release or
; publication occurs here; cancelled jobs remain cancelled throughout.
(in-package "ACL2")
(include-book "bp-checkpoint-prefix-registered")
(set-verify-guards-eagerness 2)
(defun fn-bpck-close-prepare (payload revision)
 (declare (xargs :guard (natp revision)))
 (let ((job (fn-bpck-control-job payload)))
  (cond ((fn-bpck-control-action payload) (list :busy payload nil))
        ((not (eq (fn-bpn-nth 0 (fn-bpck-control-io payload)) :close))
         (list :close-not-required payload nil))
        (t (let ((action (list :bp-checkpoint-io-action (fn-bpn-nth 1 job)
                               (1+ revision) :close (fn-bpn-nth 10 job) nil)))
            (list :action-prepared
             (fn-bpck-control-make job (fn-bpck-control-io payload)
                                  (fn-bpck-control-digest payload) action) action))))))
(defun fn-bpck-close-observe (payload token revision observation)
 (declare (xargs :guard t))
 (let ((action (fn-bpck-control-action payload)))
  (if (not (and (equal (fn-bpn-nth 0 action) :bp-checkpoint-io-action)
                (fn-bpcc-job-tokenp token)
                (equal token (fn-bpn-nth 1 action))
                (equal token (fn-bpn-nth 1 (fn-bpck-control-job payload)))
                (natp revision) (equal revision (fn-bpn-nth 2 action))
                (eq (fn-bpn-nth 3 action) :close)))
   (list :stale-checkpoint-observation payload)
   (list (if (eq observation :ok) :close-observed :close-uncertain)
    (fn-bpck-control-make (fn-bpck-control-job payload)
     (fn-bpck-io-step (fn-bpck-control-io payload)
                     (if (eq observation :ok) :ok :error))
     (fn-bpck-control-digest payload) nil)))))
(defun fn-owner-bp-checkpoint-close-next
 (controller fuel fn-bp-controller-registry)
 (declare (xargs :stobjs fn-bp-controller-registry :guard (natp fuel)
  :guard-hints (("Goal"
    :use ((:instance fn-bpcc-pending-capture-keeps-fuel-domain))
    :in-theory (disable fn-bpcc-pending-capture fn-bpcc-node-pending-capture
                       fn-bpcc-directory-payload fn-bpcc-node-payload
                       fn-bpck-close-prepare)))))
 (if (< fuel (* 2 (1+ (fn-bpcr-depth fn-bp-controller-registry))))
  (mv :yield nil fuel fn-bp-controller-registry)
  (mv-let (word token current claim payload phase revision left)
   (fn-bpcc-pending-capture controller fuel fn-bp-controller-registry)
   (declare (ignore claim))
   (cond
    ((not (eq word :checkpoint-current)) (mv word nil left fn-bp-controller-registry))
    ((not (and (natp revision)
               (member-eq phase '(:reserved :running :cancelled))
               (fn-bpck-control-matches-current-p token current payload)))
     (mv :stale-checkpoint nil left fn-bp-controller-registry))
    (t
     (let* ((prepared (fn-bpck-close-prepare payload revision))
            (decision (fn-bpn-nth 0 prepared)))
      (if (not (member-eq decision '(:action-prepared)))
       (mv decision nil left fn-bp-controller-registry)
       (mv-let (updated ignored-current ignored-claim next-payload ignored-phase
                 next-revision remaining fn-bp-controller-registry)
        (fn-bpcc-directory-payload controller token :replace revision phase phase
                                  (fn-bpn-nth 1 prepared) left fn-bp-controller-registry)
        (declare (ignore ignored-current ignored-claim ignored-phase))
        (if (and (eq updated :checkpoint-updated) (equal next-revision (1+ revision)))
         (mv decision (fn-bpck-control-action next-payload) remaining fn-bp-controller-registry)
         (mv updated nil remaining fn-bp-controller-registry))))))))))

(defun fn-owner-bp-checkpoint-close-observe
 (controller incoming-token expected-revision observation fuel fn-bp-controller-registry)
 (declare (xargs :stobjs fn-bp-controller-registry :guard (natp fuel)
  :guard-hints (("Goal"
    :use ((:instance fn-bpcc-pending-capture-keeps-fuel-domain))
    :in-theory (disable fn-bpcc-pending-capture fn-bpcc-node-pending-capture
                       fn-bpcc-directory-payload fn-bpcc-node-payload
                       fn-bpck-close-observe)))))
 (if (< fuel (* 2 (1+ (fn-bpcr-depth fn-bp-controller-registry))))
  (mv :yield fuel fn-bp-controller-registry)
  (mv-let (word token current claim payload phase revision left)
   (fn-bpcc-pending-capture controller fuel fn-bp-controller-registry)
   (declare (ignore claim))
   (cond
    ((not (eq word :checkpoint-current)) (mv word left fn-bp-controller-registry))
    ((not (and (fn-bpcc-job-tokenp incoming-token) (equal incoming-token token)
               (natp revision) (natp expected-revision) (equal revision expected-revision)
               (member-eq phase '(:reserved :running :cancelled))
               (fn-bpck-control-matches-current-p token current payload)))
     (mv :stale-checkpoint-observation left fn-bp-controller-registry))
    (t
     (let* ((observed (fn-bpck-close-observe payload token revision observation))
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
