; The native holder retains only the immutable per-job identity issued by
; the genuine holder allocator. Core derives the live job and compares it
; before preparing an effect; an old holder cannot target a replacement job.
(in-package "ACL2")
(include-book "bp-checkpoint-prefix-registered-driver")
(include-book "bp-checkpoint-close-registered")
(set-verify-guards-eagerness 2)
(defun fn-owner-bp-checkpoint-prefix-next-for-job
 (controller expected-job fuel fn-bp-controller-registry)
 (declare (xargs :stobjs fn-bp-controller-registry :guard (natp fuel)
  :guard-hints (("Goal"
    :use ((:instance fn-bpcc-pending-capture-keeps-fuel-domain))
    :in-theory (disable fn-bpcc-pending-capture fn-bpcc-node-pending-capture
                       fn-bpck-registered-prefix-next)))))
 (if (< fuel (* 3 (1+ (fn-bpcr-depth fn-bp-controller-registry))))
  (mv :yield nil fuel fn-bp-controller-registry)
  (mv-let (word token current claim payload phase revision left)
   (fn-bpcc-pending-capture controller fuel fn-bp-controller-registry)
   (declare (ignore current claim payload phase))
   (cond ((not (eq word :checkpoint-current))
           (mv word nil left fn-bp-controller-registry))
          ((not (and (fn-bpcc-job-tokenp expected-job) (equal expected-job token)))
           (mv :stale-checkpoint-job nil left fn-bp-controller-registry))
          (t (fn-bpck-registered-prefix-next controller revision left fn-bp-controller-registry))))))
(defun fn-owner-bp-checkpoint-close-next-for-job
 (controller expected-job fuel fn-bp-controller-registry)
 (declare (xargs :stobjs fn-bp-controller-registry :guard (natp fuel)
  :guard-hints (("Goal"
    :use ((:instance fn-bpcc-pending-capture-keeps-fuel-domain))
    :in-theory (disable fn-bpcc-pending-capture fn-bpcc-node-pending-capture
                       fn-owner-bp-checkpoint-close-next)))))
 (if (< fuel (* 3 (1+ (fn-bpcr-depth fn-bp-controller-registry))))
  (mv :yield nil fuel fn-bp-controller-registry)
  (mv-let (word token current claim payload phase revision left)
   (fn-bpcc-pending-capture controller fuel fn-bp-controller-registry)
   (declare (ignore current claim payload phase))
   (cond ((not (eq word :checkpoint-current))
           (mv word nil left fn-bp-controller-registry))
          ((not (and (fn-bpcc-job-tokenp expected-job) (equal expected-job token)))
           (mv :stale-checkpoint-job nil left fn-bp-controller-registry))
          (t (fn-owner-bp-checkpoint-close-next controller left fn-bp-controller-registry))))))
