; Token-only native-facing source composition. Dormant until the selected
; guarded dispatcher and actual operation/stage allowance are installed.
(in-package "ACL2")
(include-book "bp-checkpoint-prefix-registered")
(set-verify-guards-eagerness 2)

; Native supplies neither CURRENT nor an initial revision snapshot. The whole
; capture/prepare/replace composition runs in one serialized core invocation.
(defun fn-owner-bp-checkpoint-prefix-next
 (controller fuel fn-bp-controller-registry)
 (declare (xargs :stobjs fn-bp-controller-registry :guard (natp fuel)
  :guard-hints (("Goal"
    :use ((:instance fn-bpcc-pending-capture-keeps-fuel-domain))
    :in-theory (disable fn-bpcc-pending-capture fn-bpcc-node-pending-capture
                       fn-bpck-registered-prefix-next)))))
 (if (< fuel (* 3 (1+ (fn-bpcr-depth fn-bp-controller-registry))))
  (mv :yield nil fuel fn-bp-controller-registry)
  (mv-let (word token current claim payload phase revision left)
   (fn-bpcc-pending-capture controller fuel fn-bp-controller-registry)
   (declare (ignore token current claim payload phase))
   (if (not (eq word :checkpoint-current))
    (mv word nil left fn-bp-controller-registry)
    (fn-bpck-registered-prefix-next controller revision left fn-bp-controller-registry)))))
