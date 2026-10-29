; Layer A uses the same declaration as every other layer.
(in-package "ACL2")
(include-book "core-children")
(include-book "pool")
(include-book "sched")
(include-book "trace")
(include-book "exec-state")
(include-book "machines-directory")
(defcorechild fn2-core-pool fn2-pool
 :init (fn2-pool-init (fn2-profile-pool-classes profile)
         (fn2-profile-generation-start profile) (fn2-profile-generation-limit profile) fn2-pool)
 :profilep (fn2-pool-profilep (fn2-profile-pool-classes profile))
 :order :foundation :why "Pool ownership and byte loans persist across turns.")
(defcorechild fn2-core-ops fn2-ops
 :init (fn2-ops-init profile fn2-ops) :profilep (fn2-profilep profile)
 :order :foundation :why "Outstanding effects and completion cells.")
(defcorechild fn2-core-sched fn2-sched
 :init (fn2-sched-init profile (fn2-machine-index-count profile) fn2-sched) :profilep (fn2-sched-profilep profile)
 :reference :environment :order :foundation
 :why "Reference uses independent list queues/calendar; reference.lisp compares their semantic relation.")
(defcorechild fn2-core-machines fn2-machines
 :init (fn2-machines-init profile fn2-machines) :profilep (fn2-machines-profilep profile)
 :order :foundation :why "Global machine directory and admission state.")
(defcorechild fn2-core-trace fn2-trace
 :init (fn2-trace-init (fn2-profile-trace-capacity profile)
         (fn2-profile-trace profile) fn2-trace)
 :profilep (unsigned-byte-p 32 (fn2-profile-trace-capacity profile))
 :reference :environment :order :foundation
 :why "Diagnostic output is checked by TRACE; it does not drive reference transitions.")
(defcorechild fn2-core-control fn2-control
 :init (fn2-control-init profile fn2-control) :profilep (fn2-profilep profile)
 :order :foundation :why "Execution quanta and durable observation posture.")
