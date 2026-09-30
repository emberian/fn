; A-COLD-RUNTIME. Selected SBCL startup peak before collector coexistence.
; Source inventory and falsification measurements are in the resource-pool
; evidence directory. The local witness proves consistency, not qualification.
(in-package "ACL2")
(include-book "cold-runtime-bound")
(encapsulate
 (((fn-assume-cold-runtime-startup-octets * *) => *))
 (local (defun fn-assume-cold-runtime-startup-octets (workers runtime)
          (declare (ignore workers runtime)) 0))
 (defthm fn-assume-cold-runtime-startup-is-natural
   (natp (fn-assume-cold-runtime-startup-octets workers runtime))
   :rule-classes :type-prescription)
 (defthm fn-assume-cold-runtime-startup-within-selected-bound
   (implies (fn-crt-selectedp runtime)
            (<= (fn-assume-cold-runtime-startup-octets workers runtime)
                (fn-crt-executor-octets workers runtime)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-crt-executor-octets)))))
