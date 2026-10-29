; M3: a completion is harvested but its observation is not routed.
; Original: fn2/books/executor.lisp:24 at 137695dfc.
; Sole semantic edit: replace FN2-MACHINE-OBSERVE call with no-wake identity.
(in-package "ACL2")
; Test-only redefinition in a fresh process. Never include/certify this file.
; REDEF! updates both ACL2 executable counterpart and raw function.
(redef!)
(defun fn2-exec-harvest (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :guard (fn2-core-wfp fn2-core)))
  (b* (((mv & ?kind ?id ?gen principal) (fn2-core-next-owner fn2-core))
       (start (fn2-exec-queued fn2-core))
       ((mv delivered & & & ?event ?outcome ?reason ?count ?aux0 ?aux1 fn2-core)
        (fn2-harvest-one fn2-core))
       ((unless delivered) (mv 1 0 0 0 24 fn2-core))
       ((mv wake fn2-core)
        (mv 4294967295 fn2-core))
       (fn2-core (fn2-exec-wake wake fn2-core))
       (fn2-core (fn2-exec-record 0 wake principal 0 0 24 0 nil 4294967295 start fn2-core)))
    (mv 1 0 0 0 24 fn2-core)))
