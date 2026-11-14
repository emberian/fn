; The actual transaction callback interface, compiled through child arms.
; Alternative qualification root: do not include together with d-txn.
(in-package "ACL2")
(include-book "assembly-callbacks-e-cns")
(include-book "txn")
(include-book "authority")
(fn2-txn-op-events)
(fn2-authority-allows-events)
(assert-event (equal *fn2-auth-depend-slot* *fn2-txn-slot-depend*))
(fn2-txn-child-events)
