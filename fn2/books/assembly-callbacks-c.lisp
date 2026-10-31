; Materialize layer C's core operations after the core instance and before
; layer D's machines, which call them: the identity decisions and the
; private successor (assembly-callbacks-c-prepare, -commit), then the group
; directory (S-GROUP) and the sealer (C1c).
(in-package "ACL2")
(include-book "assembly-callbacks-c-commit")
(include-book "machines-c-sealer-events")
(fn2-groups-core-events)
(fn2-sealer-core-events)
(fn2-read-core-events)
