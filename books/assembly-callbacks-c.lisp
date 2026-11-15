; Materialize layer C's core operations after the core instance and before
; layer D's machines, which call them: the private successor
; (assembly-callbacks-c-prepare, -commit), then the group directory
; (S-GROUP), the identity decision (C-S1, §4a) and the sealer (C1c).
(in-package "ACL2")
(include-book "assembly-callbacks-c-commit")
(include-book "machines-c-sealer-events")
(include-book "startup-genesis")
(fn2-groups-core-events)
(fn2-identity-core-events)
(fn2-sealer-core-events)
(fn2-read-core-events)
(fn2-startup-name-events)

; Same generated owners declared before index consumption; no alternate core
; writer implementation. The maintenance admission gate remains disabled.
(fn2-checkpoint-page-worker-events)
(fn2-checkpoint-writer-events)
(fn2-event-producer-rearm-events)
(fn2-checkpoint-summary-authority-live-events)
(fn2-checkpoint-live-adoption-rearm-events)
(fn2-checkpoint-master-events)
