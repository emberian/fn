; Actual allocator/coordinator entry controls. No independent retirement model.
; Source prepared only: physical writer/fence execution remains a separate gate.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "retirement-intent-leaf-unit")
(include-book "../sim/commit-proof-step")



(include-book "retirement-intent-core-controls")
(fn2-retirement-intent-core-controls-events)
