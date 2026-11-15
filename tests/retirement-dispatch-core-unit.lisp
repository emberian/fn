; Actual persisted lifecycle dispatcher controls over the bounded B instance.
; Publish phase, installed batch and successful IO flags below are explicit
; logical persisted-state fixture premises, not execution of physical IO.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "retirement-core-instance")
(include-book "../sim/commit-test-profile")

; The existing declaration-owned reference generator includes every field,
; row count and scalar extra field; no hand-written snapshot model.
(include-book "retirement-state-projections")
(make-event
 (cons 'progn (fn2-riud-projection-events
               '(fn2-extents fn2-retirement-control fn2-alloc-edges) (w state))))
(include-book "retirement-dispatch-controls")
(fn2-retirement-dispatch-controls-events)
