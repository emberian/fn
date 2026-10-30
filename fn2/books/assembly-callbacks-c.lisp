; Materialize layer C's core operations (identity decisions, C-S1) after the
; core instance and before layer D's machines, which call them.
(in-package "ACL2")
(include-book "assembly-callbacks-a")
(fn2-identity-core-events)
