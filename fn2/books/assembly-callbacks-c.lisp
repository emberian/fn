; Materialize layer C's core operations (identity decisions, C-S1; the
; batch's private successor, C-S3) after the core instance and before layer
; D's machines, which call them.
(in-package "ACL2")
(include-book "assembly-callbacks-a")
(fn2-identity-core-events)
(fn2-successor-core-events)
(fn2-groups-core-events)
