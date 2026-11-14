; Admission is checked after all machine declarations, so the supported
; profile cannot silently promise a quantum smaller than an actual arm needs.
(in-package "ACL2")
(include-book "assembly-core")
(include-book "executor-reservation-events")

(fn2-executor-reservation-events)
