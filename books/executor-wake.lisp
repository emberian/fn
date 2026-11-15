; Earliest required host wake for the current observed clock view. Layer A
; has no machine timer heap: callers explicitly register the next requirement.
(in-package "ACL2")
(include-book "executor-access")
(include-book "executor-wake-events")

(fn2-executor-wake-events)
