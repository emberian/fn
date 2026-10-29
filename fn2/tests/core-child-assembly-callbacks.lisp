; Admit every machine's callbacks before generating final dispatch.
(in-package "ACL2")
(include-book "core-child-assembly-access")

(fn2-scribe-events)
(fn2-machine-a-events)
(fn2-test-machine-events)

(fn2-resolve :callbacks)
