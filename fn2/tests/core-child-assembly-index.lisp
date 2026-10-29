; Complete both registries before consuming the machine index and directory.
(in-package "ACL2")
(include-book "../books/machines-all")
(include-book "core-child-registration")
(include-book "../books/machine-dispatch")
(include-book "../books/reference-state")

(fn2-machine-index-events)
(in-theory (disable fn2-machine-local-id))
(fn2-machine-directory-events)
