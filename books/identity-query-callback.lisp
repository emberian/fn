; Materialize the actual identity callback from its sole production generator.
; This section needs no successor prepare/commit or later machine callbacks.
; Consumers of assembly-callbacks-c receive these same generated definitions.
(in-package "ACL2")
(include-book "query-ref-wake")
(include-book "machines-c-groups")
(fn2-identity-core-events)
