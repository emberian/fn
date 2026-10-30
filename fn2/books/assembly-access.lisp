; Materialize machine access through the assembled core.
(in-package "ACL2")
(include-book "assembly-init")
; The ledger's core wrappers first: the access section's grant source
; (fn2-machine-grant-ready-p / -grant-one, D7's S5) and the listener's
; Accept booking (S1) call them.
(fn2-account-events)
(fn2-machine-access-events)
