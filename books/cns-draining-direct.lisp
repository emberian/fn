; Actual held/final direct-arm proofs, before public wrapper transport.
; Remaining proof surface after the explicit component uses: successful
; batched row writes must equal the independent CNS/directory updates.
; Their actual names and intermediate arguments are recorded below; the
; proof opens exactly those writers. No speculative writer twin is added.
(in-package "ACL2")
(include-book "cns-draining-effects")
(include-book "cns-draining-direct-events")
(make-event (value (fn2-cns-draining-proof-event :calls (w state))))
(make-event (value (fn2-cns-draining-proof-event :held (w state))))
(make-event (value (fn2-cns-draining-proof-event :final (w state))))
(make-event (value (fn2-cns-draining-proof-event :direct (w state))))
