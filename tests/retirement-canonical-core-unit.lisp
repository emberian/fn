; Canonical actual controls: one served R2 core world and its C attachments.
; The shared events are identical to the historical partial-core controls.
; Persisted-state premises and settlements remain explicit logical fixtures,
; not physical IO/ACK acceptance witnesses.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "retirement-publish-core-unit")
(include-book "retirement-intent-core-controls")
(include-book "retirement-generic-controls")
(include-book "retirement-dispatch-controls")

; The publish entry already materializes the same declaration-owned extent,
; retirement-control and edge projections used by the dispatcher controls.
; No partial core instance or alternate machine/run implementation is included.
(fn2-retirement-intent-core-controls-events)
(fn2-retirement-generic-controls-events)
(fn2-retirement-dispatch-controls-events)
