; The sole served core instance. Include registration books in node order.
(in-package "ACL2")
(include-book "machines-all")
(include-book "machine-dispatch")
(include-book "reference-state")
; B/C/D registration books go HERE, before either registry is consumed.

(fn2-machine-index-events)
(in-theory (disable fn2-machine-local-id))
(fn2-machine-directory-events)
(fn2-core-events)
(fn2-machine-access-events)
(fn2-scribe-events)
(fn2-machine-a-events)
; Other layers' continuation event macros go HERE, before final dispatch.
(fn2-machine-dispatch-events)
(fn2-reference-state-events)

(assert-event
 (and (fn2-core-profilep *fn2-profile-concrete*)
      (fn2-core-profilep *fn2-profile-tiny*)
      (fn2-core-profilep *fn2-profile-tiny-near-limit*)))
