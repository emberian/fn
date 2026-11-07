; Other layers' continuations follow layer A's section, before final dispatch.
(in-package "ACL2")
(include-book "assembly-callbacks-s")
(include-book "assembly-callbacks-d")
; Recovery's payload pass reads layers C's and D's record shapes.
(include-book "recovery-payload")
; Other layers' continuation event macros go HERE, before final dispatch.
; B5 recovery's arms (recovery-machine.lisp, in the arm language).
(fn2-recovery-events-3)
(include-book "boot")
(fn2-boot-events)

(table fn2-costs 'fn2-conn-run-greeting nil)
(fn2-resolve :callbacks)
