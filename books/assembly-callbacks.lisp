; Other layers' continuations follow layer A's section, before final dispatch.
(in-package "ACL2")
(include-book "assembly-callbacks-s")
(include-book "assembly-callbacks-d")
; Other layers' continuation event macros go HERE, before final dispatch.
; B5 recovery's arms (recovery-machine.lisp, in the arm language).
(fn2-recovery-events-3)

(table fn2-costs 'fn2-conn-run-greeting nil)
(fn2-resolve :callbacks)
