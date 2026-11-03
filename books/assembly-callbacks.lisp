; Other layers' continuations follow layer A's section, before final dispatch.
(in-package "ACL2")
(include-book "assembly-callbacks-t")
(include-book "assembly-callbacks-d")
; Other layers' continuation event macros go HERE, before final dispatch.
(fn2-recovery-events-3)

(table fn2-costs 'fn2-conn-run-greeting nil)
(fn2-resolve :callbacks)
