; Other layers' continuations follow layer A's section, before final dispatch.
(in-package "ACL2")
(include-book "assembly-callbacks-t")
; Other layers' continuation event macros go HERE, before final dispatch.
(fn2-recovery-events-3)

(fn2-resolve :callbacks)
