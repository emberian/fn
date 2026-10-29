; Other layers' continuations follow layer A's section, before final dispatch.
(in-package "ACL2")
(include-book "assembly-callbacks-a")
; Other layers' continuation event macros go HERE, before final dispatch.
(fn2-commit-events)

(fn2-resolve :callbacks)
