; Other layers' continuations follow layer A's section, before final dispatch.
(in-package "ACL2")
(include-book "assembly-callbacks-t")
(include-book "assembly-callbacks-d-conn2")
(include-book "assembly-callbacks-d-upload")
(include-book "assembly-callbacks-d-txn")
(include-book "assembly-callbacks-d-cursor")
; Other layers' continuation event macros go HERE, before final dispatch.
(fn2-cns-events)
(fn2-recovery-events-3)

(fn2-resolve :callbacks)
