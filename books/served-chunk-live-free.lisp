; served-chunk-live-free.lisp -- a served chunk that selects nothing does not
; read the committed view (lane join-f2-2, 2026-09-29; PKT-731).

(in-package "ACL2")

(include-book "served-tls-prefix")

(local (in-theory (disable (tau-system))))
