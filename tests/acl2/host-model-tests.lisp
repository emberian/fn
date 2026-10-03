; Teeth for books/host-model.lisp (lane host-model, PRF-1242..1244).  The
; reached schedules are written as the book's theorems land; this file is
; a Makefile root from the book's first commit so the roots resolve.
(in-package "ACL2")
(include-book "../../books/host-model")

(assert-event (fn-hmc-invp (fn-hmc-init)))
