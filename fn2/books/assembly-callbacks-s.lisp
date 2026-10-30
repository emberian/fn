; B5 recovery's table-level operations, after the commit continuations
; (they reuse its opaque invariant interface); the arms follow in
; assembly-callbacks.lisp.
(in-package "ACL2")
(include-book "assembly-callbacks-r")
(include-book "recovery-machine")
(fn2-recovery-events)
