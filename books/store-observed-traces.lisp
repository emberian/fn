; Folded into store-observed.lisp (2026-09-19 realignment): the process-root
; relation (D6) and reopen retention (D5) theorems now live beside the entry
; point whose guard proof they share.  This book remains only as an include
; shim for books/bp-receiver-evolving-store-invariants.lisp; switch that
; include to "store-observed" and delete this file.
(in-package "ACL2")
(include-book "store-observed")
