; Prints fn2's world for the Lean side (meta/emit/print-world.lisp): the declaration
; registry and the closed subset's embedding, as one S-expression in meta/emit/world.sexp.
; Ordinary top-level I/O, never a certifying event (the pattern of tools/owed-export.lsp).
; Run from the worktree root after `tools/certify.sh books/reference.lisp`:
;   meta/emit/emit.sh
(in-package "ACL2")
(include-book "books/reference")
:q
(load "meta/emit/print-world.lisp")
(in-package "ACL2")
(meta-print-world "meta/emit/world.sexp")
