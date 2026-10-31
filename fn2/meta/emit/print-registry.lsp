; Prints fn2's world for the Lean side (fn2/meta/emit/print-world.lisp): the declaration
; registry and the closed subset's embedding, as one S-expression in fn2/meta/emit/world.sexp.
; Ordinary top-level I/O, never a certifying event (the pattern of fn2/tools/owed-export.lsp).
; Run from the worktree root after `fn2/tools/certify.sh books/reference.lisp`:
;   fn2/meta/emit/emit.sh
(in-package "ACL2")
(include-book "fn2/books/reference")
:q
(load "fn2/meta/emit/print-world.lisp")
(in-package "ACL2")
(meta-print-world "fn2/meta/emit/world.sexp")
