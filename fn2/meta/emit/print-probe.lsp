; Prints the measured world (fn2/meta/emit/print-world.lisp) from reference plus the probe book
; (fn2/meta/emit/meta-probe.lisp) into world-probe.sexp, from which emit.sh emits the embedding,
; so the probe kinds are translated beside the served ones (the registry stays reference's,
; print-registry.lsp). Run from the worktree root after `fn2/tools/certify.sh
; meta/emit/meta-probe.lisp`.
(in-package "ACL2")
(include-book "fn2/meta/emit/meta-probe")
(include-book "fn2/books/reference")
:q
(load "fn2/meta/emit/print-world.lisp")
(in-package "ACL2")
(meta-print-world "fn2/meta/emit/world-probe.sexp")
