; Prints the measured world (meta/emit/print-world.lisp) from reference plus the probe book
; (meta/emit/meta-probe.lisp) into world-probe.sexp, from which emit.sh emits the embedding,
; so the probe kinds are translated beside the served ones (the registry stays reference's,
; print-registry.lsp). Run from the worktree root after `tools/certify.sh
; meta/emit/meta-probe.lisp`.
(in-package "ACL2")
(include-book "meta/emit/meta-probe")
(include-book "books/reference")
:q
(load "meta/emit/print-world.lisp")
(in-package "ACL2")
(meta-print-world "meta/emit/world-probe.sexp")
