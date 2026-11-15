; Scoped proposal only: run after the current callback closure is qualified.
(in-package "ACL2")
(include-book "books/assembly-callbacks-e-cns")
(include-book "books/translation-validation")
:q
(load "meta/emit/print-world.lisp")
(in-package "ACL2")
(meta-print-certificate "meta/emit/cns-member-certificate.sexp"
 '(fn2-cns-run-draining) 'fn2-cns nil nil)
