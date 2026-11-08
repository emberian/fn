(in-package "ACL2")
(include-book "books/assembly-callbacks-e-cns")
(include-book "books/translation-validation")
:q
(load "meta/emit/print-world.lisp")
(in-package "ACL2")
(meta-print-certificate "meta/emit/core-certificate.sexp"
 '(fn2-cns-run-draining fn2-cns-on-read-result)
 'fn2-cns '(fn2-cns-reclaim fn2-cns-lease-release))
