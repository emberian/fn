(in-package "ACL2")
(include-book "books/assembly-callbacks-a")
(include-book "books/translation-validation")
:q
(load "meta/emit/print-world.lisp")
(in-package "ACL2")
(meta-print-certificate "meta/emit/loop-certificate.sexp"
                        '(fn2-pool-compare-loop) 'fn2-echo)
