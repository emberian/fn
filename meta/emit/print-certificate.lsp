(in-package "ACL2")
(include-book "books/assembly-callbacks-a")
(ld "books/translation-validation.lisp")
:q
(load "meta/emit/print-world.lisp")
(in-package "ACL2")
(meta-print-certificate "meta/emit/bridge-certificate.sexp"
                        '(fn2-echo-run-free fn2-echo-run-free-children) 'fn2-echo)
