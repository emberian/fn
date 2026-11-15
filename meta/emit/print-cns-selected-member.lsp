; Run only in the shared admitted served world; do not load a duplicate world.
(in-package "ACL2")
(include-book "books/assembly-attach")
(include-book "books/translation-validation")
:q
(load "meta/emit/print-world.lisp")
(in-package "ACL2")
(meta-print-certificate "meta/emit/cns-selected-member.sexp"
                        '(fn2-cns-run-stub) 'fn2-cns nil nil)
