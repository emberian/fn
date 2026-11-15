(in-package "ACL2")
(include-book "books/assembly-callbacks-e-cns")
(include-book "books/translation-validation")
:q
(load "meta/emit/print-world.lisp")
(in-package "ACL2")
; One actual served helper, with full body/guard/measure dependency closure.
; No unrelated CNS arm or convenience reader roots are added.
(meta-print-certificate "meta/emit/cns-timer-certificate.sexp"
 '(fn2-cns-clear-wait-timer) 'fn2-cns nil nil)
