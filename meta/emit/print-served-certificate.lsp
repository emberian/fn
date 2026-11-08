(in-package "ACL2")
(include-book "books/reference")
(include-book "books/translation-validation")
:q
(load "meta/emit/print-world.lisp")
(in-package "ACL2")
(meta-print-served-certificate "meta/emit/served-certificate.sexp")
