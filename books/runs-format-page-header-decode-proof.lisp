; The stored page header decoder agrees with the layout scanner.
(in-package "ACL2")
(include-book "format-physical")
(include-book "runs-page-reader-proof")

(fn2-run-prove-page-reader fn2-format-page-header)
