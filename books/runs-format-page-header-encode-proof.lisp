; The enclosing page header encoder writes its ten fields at the page start.
(in-package "ACL2")
(include-book "runs-header-emitter-proof")
(fn2-run-prove-header-encoder fn2-format-page-header *fn2-format-page-header*)
