; Materialize the private successor's stage half (C-S3: stage, out,
; fill-octets, bind, release, publish, drop) after its :prepare half.
(in-package "ACL2")
(include-book "assembly-callbacks-c-prepare")
(fn2-successor-commit-events)
