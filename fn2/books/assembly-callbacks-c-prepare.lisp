; Materialize layer C's first core operations after the core instance: the
; identity decisions (C-S1) and the private successor's :prepare half (C-S3:
; put, arg, arg-octets, arg-octets-late, resolve). The stage half is
; assembly-callbacks-c-commit's, the group directory and the sealer
; assembly-callbacks-c's: one book made 69 s on forge (the one-minute rule;
; C-SUCCESSOR-BOOK).
(in-package "ACL2")
(include-book "assembly-callbacks-b2")
(include-book "machines-c-bind")
(fn2-identity-core-events)
(fn2-successor-prepare-events)
