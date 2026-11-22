; Materialize layer C's first core operations after the core instance: the
; private successor's :prepare half (C-S3: put, arg, arg-octets,
; arg-octets-late, resolve). The stage half is assembly-callbacks-c-commit's,
; the group directory, the identity decision and the sealer
; assembly-callbacks-c's: one book made 69 s on forge (the one-minute rule;
; C-SUCCESSOR-BOOK).
(in-package "ACL2")
(include-book "query-ref-wake")
(include-book "machines-c-bind")
(include-book "journal-retention-core")
(include-book "peer-retained-drain")
(fn2-csnapshot-core-events)
(fn2-journal-retention-core-events)
(fn2-peer-retained-drain-events)
(fn2-successor-prepare-events)
