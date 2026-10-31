; Register the sole served instance, then materialize its kind index and directory.
(in-package "ACL2")
(include-book "machines-all")
(include-book "machine-dispatch")
(include-book "reference-state")
; B/C/D registration books go HERE, before either registry is consumed.
(include-book "machines-b")
(include-book "machines-c-sealer")
(include-book "conn")
(include-book "upload")
(include-book "txn")
(fn2-machine-index-events)
(in-theory (disable fn2-machine-local-id))
(fn2-machine-directory-events)
