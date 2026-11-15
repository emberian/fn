; Public kind keeps its original dependency order and admission partition.
; The stable schema provider is independently reusable across arm changes.
(in-package "ACL2")
(include-book "machines-a")
(include-book "codec-profile")
(include-book "core-children")
(include-book "machine-arms")
(include-book "tls-schema")
(fn2-book-layer :d)
(defmachine-registry fn2-tls-admit)
