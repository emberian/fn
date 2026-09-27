; The world the extractor reads: the served step machine and the reader seed,
; with the attachments the native image makes, in its order
; (host/native/build.lisp): the codec seams, the concrete record encoder,
; then the payload arena's attachment before any book that names fn-arena.
(in-package "ACL2")
(include-book "../../books/codec-attach")
(include-book "../../books/records-attach-concrete")
(include-book "../../books/payload-arena-attach")
(include-book "../../books/served")
(include-book "../../books/reader-open-carried")
(include-book "../../books/store-node")
