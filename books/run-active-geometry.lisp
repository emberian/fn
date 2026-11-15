; Shared active-source work geometry. This bounds simultaneous merge heads,
; not stored entries/pages; the sealer compacts sources within this envelope.
(in-package "ACL2")
(include-book "declare")
(fn2-book-layer :b)
(defconst *fn2-run-active-source-cursors* 8)
