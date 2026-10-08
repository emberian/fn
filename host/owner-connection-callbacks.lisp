; Single guarded callback implementation lives in the admitted pure/state leaf.
; Loading this adapter does not install or select any native callback.
(in-package "ACL2")
; D61: the image attaches these (attach-stobj) before the generic they implement;
; a certified host file carries the same order in its own world (tools/host_check.py --attach-order).
(include-book "../books/payload-arena-attach")
(include-book "../books/history-paged-attach")
(include-book "../books/catalog-paged-attach")
(include-book "../books/owner-connection-callbacks")
