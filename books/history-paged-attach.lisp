; The canonical history exports retain their logical all-event sequence.
; The installed physical foundation is one resident P3 prefix and append tail.
(in-package "ACL2")
(include-book "history-paged")
(attach-stobj fn-hist fn-hist-paged)
(include-book "history-columns")
