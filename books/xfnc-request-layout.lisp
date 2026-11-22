; Shared outbound and inbound bounds for the peer XFNC request profile.
(in-package "ACL2")
(include-book "fnct-pool")
(fn2-book-layer :e)

; A peer registers one stream. The canonical stream list encodes each
; name as (:octets 64), inside REGISTER's length-prefixed streams field.
(deflayout fn2-xfnc-stream-name '((name (:octets 64))))
(defconst *fn2-xfnc-register-body-max* (+ 1 1 8 2 1 64 1))
(defconst *fn2-xfnc-read-body-max* (+ 1 2 366 4 4))

