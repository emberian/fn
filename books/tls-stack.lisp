; COMPRESS private windows use the same TLS record controller as pool loans.
(in-package "ACL2")
(include-book "codec-stack")
(include-book "compress-transport-state")
(include-book "tls-record")
(fn2-book-layer :d)
(defcodec-stack-bridge fn2-compress-tls fn2-compress-transport fn2-tls-transport fn2-tls-record)
