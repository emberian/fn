; Per-core-operation application progress, emitted by the shared codec factory.
; Wire/compressed prefixes live only in fn2-compress-transport.
(in-package "ACL2")
(include-book "codec-transport")
(fn2-book-layer :d)
(defcodec-operation fn2-compress-operation
 ((flush-complete :bool) (need-input :bool) (interest :u8) (kick :bool)
  (result (:enum fn2-compress-op-result (:running :draining :done :eof :failed :cancelled :limit)))))
