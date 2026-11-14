; Per-operation TLS state, separate from the capability's retained ciphertext.
(in-package "ACL2")
(include-book "codec-transport")
(fn2-book-layer :a)
(defcodec-operation fn2-tls-record
 ((writep :bool) (status :u8) (seen-progress :u60) (ssl-progress :u60) (interest :u8) (kick :bool)))
(make-event
 (value `(deftheory fn2-tls-record-readers
  ',(cons 'fn2-tls-record-rows
     (fn2-columns-projection-readers 'fn2-tls-record
      (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-tls-record) (w state))))))))
