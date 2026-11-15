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

; TLS policy selects public Receive action12; ownership/progress is shared.
(defun fn2-tls-record-public-input-prefix (serial action offset count fn2-tls-record)
 (declare (xargs :stobjs fn2-tls-record :verify-guards nil
  :guard (and (fn2-tls-record-wfp fn2-tls-record) (= (fn2-tls-record-rows fn2-tls-record) 1))))
 (if (not (= (fn2-tls-record-writep 0 fn2-tls-record) 0)) (mv :none 0 0)
  (fn2-tls-record-input-prefix serial action 12 offset count fn2-tls-record)))
(verify-guards fn2-tls-record-public-input-prefix
 :hints (("Goal" :in-theory
  (set-difference-theories (current-theory :here) (theory 'fn2-tls-record-readers)))))
