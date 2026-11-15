; Concrete per-capability transport storage, generated once by defcolumns.
(in-package "ACL2")
(include-book "codec-transport")
(fn2-book-layer :a)

(defcodec-transport fn2-tls-transport
 ((quantum :u32)
  ;; SSL status: 0 complete, 1 WANT_READ, 2 WANT_WRITE, 5 must-call.
  (ssl-status :u8)
  ;; Last physical progress/SSL observation, excluding socket EAGAIN attempts.
  (progress-serial :u60))
 :rows-bound 2)

; One generated reader theory, shared by guards and ownership proofs.
(make-event
 (let* ((row (fn2-decl-row '(:columns fn2-tls-transport) (w state)))
        (readers (fn2-columns-projection-readers 'fn2-tls-transport
                   (fn2-decl-get :columns row))))
  (value `(deftheory fn2-tls-transport-readers
            ',(cons 'fn2-tls-transport-rows readers)))))
