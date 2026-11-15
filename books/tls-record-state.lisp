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

; Project the accepted PUBLIC Receive effect for the existing boundary trace.
; Private child plaintext belongs to the upper codec, not the application loan.
(defun fn2-tls-record-input-prefix (serial action offset count fn2-tls-record)
 (declare (xargs :stobjs fn2-tls-record :verify-guards nil
  :guard (and (fn2-tls-record-wfp fn2-tls-record) (= (fn2-tls-record-rows fn2-tls-record) 1))))
 (cond
  ((or (not (equal action 12)) (equal count 0)
       (not (= (fn2-tls-record-parent-serial 0 fn2-tls-record) 0))) (mv :none 0 0))
  ((not (and (posp serial) (unsigned-byte-p 60 serial)
              (unsigned-byte-p 32 offset) (posp count) (unsigned-byte-p 32 count)
              (= (fn2-tls-record-writep 0 fn2-tls-record) 0)
              (= (fn2-tls-record-pending-serial 0 fn2-tls-record) 0)
              (= (fn2-tls-record-pending-action 0 fn2-tls-record) 12)
              (= (fn2-tls-record-last-serial 0 fn2-tls-record) serial)
              (= (fn2-tls-record-ssl-progress 0 fn2-tls-record) serial)
              (<= count (fn2-tls-record-sink-count 0 fn2-tls-record))
              (= (+ offset count) (fn2-tls-record-sink-progress 0 fn2-tls-record))
              (<= (+ offset count) (fn2-tls-record-extent 0 fn2-tls-record))))
   (mv :stale 0 0))
  (t (mv :input-prefix offset count))))
(verify-guards fn2-tls-record-input-prefix
 :hints (("Goal" :in-theory
  (set-difference-theories (current-theory :here) (theory 'fn2-tls-record-readers)))))
