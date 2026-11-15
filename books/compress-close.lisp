; Shared physical reclamation enables deferred public cancellation.
(in-package "ACL2")
(include-book "compress-record")
(include-book "compress-transport-lifecycle")
(include-book "codec-close")
(include-book "tls-stack")
(fn2-book-layer :d)
(defcodec-record-closure fn2-compress-operation fn2-compress-transport)

; Whole-carrier Close first frees TLS. Its private child may have consumed a
; prefix while the parent remained pending. Settle that prefix once before
; retiring compression; application progress remains in the outer operation.
(defun fn2-compress-record-close-child
 (cap nonce slot generation fn2-compress-operation fn2-compress-transport fn2-tls-transport fn2-tls-record)
 (declare (xargs :stobjs (fn2-compress-operation fn2-compress-transport fn2-tls-transport fn2-tls-record)
  :verify-guards nil
  :guard (and (fn2-compress-operation-wfp fn2-compress-operation)
              (= (fn2-compress-operation-rows fn2-compress-operation) 1)
              (fn2-compress-transport-wfp fn2-compress-transport)
              (= (fn2-compress-transport-rows fn2-compress-transport) 1)
              (fn2-tls-transport-wfp fn2-tls-transport)
              (fn2-tls-record-wfp fn2-tls-record))))
 (mv-let (code serial action used made)
  (fn2-compress-tls-closed-child cap nonce slot generation
   fn2-compress-transport fn2-tls-transport fn2-tls-record)
  (if (not (eq code :ok)) (mv code fn2-compress-operation fn2-compress-transport)
   (if (not (and (equal serial (fn2-compress-operation-pending-serial 0 fn2-compress-operation))
                 (equal action (fn2-compress-operation-pending-action 0 fn2-compress-operation))
                 (fn2-compress-operation-observable-p serial 0 0 fn2-compress-operation)))
       (mv :stale fn2-compress-operation fn2-compress-transport)
    (mv-let (advanced fn2-compress-transport)
     (fn2-compress-transport-advance-spans cap nonce slot generation serial used made fn2-compress-transport)
     (if (not (eq advanced :ok)) (mv advanced fn2-compress-operation fn2-compress-transport)
      (mv-let (observed fn2-compress-operation)
       (fn2-compress-operation-observe serial 0 0 fn2-compress-operation)
       (let ((fn2-compress-transport (fn2-compress-transport-put 0 (terminal 2))))
        (mv observed fn2-compress-operation fn2-compress-transport)))))))))

; A pending logical TLS child owns readiness until it settles. Plain socket
; retries use the outer operation's observed blocked interest and fresh serial.
(defun fn2-compress-record-stack-wait
 (fn2-compress-operation fn2-compress-transport fn2-tls-transport fn2-tls-record)
 (declare (xargs :stobjs (fn2-compress-operation fn2-compress-transport fn2-tls-transport fn2-tls-record)
  :verify-guards nil
  :guard (and (fn2-compress-operation-wfp fn2-compress-operation)
              (fn2-compress-transport-wfp fn2-compress-transport)
              (fn2-tls-transport-wfp fn2-tls-transport) (fn2-tls-record-wfp fn2-tls-record))))
 (if (and (= (fn2-compress-operation-rows fn2-compress-operation) 1)
          (= (fn2-compress-transport-rows fn2-compress-transport) 1)
          (fn2-compress-transport-match-p
           (fn2-compress-operation-cap 0 fn2-compress-operation)
           (fn2-compress-operation-nonce 0 fn2-compress-operation)
           (fn2-compress-operation-slot 0 fn2-compress-operation)
           (fn2-compress-operation-generation 0 fn2-compress-operation)
           (fn2-compress-operation-pending-serial 0 fn2-compress-operation) fn2-compress-transport)
          (member-equal (fn2-compress-transport-pending 0 fn2-compress-transport) '(5 6))
          (fn2-tls-transport-selected-p
           (fn2-compress-operation-cap 0 fn2-compress-operation)
           (fn2-compress-operation-nonce 0 fn2-compress-operation) fn2-tls-transport))
     (fn2-tls-record-wait fn2-tls-transport fn2-tls-record)
   (fn2-compress-record-wait fn2-compress-operation)))

(make-event
 (let* ((world (w state))
        (readers
         (append
          '(fn2-compress-operation-rows fn2-compress-transport-rows fn2-tls-transport-rows fn2-tls-record-rows
            fn2-compress-transport-advance-spans fn2-compress-operation-observe)
          (fn2-columns-projection-readers 'fn2-compress-operation
           (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-compress-operation) world)))
          (fn2-columns-projection-readers 'fn2-compress-transport
           (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-compress-transport) world)))
          (fn2-columns-projection-readers 'fn2-tls-transport
           (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-tls-transport) world)))
          (fn2-columns-projection-readers 'fn2-tls-record
           (fn2-decl-get :columns (fn2-decl-row '(:columns fn2-tls-record) world)))))
        (hints `(("Goal" :in-theory (disable ,@readers)))))
  (value `(progn
   (verify-guards fn2-compress-record-close-child :hints ,hints)
   (verify-guards fn2-compress-record-stack-wait :hints ,hints)))))
