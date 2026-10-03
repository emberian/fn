;;; S092: actual self-signed key generator receives an injected EVP failure.
;;; The real OpenSSL context is allocated and freed; the original diagnostic
;;; remains a typed fnn-tls-unavailable condition, never FIRST-of-string.
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defvar *the-live-state* nil)
(defun f-get-global (name state) (declare (ignore name state)) nil)
(load "tests/native_io_prelude.lisp")
(load "host/native/io.lisp")
(load "host/native/tls.lisp")
(fnn-tls-initialize)
(let* ((init (symbol-function 'fnn-%evp-pkey-keygen-init))
       (free (symbol-function 'fnn-%evp-pkey-ctx-free))
       (stack (symbol-function 'fnn-tls-error-stack))
       (frees 0) (reached nil))
  (unwind-protect
       (progn
         (setf (symbol-function 'fnn-%evp-pkey-keygen-init)
               (lambda (ctx) (declare (ignore ctx)) (setq reached t) 0)
               (symbol-function 'fnn-%evp-pkey-ctx-free)
               (lambda (ctx) (incf frees) (funcall free ctx))
               (symbol-function 'fnn-tls-error-stack)
               (lambda () "injected OpenSSL keygen failure"))
         (let ((condition (handler-case (progn (fnn-tls-ssc-generate-key) nil)
                            (error (e) e))))
           (unless (and reached (= frees 1) (typep condition 'fnn-tls-unavailable)
                        (search "EVP_PKEY_keygen_init failed: injected OpenSSL keygen failure"
                                (princ-to-string condition)))
             (error "self-signed failure changed condition type or lost cleanup: ~s / ~s" condition frees))))
    (setf (symbol-function 'fnn-%evp-pkey-keygen-init) init
          (symbol-function 'fnn-%evp-pkey-ctx-free) free
          (symbol-function 'fnn-tls-error-stack) stack)))
(format t "native_self_signed_original_failure_and_context_cleanup: PASS~%")
