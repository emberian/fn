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

;;; S093: actual exclusive writer owns a newly created file. The real
;;; descriptor is closed even when a close failure is injected afterward.
(let* ((saved (mapcar (lambda (name) (cons name (symbol-function name)))
                     '(fnn-write-all fnn-fsync-file fnn-close)))
       (close (symbol-function 'fnn-close))
       (root (format nil "/tmp/fn-ssc-failure-~d-~a" (sb-posix:getpid) (fnn-random-hex 8))))
  (sb-posix:mkdir root #o700)
  (unwind-protect
       (dolist (operations '((:write) (:fsync) (:close) (:write :close) (:fsync :close)))
         (let ((path (fnn-join root "candidate")) (closed 0))
           (dolist (pair saved) (setf (symbol-function (car pair)) (cdr pair)))
           (when (member :write operations)
             (setf (symbol-function 'fnn-write-all)
                   (lambda (fd bytes) (declare (ignore fd bytes)) (fnn-os-fail sb-posix:eio))))
           (when (member :fsync operations)
             (setf (symbol-function 'fnn-fsync-file)
                   (lambda (fd) (declare (ignore fd)) (fnn-os-fail sb-posix:eio))))
           (setf (symbol-function 'fnn-close)
                 (lambda (fd) (incf closed) (funcall close fd)
                   (when (member :close operations) (fnn-os-fail sb-posix:enospc))))
           (let ((condition (handler-case
                                (progn (fnn-tls-ssc-write-new path '(1 2 3) #o600) nil)
                              (error (e) e))))
             (unless (and (typep condition 'fnn-os-error) (= closed 1)
                          (= (fnn-os-errno condition)
                             (if (or (member :write operations) (member :fsync operations))
                                 sb-posix:eio sb-posix:enospc))
                          (not (probe-file path)))
               (error "self-signed owned-file cleanup or primary failure changed at ~s" operations)))))
    (dolist (pair saved) (setf (symbol-function (car pair)) (cdr pair)))
    ;; This directory and every candidate are solely this witness's files.
    (let ((candidate (fnn-join root "candidate")))
      (when (probe-file candidate) (fnn-unlink candidate)))
    (sb-posix:rmdir root)))
(format t "native_self_signed_owned_file_cleanup_and_primary_failure: PASS~%")
