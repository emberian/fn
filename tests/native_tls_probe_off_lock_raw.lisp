;;; The OpenSSL library probe (a stat of each candidate pair) never runs while
;;; the TLS initialization lock is held (lock discipline R2): initialization
;;; observes the filesystem first, then loads under the lock.
(require :sb-posix)
(defpackage "ACL2" (:use "CL") (:shadow #:probe-file))
(in-package "ACL2")
(defvar *probes* nil)
(defvar *lock-held-at-probe* nil)
(defun probe-file (path)
  (push path *probes*)
  (when (sb-thread:holding-mutex-p *fnn-tls-initialize-lock*)
    (setq *lock-held-at-probe* t))
  (cl:probe-file path))
(defun fnn-tls-missing-symbols () '("stub"))
(defun load-shipped (path kinds names)
  (with-open-file (stream path)
    (dolist (wanted names)
      (file-position stream 0)
      (loop for form = (read stream nil :eof) until (eq form :eof)
            when (and (consp form) (member (car form) kinds) (eq (cadr form) wanted))
              do (eval form) (return)))))
(let ((file "host/native/tls.lisp"))
  (load-shipped file '(define-condition) '(fnn-tls-error fnn-tls-unavailable))
  (load-shipped file '(defvar defparameter)
                '(*fnn-tls-state* *fnn-tls-libraries* *fnn-tls-pinned-libraries*
                  *fnn-tls-version* *fnn-tls-pinned-missing*
                  *fnn-tls-initialize-lock* *fnn-tls-default-openssl-prefix*))
  (load-shipped file '(defun)
                '(fnn-tls-openssl-prefix fnn-tls-configured-library-pair
                  fnn-tls-system-library-candidates fnn-tls-select-pair
                  fnn-tls-library-selection fnn-tls-load-libraries
                  fnn-tls-require-initialized fnn-tls-initialize)))
(sb-posix:setenv "FN_OPENSSL_PREFIX" "/nonexistent-openssl-prefix" 1)
(handler-case (fnn-tls-initialize)
  (fnn-tls-unavailable () nil))
(unless *probes* (error "initialization probed no library path"))
(when *lock-held-at-probe*
  (error "a library path was probed while the TLS initialization lock was held"))
(unless (eq *fnn-tls-state* :unavailable)
  (error "a failed initialization is not :unavailable"))
(format t "native TLS probe off lock: PASS~%")
