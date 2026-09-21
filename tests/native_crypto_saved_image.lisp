;;; Save a core with deliberately stale facility state, then check its restart.

(unless (find-package "ACL2") (make-package "ACL2" :use '("COMMON-LISP")))
(load "host/native/crypto.lisp")
(in-package "ACL2")

(defun fnn-crypto-saved-image-test-main ()
  (handler-case
      (progn
        (fnn-crypto-startup)
        (unless (and (eq *fnn-crypto-state* :ready)
                     (not (string= *fnn-crypto-library* "serialized stale library"))
                     (not (string= *fnn-crypto-version* "serialized stale version"))
                     (= (length (fnn-crypto-sha512 #(97 98 99))) 64))
          (error "saved-image crypto startup did not refresh the facility"))
        (format t "FN_NATIVE_CRYPTO_SAVED_IMAGE_TEST passed library=~s version=~s~%"
                *fnn-crypto-library* *fnn-crypto-version*)
        (sb-ext:exit :code 0))
    (error (condition)
      (format *error-output* "FN_NATIVE_CRYPTO_SAVED_IMAGE_TEST failed: ~a~%"
              condition)
      (sb-ext:exit :code 1))))

(fnn-crypto-initialize)
(setq *fnn-crypto-state* :ready
      *fnn-crypto-library* "serialized stale library"
      *fnn-crypto-version* "serialized stale version")
(let ((core (sb-ext:posix-getenv "FN_CRYPTO_TEST_CORE")))
  (unless core (error "FN_CRYPTO_TEST_CORE is unset"))
  (sb-ext:save-lisp-and-die core :toplevel #'fnn-crypto-saved-image-test-main))
