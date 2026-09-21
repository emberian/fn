;;; Native AUTHINFO profile transport.
;;;
;;; This raw module reads one bounded regular file selected by ACL2 and hands
;;; its octets to books/native-auth-profile.lisp.  It does not parse TOML,
;;; decode hex, build credentials, choose permissions, hash secrets or mark a
;;; socket protected.  The current native image always reports TLS unavailable.

(in-package "ACL2")

(defvar *fnn-owner-startup-hooks* nil)

(defun fnn-native-auth-read (path maximum)
  "Return OCTETS,PRESENTP; missing is the existing empty credential registry."
  (let ((info (fnn-lstat path)))
    (if (null info)
        (values nil nil)
      (progn
        (when (or (fnn-symlink-p info) (not (fnn-regular-p info)))
          (fnn-refuse "AUTHINFO credential path is not a regular file: ~a" path))
        (when (> (sb-posix:stat-size info) maximum)
          (fnn-refuse "AUTHINFO credential file exceeds ACL2 bound: ~a" path))
        (values (fnn-octet-list (fnn-read-regular-bounded path maximum)) t)))))

(defun fnn-native-auth-install (path requiredp protected-onlyp)
  "Load and install the exact ACL2-produced config before any connection opens."
  (multiple-value-bind (octets presentp)
      (fnn-native-auth-read path (fnn-core 'fn-native-auth-host-max-octets))
    (let* ((result
             (fnn-core 'fn-native-auth-host-load octets presentp
                       requiredp protected-onlyp nil))
           (status (fnn-core 'fn-native-auth-host-status result)))
      (unless (eq status :accepted)
        (fnn-refuse "AUTHINFO profile refused: ~a"
                    (fnn-core 'fn-native-auth-host-reason result)))
      (let ((config (fnn-core 'fn-native-auth-host-config result)))
        (unless (eq (fnn-owner-action 'fn-owner-set-auth-config config) :ok)
          (fnn-fault "owner rejected ACL2-produced AUTHINFO configuration")))
      :accepted)))

(defun fnn-native-auth-startup-hook (path requiredp protected-onlyp)
  "Return a composable owner hook; SERVICE is intentionally not semantic input."
  (lambda (service)
    (declare (ignore service))
    (fnn-native-auth-install path requiredp protected-onlyp)))
