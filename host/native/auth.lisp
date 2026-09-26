;;; Native AUTHINFO profile transport.
;;;
;;; This raw module reads one bounded regular file selected by ACL2 and hands
;;; its octets to books/native-auth-profile.lisp.  It does not parse TOML,
;;; decode hex, build credentials, choose permissions, hash secrets or mark a
;;; socket protected.  TLS availability is observed only from a successfully
;;; loaded service context, never inferred from configured path text.

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

(defvar *fnn-native-auth-live-path* nil
  "The credential file this owner was started with, for the binding reload
(host/native/login-bindings.lisp, control request 14).  NIL: none.")

(defun fnn-native-auth-publish-bindings (service octets presentp max-credentials)
  "Publish the credential file's login bindings into the owner's configuration.
PKT-221: ACL2's fn-lb-sync-plan names the delta lists; each is staged and made
durable through fnn-owner-live-reconfigure-locked, the one live path.  The
caller holds the owner mutex.  Answers :accepted, or :refused before any
record whose publication was refused (records published before it stand)."
  (let ((plan (fnn-owner-core 'fn-owner-login-bindings-plan
                              (fnn-core 'fn-native-auth-host-load-bindings
                                        octets presentp max-credentials))))
    (unless (and (consp plan) (eq (first plan) :ok) (listp (second plan)))
      (fnn-err "login bindings refused: ~a" (and (consp plan) (second plan)))
      (return-from fnn-native-auth-publish-bindings :refused))
    (dolist (deltas (second plan) :accepted)
      (unless (eq (fnn-owner-live-reconfigure-locked
                   service
                   (lambda (cid)
                     (fnn-owner-action 'fn-owner-reconfigure-deltas cid deltas)))
                  :accepted)
        (return-from fnn-native-auth-publish-bindings :refused)))))

(defun fnn-native-auth-install (service path requiredp protected-onlyp
                                 tls-availablep max-credentials)
  "Load and install the exact ACL2-produced config before any connection opens.
MAX-CREDENTIALS is the store profile's max-credentials (D27, PRF-102)."
  (multiple-value-bind (octets presentp)
      (fnn-native-auth-read path (fnn-core 'fn-native-auth-host-max-octets
                                           max-credentials))
    (let* ((result
             (fnn-core 'fn-native-auth-host-load octets presentp
                       requiredp protected-onlyp (and tls-availablep t)
                       max-credentials))
           (status (fnn-core 'fn-native-auth-host-status result)))
      (unless (eq status :accepted)
        (fnn-refuse "AUTHINFO profile refused: ~a"
                    (fnn-core 'fn-native-auth-host-reason result)))
      (let ((config (fnn-core 'fn-native-auth-host-config result)))
        (unless (eq (fnn-owner-action 'fn-owner-set-auth-config config) :ok)
          (fnn-fault "owner rejected ACL2-produced AUTHINFO configuration")))
      ;; The same accepted file's login bindings (`signing' fields), for the
      ;; posting policy, are published into the configuration (PKT-221,
      ;; books/login-binding-live.lisp) before the listener opens.
      (setq *fnn-native-auth-live-path* path)
      (unless (eq (fnn-owner-serialized
                   service nil
                   (lambda ()
                     (fnn-native-auth-publish-bindings service octets presentp
                                                       max-credentials)))
                  :accepted)
        (fnn-refuse "owner refused to publish the credential file's login bindings"))
      :accepted)))

(defun fnn-native-auth-startup-hook (path requiredp protected-onlyp)
  "Return a composable owner hook.  SERVICE contributes only whether a real
TLS context loaded; ACL2 still owns the authentication policy decision."
  (lambda (service)
    (fnn-native-auth-install service path requiredp protected-onlyp
                             (fnn-owner-service-tls-context service)
                             (fnn-profile-nat 'fn-store-profile-max-credentials
                                              (fnn-owner-service-store service)))))
