;;; Native AUTHINFO profile transport.
;;;
;;; This raw module reads one bounded regular file selected by ACL2 and hands
;;; its octets to books/native-auth-profile.lisp.  It does not parse TOML,
;;; decode hex, build credentials, choose permissions, hash secrets or mark a
;;; socket protected.  TLS availability is observed only from a successfully
;;; loaded service context, never inferred from configured path text.

(in-package "ACL2")

(defvar *fnn-owner-startup-hooks* nil)



(defvar *fnn-native-auth-live-path* nil
  "The credential file this owner was started with, for the reload
(host/native/login-bindings.lisp, control request 14).  NIL: none.")

(defvar *fnn-native-auth-live-policy* nil
  "(REQUIREDP PROTECTED-ONLYP) this owner was started with: the reload
(control request 14) rebuilds the credential table under the same policy.")

(defun fnn-native-auth-load-config (octets presentp requiredp protected-onlyp
                                    tls-availablep max-credentials)
  "ACL2's credential table for OCTETS (fn-native-auth-host-load), or
(values nil REASON) when ACL2 refuses the file."
  (let* ((result
           (fnn-core 'fn-native-auth-host-load octets presentp
                     requiredp protected-onlyp (and tls-availablep t)
                     max-credentials))
         (status (fnn-core 'fn-native-auth-host-status result)))
    (if (eq status :accepted)
        (values (fnn-core 'fn-native-auth-host-config result) nil)
      (values nil (fnn-core 'fn-native-auth-host-reason result)))))

(defun fnn-native-auth-reload-config (service octets presentp max-credentials)
  "Replace the running owner's credential table with ACL2's table for the
credential file as it is now (a `principal set-password' against a running
owner).  The caller holds the owner mutex.  A connection open at that moment
keeps the table it pinned (fn-ocfg-open); the next connection pins this one.
Answers :accepted, or :refused (the old table stays) with the reason logged."
  (multiple-value-bind (config reason)
      (fnn-native-auth-load-config octets presentp
                                   (first *fnn-native-auth-live-policy*)
                                   (second *fnn-native-auth-live-policy*)
                                   (fnn-owner-service-tls-context service)
                                   max-credentials)
    (cond ((null config)
           (fnn-err "credential file reload refused: ~a" reason)
           :refused)
          ((eq (fnn-owner-action 'fn-owner-set-auth-config config) :ok) :accepted)
          (t (fnn-err "credential file reload: the owner rejected ACL2's table")
             :refused))))

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
                     (fnn-owner-result 'fn-ores-config-result-p
                                       'fn-owner-reconfigure-deltas cid deltas)))
                  :accepted)
        (return-from fnn-native-auth-publish-bindings :refused)))))

(defun fnn-native-auth-install (service path requiredp protected-onlyp
                                 tls-availablep max-credentials)
  "Load and install the exact ACL2-produced config before any connection opens.
MAX-CREDENTIALS is the store profile's max-credentials (D27, PRF-102)."
  (multiple-value-bind (octets presentp)
      (fnn-native-auth-read path (fnn-core 'fn-native-auth-host-max-octets
                                           max-credentials))
    (multiple-value-bind (config reason)
        (fnn-native-auth-load-config octets presentp requiredp protected-onlyp
                                     tls-availablep max-credentials)
      (unless config
        (fnn-refuse "AUTHINFO profile refused: ~a" reason))
      (unless (eq (fnn-owner-action 'fn-owner-set-auth-config config) :ok)
        (fnn-fault "owner rejected ACL2-produced AUTHINFO configuration"))
      ;; The same accepted file's login bindings (`signing' fields), for the
      ;; posting policy, are published into the configuration (PKT-221,
      ;; books/login-binding-live.lisp) before the listener opens.
      (setq *fnn-native-auth-live-path* path
            *fnn-native-auth-live-policy* (list requiredp protected-onlyp))
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
