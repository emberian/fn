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

;;; Actual account adoption is a continuation, not a table setter. The core
;;; owns its source capture, funded candidate work, selected record and saved
;;; publication decision. One serialized action is one bounded preparation or
;;; durable publication quantum; concurrent configuration changes are checked
;;; by the core before any later mutation. No credentials become usable from
;;; a pending stage or merely from successful parsing of this file.
;;;
;;; NOTREADY source join: owner adoption begin/tick and typed account prepare/
;;; finish must be installed together with the operation census and restart
;;; producer. This caller deliberately has no direct-set-config fallback.
(defun fnn-native-auth-adopt-config (service config bindings)
  (let ((entropy (fnn-owner-consumer-entropy-observation)))
    (multiple-value-bind (word answer)
        (fnn-owner-serialized-with-control-turn
          service nil
          (lambda (slot nonce slots pool)
            (let ((result (fnn-account-adoption-begin
                            config bindings entropy slot nonce slots pool)))
              (setf config nil bindings nil entropy nil)
              (multiple-value-prog1 (values-list result) (setf result nil))))
          :control #'fnn-account-adoption-epilogue)
      (declare (ignore answer))
      ;; The outer issuer exposes only core word/answer after scheduler
      ;; cleanup. Missing installed binding invokes no allocating callback.
      (unless (eq word :yield)
        (return-from fnn-native-auth-adopt-config
          (case word
            (:accepted :accepted)
            (:recovery-required (fnn-indeterminate "account begin requires recovery"))
            ((:refused :unavailable :owner-control-unavailable) :refused)
            (otherwise (fnn-fault "malformed account begin result"))))))
    (loop
      (multiple-value-bind (word answer)
          (fnn-owner-serialized-with-control-turn
            service nil
            (lambda (slot nonce slots pool)
              (let* ((result (fnn-account-adoption-tick slot nonce slots pool))
                     (step (fnn-core 'fn-cado-result-action result))
                     (kind (fnn-core 'fn-cad-action-kind step)))
                (when (member kind '(:publish :configure))
                  (let ((durable
                         (if (eq kind :configure)
                             (fnn-owner-account-configuration-publication-locked service)
                           (fnn-owner-account-publication-locked service))))
                    (unless (eq durable :durable)
                      (fnn-fault "account publication returned ~a" durable))
                    (setf result (fnn-account-adoption-collect slot nonce slots pool))))
                (setf step nil)
                (multiple-value-prog1 (values-list result) (setf result nil))))
            :control #'fnn-account-adoption-epilogue)
        (declare (ignore answer))
        (case word
          (:yield nil)
          (:accepted (return :accepted))
          ((:refused :unavailable :owner-control-unavailable) (return :refused))
          (:recovery-required
           (fnn-indeterminate "account authority adoption requires recovery"))
          (otherwise (fnn-fault "owner returned malformed account adoption action")))))))

(defun fnn-native-auth-reload-config (service octets presentp max-credentials)
  "Adopt the parsed credential file through the durable account continuation.
The caller is outside the owner mutex; each bounded step acquires its own
quantum. Answers :accepted only after the final typed account/config commit, or
:refused while the previously admitted authority remains usable."
  (multiple-value-bind (config reason)
      (fnn-native-auth-load-config octets presentp
                                   (first *fnn-native-auth-live-policy*)
                                   (second *fnn-native-auth-live-policy*)
                                   (fnn-owner-service-tls-context service)
                                   max-credentials)
    (cond ((null config)
           (fnn-err "credential file reload refused: ~a" reason)
           :refused)
          (t (fnn-native-auth-adopt-config
              service config
              (fnn-core 'fn-native-auth-host-load-bindings
                        octets presentp max-credentials))))))

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
      (unless (eq (fnn-native-auth-adopt-config
                   service config
                   (fnn-core 'fn-native-auth-host-load-bindings
                             octets presentp max-credentials)) :accepted)
        (fnn-refuse "owner refused durable AUTHINFO account adoption"))
      ;; Publishing the file's signing/login bindings is part of the account
      ;; transaction's final configuration fence, not a second publication
      ;; after credentials have already become authoritative.
      (setq *fnn-native-auth-live-path* path
            *fnn-native-auth-live-policy* (list requiredp protected-onlyp))
      :accepted)))

(defun fnn-native-auth-startup-hook (path requiredp protected-onlyp)
  "Return a composable owner hook.  SERVICE contributes only whether a real
TLS context loaded; ACL2 still owns the authentication policy decision."
  (lambda (service)
    (fnn-native-auth-install service path requiredp protected-onlyp
                             (fnn-owner-service-tls-context service)
                             (fnn-profile-nat 'fn-store-profile-max-credentials
                                              (fnn-owner-service-store service)))))
