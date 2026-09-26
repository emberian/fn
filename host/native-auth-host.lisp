; ACL2-facing boundary for the native AUTHINFO credential profile.
(in-package "ACL2")
(include-book "../books/native-auth-profile")

(defun fn-native-auth-host-load (octets presentp requiredp protected-onlyp
                                        tls-availablep max-credentials)
  (declare (xargs :mode :program))
  (fn-native-auth-load octets presentp requiredp protected-onlyp tls-availablep
                       max-credentials))

;; The file bound follows the store profile's max-credentials (D27, PRF-102).
(defun fn-native-auth-host-max-octets (max-credentials)
  (declare (xargs :mode :program))
  (fn-native-auth-max-octets max-credentials))

(defun fn-native-auth-host-status (result)
  (declare (xargs :mode :program))
  (fn-native-auth-result-status result))

(defun fn-native-auth-host-reason (result)
  (declare (xargs :mode :program))
  (fn-native-auth-result-reason result))

(defun fn-native-auth-host-config (result)
  (declare (xargs :mode :program))
  (fn-native-auth-result-config result))

(defun fn-native-auth-host-load-bindings (octets presentp max-credentials)
  (declare (xargs :mode :program))
  (fn-native-auth-load-bindings octets presentp max-credentials))

;; PKT-221: the credential file's login bindings against the running owner's
;; live configuration (books/login-binding-live.lisp fn-lb-sync-plan):
;; (:ok RECORDS), each a delta list the host stages and publishes through
;; fnn-owner-live-reconfigure-locked in order, or (:refused REASON).  The
;; file is the one fn-native-auth-host-load accepted under the same bound.
(defun fn-native-auth-host-bindings-plan (octets presentp max-credentials state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-lb-sync-plan
          (fn-native-auth-load-bindings octets presentp max-credentials)
          (fn-cfg-value (fn-ocfg-config (fn-owner-ocfg state))))))
