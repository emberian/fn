; ACL2-facing boundary for the native AUTHINFO credential profile.
(in-package "ACL2")
(include-book "../books/native-auth-profile")
(include-book "../books/definterface")

(defun fn-native-auth-host-load (octets presentp requiredp protected-onlyp
                                        tls-availablep max-credentials)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-native-auth-load octets presentp requiredp protected-onlyp tls-availablep
                       max-credentials))

(definterface fn-native-auth-host-load
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

;; The file bound follows the store profile's max-credentials (D27, PRF-102).
(defun fn-native-auth-host-max-octets (max-credentials)
  (declare (xargs :mode :program))
  (fn-native-auth-max-octets max-credentials))

(definterface fn-native-auth-host-max-octets
  :class ::program)

(defun fn-native-auth-host-status (result)
  (declare (xargs :mode :program))
  (fn-native-auth-result-status result))

(definterface fn-native-auth-host-status
  :class ::program)

(defun fn-native-auth-host-reason (result)
  (declare (xargs :mode :program))
  (fn-native-auth-result-reason result))

(definterface fn-native-auth-host-reason
  :class ::program)

(defun fn-native-auth-host-config (result)
  (declare (xargs :mode :program))
  (fn-native-auth-result-config result))

(definterface fn-native-auth-host-config
  :class ::program)

(defun fn-native-auth-host-load-bindings (octets presentp max-credentials)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-native-auth-load-bindings octets presentp max-credentials))

(definterface fn-native-auth-host-load-bindings
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))
