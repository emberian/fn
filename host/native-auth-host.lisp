; ACL2-facing boundary for the native AUTHINFO credential profile.
(in-package "ACL2")
(include-book "../books/native-auth-profile")

(defun fn-native-auth-host-load (octets presentp requiredp protected-onlyp
                                        tls-availablep)
  (declare (xargs :mode :program))
  (fn-native-auth-load octets presentp requiredp protected-onlyp tls-availablep))

(defun fn-native-auth-host-max-octets ()
  (declare (xargs :mode :program))
  *fn-native-auth-max-octets*)

(defun fn-native-auth-host-status (result)
  (declare (xargs :mode :program))
  (fn-native-auth-result-status result))

(defun fn-native-auth-host-reason (result)
  (declare (xargs :mode :program))
  (fn-native-auth-result-reason result))

(defun fn-native-auth-host-config (result)
  (declare (xargs :mode :program))
  (fn-native-auth-result-config result))

