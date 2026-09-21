; Program bridge for the native administrative plan.
(in-package "ACL2")
(include-book "../books/native-admin")

(defun fn-native-admin-host-plan (argv) (fn-native-admin-plan argv))
(defun fn-native-admin-host-status (result) (fn-native-admin-result-status result))
(defun fn-native-admin-host-reason (result) (fn-native-admin-result-reason result))
(defun fn-native-admin-host-kind (result) (fn-native-admin-result-kind result))
(defun fn-native-admin-host-name (result) (fn-native-admin-result-name result))
(defun fn-native-admin-host-capacity (result) (fn-native-admin-result-capacity result))
(defun fn-native-admin-host-config-name (generation)
  (fn-native-admin-config-name generation))
