; ACL2-facing native operator boundary.
;
; The raw image is allowed to make bounded file/argv byte vectors and emit the
; returned tagged result.  It does not parse a command, choose defaults, or
; assign an exit code: fn-native-operator-run owns all three.
(in-package "ACL2")
(include-book "../books/native-operator")

(defun fn-native-operator-host-preflight (argv-octets)
  (declare (xargs :mode :program))
  (fn-native-operator-command-preflight argv-octets))

(defun fn-native-operator-host-preflight-needs-config-p (result)
  (declare (xargs :mode :program))
  (fn-native-operator-preflight-needs-config-p result))

(defun fn-native-operator-host-run (config-octets argv-octets)
  (declare (xargs :mode :program))
  (fn-native-operator-run config-octets argv-octets))

(defun fn-native-operator-host-argv-max-arguments ()
  (declare (xargs :mode :program))
  *fn-nop-max-arguments*)

(defun fn-native-operator-host-argv-max-octets ()
  (declare (xargs :mode :program))
  *fn-nop-max-argument-octets*)

(defun fn-native-operator-host-result-status (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-status result))

(defun fn-native-operator-host-result-reason (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-reason result))

(defun fn-native-operator-host-result-command (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-command result))

(defun fn-native-operator-host-result-exit-code (result)
  (declare (xargs :mode :program))
  (fn-native-operator-exit-code result))

(defun fn-native-operator-host-result-native-action (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-native-action result))

(defun fn-native-operator-host-result-store-root (result)
  (declare (xargs :mode :program))
  (fn-native-config-store (fn-native-operator-result-config result)))

(defun fn-native-operator-host-result-config (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-config result))

(defun fn-native-operator-host-result-arguments (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-arguments result))


(defun fn-native-operator-host-result-run-store-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-store-octets result))

(defun fn-native-operator-host-result-run-listener-host-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-listener-host-octets result))

(defun fn-native-operator-host-result-run-listener-port (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-listener-port result))

(defun fn-native-operator-host-result-run-oncep (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-oncep result))

(defun fn-native-operator-host-result-run-max-connections (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-max-connections result))
