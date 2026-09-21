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

(defun fn-native-operator-host-result-run-tls-cert-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-tls-cert-octets result))

(defun fn-native-operator-host-result-run-tls-key-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-tls-key-octets result))

(defun fn-native-operator-host-result-run-oncep (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-oncep result))

(defun fn-native-operator-host-result-run-max-connections (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-max-connections result))

(defun fn-native-operator-host-result-run-auth-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-auth-path-octets result))

(defun fn-native-operator-host-result-run-auth-requiredp (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-auth-requiredp result))

(defun fn-native-operator-host-result-run-auth-protected-onlyp (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-auth-protected-onlyp result))

(defun fn-native-operator-host-result-run-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-control-path-octets result))

(defun fn-native-operator-host-result-run-posting-enabledp (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-posting-enabledp result))

(defun fn-native-operator-host-result-post-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-post-control-path-octets result))

(defun fn-native-operator-host-result-post-msgid-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-post-msgid-octets result))

(defun fn-native-operator-host-result-post-payload-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-post-payload-path-octets result))

(defun fn-native-operator-host-result-post-group-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-post-group-octets result))

(defun fn-native-operator-host-result-admin-plan (result)
  "Exact accepted ACL2 native-admin plan; raw Lisp may only deliver it."
  (declare (xargs :mode :program))
  (fn-native-operator-result-admin-plan result))
(defun fn-native-operator-host-result-admin-argv (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-admin-argv result))
(defun fn-native-operator-host-result-admin-control-path-octets (result)
  (declare (xargs :mode :program))
  (if (fn-native-operator-result-admin-planp result)
      (fn-record-string-octets
       (fn-native-config-control-path (fn-native-operator-result-config result)))
    nil))
