; ACL2-facing native operator boundary.
;
; The raw image is allowed to make bounded file/argv byte vectors and emit the
; returned tagged result.  It does not parse a command, choose defaults, or
; assign an exit code: fn-native-operator-run owns all three.
(in-package "ACL2")
(include-book "../books/native-operator")

(defun fn-native-operator-host-run (config-octets argv-octets)
  (declare (xargs :mode :program))
  (fn-native-operator-run config-octets argv-octets))

(defun fn-native-operator-host-argv-max-arguments ()
  (declare (xargs :mode :program))
  *fn-nop-max-arguments*)

(defun fn-native-operator-host-argv-max-octets ()
  (declare (xargs :mode :program))
  *fn-nop-max-argument-octets*)
