; ACL2-facing wrapper for the native fn.toml profile.  The raw host calls this
; exact executable subject after it has made one bounded file read.
(in-package "ACL2")
(include-book "../books/native-config")

(defun fn-native-config-host-load (octets)
  (declare (xargs :mode :program))
  (fn-native-config-load octets))

(defun fn-native-config-host-max-octets ()
  (declare (xargs :mode :program))
  *fn-ncfg-max-octets*)

(defun fn-native-config-host-listener-address (host-octets)
  "The raw owner consumes this ACL2 projection instead of resolving HOST."
  (declare (xargs :mode :program))
  (fn-native-config-listener-address host-octets))
