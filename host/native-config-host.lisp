; ACL2-facing wrapper for the native fn.toml profile.  The raw host calls this
; exact executable subject after it has made one bounded file read.
(in-package "ACL2")
(include-book "../books/native-config")
(include-book "../books/definterface")
(include-book "../books/payload-kinds")

(defun fn-native-config-host-load (octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp octets)))
  (fn-native-config-load octets))

(definterface fn-native-config-host-load
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(defun fn-native-config-host-max-octets ()
  (declare (xargs :mode :program))
  *fn-ncfg-max-octets*)

(definterface fn-native-config-host-max-octets
  :class ::program)

(defun fn-native-config-host-listener-addresses (host-octets)
  "NNT-041: every (FAMILY ADDRESS) the owner binds, in the written order."
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp host-octets)))
  (fn-native-config-listener-addresses host-octets))

(definterface fn-native-config-host-listener-addresses
  :class ::program
  :kinds ((host-octets fn-cbor-octet-listp)))

;; test-only (tools/host_callers.py): tests/acl2/native-config-tests.lisp
(defun fn-native-config-host-listener-address (host-octets)
  "The raw owner consumes this ACL2 projection instead of resolving HOST."
  (declare (xargs :mode :program))
  (fn-native-config-listener-address host-octets))
