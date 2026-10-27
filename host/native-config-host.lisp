; ACL2-facing wrapper for the native fn.toml profile.  The raw host calls this
; exact executable subject after it has made one bounded file read.
(in-package "ACL2")
(include-book "../books/native-config")
(include-book "../books/definterface")
(include-book "../books/payload-kinds")

(include-book "../books/entries-native-config-host")

(definterface fn-native-config-host-load
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(defun fn-native-config-host-max-octets ()
  (declare (xargs :mode :program))
  *fn-ncfg-max-octets*)

(definterface fn-native-config-host-max-octets
  :class ::program)

(definterface fn-native-config-host-listener-addresses
  :class ::program
  :kinds ((host-octets fn-cbor-octet-listp)))

;; test-only (tools/host_callers.py): tests/acl2/native-config-tests.lisp
