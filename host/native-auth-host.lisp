; ACL2-facing boundary for the native AUTHINFO credential profile.
(in-package "ACL2")
; D61: the image attaches these (attach-stobj) before the generic they implement;
; a certified host file carries the same order in its own world (tools/host_check.py --attach-order).
(include-book "../books/payload-arena")
(include-book "../books/native-auth-profile")
(include-book "../books/definterface")

(include-book "../books/entries-native-auth-host")

(definterface fn-native-auth-host-load
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

;; The file bound follows the store profile's max-credentials (D27, PRF-102).

(definterface fn-native-auth-host-max-octets
  :class ::program)

(definterface fn-native-auth-host-status
  :class ::program)

(definterface fn-native-auth-host-reason
  :class ::program)

(definterface fn-native-auth-host-config
  :class ::program)

(definterface fn-native-auth-host-load-bindings
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))
