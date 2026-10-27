(in-package "ACL2")
(include-book "../books/native-hybrid-control")
(include-book "../books/definterface")
; The owner's read bound when hybrid control is loaded: an ordinary request
; under the profile's A and G, or a hybrid request (`fn-nhctrl-read-bound-for').
(include-book "../books/entries-native-hybrid-control-host")

(definterface fn-native-hybrid-control-host-read-bound
  :class ::program)

(definterface fn-native-hybrid-control-host-uint32
  :class ::program)

(definterface fn-native-hybrid-control-host-enroll-encode
  :class ::program)

(definterface fn-native-hybrid-control-host-enroll-decode
  :class ::program)

(definterface fn-native-hybrid-control-host-author-encode
  :class ::program)

(definterface fn-native-hybrid-control-host-author-decode
  :class ::program)

(definterface fn-native-hybrid-control-host-revoke-encode
  :class ::program)

(definterface fn-native-hybrid-control-host-revoke-decode
  :class ::program)

(definterface fn-native-hybrid-control-host-enroll-next-encode
  :class ::program)

(definterface fn-native-hybrid-control-host-enroll-next-decode
  :class ::program)

(definterface fn-native-hybrid-control-host-revoke-next-encode
  :class ::program)

(definterface fn-native-hybrid-control-host-revoke-next-decode
  :class ::program)

(definterface fn-native-hybrid-control-host-enroll-next-event
  :class ::program)

(definterface fn-native-hybrid-control-host-revoke-next-event
  :class ::program)
