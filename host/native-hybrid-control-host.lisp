(in-package "ACL2")
(include-book "../books/native-hybrid-control")
(include-book "../books/definterface")
; The owner's read bound when hybrid control is loaded: an ordinary request
; under the profile's A and G, or a hybrid request (`fn-nhctrl-read-bound-for').
(defun fn-native-hybrid-control-host-read-bound (a g)
  (declare (xargs :mode :program))
  (fn-nhctrl-read-bound-for a g))

(definterface fn-native-hybrid-control-host-read-bound
  :class ::program)
(defun fn-native-hybrid-control-host-uint32 (text)
  (declare (xargs :mode :program))
  (fn-native-hybrid-control-uint32 text))

(definterface fn-native-hybrid-control-host-uint32
  :class ::program)
(defun fn-native-hybrid-control-host-enroll-encode (g p e m)
  (declare (xargs :mode :program))
  (fn-native-hybrid-control-enroll-encode g p e m))

(definterface fn-native-hybrid-control-host-enroll-encode
  :class ::program)
(defun fn-native-hybrid-control-host-enroll-decode (x)
  (declare (xargs :mode :program))
  (fn-native-hybrid-control-enroll-decode x))

(definterface fn-native-hybrid-control-host-enroll-decode
  :class ::program)
(defun fn-native-hybrid-control-host-author-encode (g source ed ml path)
  (declare (xargs :mode :program))
  (fn-native-hybrid-control-author-encode g source ed ml path))

(definterface fn-native-hybrid-control-host-author-encode
  :class ::program)
(defun fn-native-hybrid-control-host-author-decode (x)
  (declare (xargs :mode :program))
  (fn-native-hybrid-control-author-decode x))

(definterface fn-native-hybrid-control-host-author-decode
  :class ::program)
(defun fn-native-hybrid-control-host-revoke-encode (g p)
  (declare (xargs :mode :program))
  (fn-native-hybrid-control-revoke-encode g p))

(definterface fn-native-hybrid-control-host-revoke-encode
  :class ::program)
(defun fn-native-hybrid-control-host-revoke-decode (x)
  (declare (xargs :mode :program))
  (fn-native-hybrid-control-revoke-decode x))

(definterface fn-native-hybrid-control-host-revoke-decode
  :class ::program)
(defun fn-native-hybrid-control-host-enroll-next-encode (p e m)
  (declare (xargs :mode :program))
  (fn-native-hybrid-control-enroll-next-encode p e m))

(definterface fn-native-hybrid-control-host-enroll-next-encode
  :class ::program)
(defun fn-native-hybrid-control-host-enroll-next-decode (x)
  (declare (xargs :mode :program))
  (fn-native-hybrid-control-enroll-next-decode x))

(definterface fn-native-hybrid-control-host-enroll-next-decode
  :class ::program)
(defun fn-native-hybrid-control-host-revoke-next-encode (p)
  (declare (xargs :mode :program))
  (fn-native-hybrid-control-revoke-next-encode p))

(definterface fn-native-hybrid-control-host-revoke-next-encode
  :class ::program)
(defun fn-native-hybrid-control-host-revoke-next-decode (x)
  (declare (xargs :mode :program))
  (fn-native-hybrid-control-revoke-next-decode x))

(definterface fn-native-hybrid-control-host-revoke-next-decode
  :class ::program)
(defun fn-native-hybrid-control-host-enroll-next-event (sq tx g p k snaps)
  (declare (xargs :mode :program))
  (fn-native-hybrid-control-enroll-next-event sq tx g p k snaps))

(definterface fn-native-hybrid-control-host-enroll-next-event
  :class ::program)
(defun fn-native-hybrid-control-host-revoke-next-event (sq tx g p snaps)
  (declare (xargs :mode :program))
  (fn-native-hybrid-control-revoke-next-event sq tx g p snaps))

(definterface fn-native-hybrid-control-host-revoke-next-event
  :class ::program)
