; The native host wrapper calls the exact ACL2 credential-profile subject.
(in-package "ACL2")
(include-book "../../host/native-auth-host")
(include-book "../../books/codec-attach")

(defconst *fn-native-auth-host-empty*
  (fn-native-auth-host-load nil nil t nil nil))
(assert-event (equal (fn-native-auth-host-status *fn-native-auth-host-empty*)
                     :accepted))
(assert-event
 (equal (fn-native-auth-host-config *fn-native-auth-host-empty*)
        (fn-auth-make-config t nil nil nil)))
(assert-event
 (equal (fn-native-auth-host-load nil nil t t nil)
        '(:refused :protected-transport-unavailable)))
(assert-event (equal (fn-native-auth-host-max-octets) 65536))

