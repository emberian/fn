; The native host wrapper calls the exact ACL2 credential-profile subject.
(in-package "ACL2")
(include-book "../../host/native-auth-host")
(include-book "../../books/codec-attach")

(defconst *fn-native-auth-host-empty*
  (fn-native-auth-host-load nil nil t nil nil 128))
(assert-event (equal (fn-native-auth-host-status *fn-native-auth-host-empty*)
                     :accepted))
(assert-event
 (equal (fn-native-auth-host-config *fn-native-auth-host-empty*)
        (fn-auth-make-config t nil nil nil)))
(assert-event
 (equal (fn-native-auth-host-load nil nil t t nil 128)
        '(:refused :protected-transport-unavailable)))
; The file bound follows the profile's max-credentials: 512 octets per
; credential plus one unit for the writer's header (D27, PRF-102).
(assert-event (equal (fn-native-auth-host-max-octets 128) 66048))
(assert-event (equal (fn-native-auth-host-max-octets 1048576) 536871424))

