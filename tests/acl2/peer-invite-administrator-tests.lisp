; The external administrator cannot manufacture internal acceptance deltas.
(in-package "ACL2")
(include-book "../../books/native-admin")
(assert-event
 (let ((plan (fn-native-admin-plan
              (list (fn-record-string-octets "peer")
                    (fn-record-string-octets "accept-peer")
                    (fn-record-string-octets "a.example")))))
   (and (equal (fn-native-admin-result-status plan) :refused)
        (not (equal (fn-native-admin-result-kind plan) :accept-peer)))))
; The ordinary public removal grammar remains accepted.
(assert-event
 (let ((plan (fn-native-admin-plan
              (list (fn-record-string-octets "peer")
                    (fn-record-string-octets "remove")
                    (fn-record-string-octets "a.example")))))
   (and (equal (fn-native-admin-result-status plan) :accepted)
        (equal (fn-native-admin-result-kind plan) :remove-peer))))
