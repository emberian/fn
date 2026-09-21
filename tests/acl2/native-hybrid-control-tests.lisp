(in-package "ACL2")
(include-book "../../books/native-hybrid-control")
(include-book "std/testing/assert-equal" :dir :system)

(defconst *nhc-principal* (make-list 32 :initial-element 1))
(defconst *nhc-ed-key* (make-list 32 :initial-element 2))
(defconst *nhc-ml-key* (make-list 1952 :initial-element 3))
(defconst *nhc-ed-signature* (make-list 64 :initial-element 4))
(defconst *nhc-ml-signature* (make-list 3309 :initial-element 5))

(assert-equal
 (fn-native-hybrid-control-enroll-decode
  (fn-native-hybrid-control-enroll-encode
   7 *nhc-principal* *nhc-ed-key* *nhc-ml-key*))
 (list :hybrid-enroll 7 *nhc-principal* *nhc-ed-key* *nhc-ml-key*))

(assert-equal
 (fn-native-hybrid-control-author-decode
  (fn-native-hybrid-control-author-encode
   7 (fn-record-string-octets "<hybrid@example.invalid>") '(65 13 10)
   *nhc-ed-signature* *nhc-ml-signature*
   (fn-record-string-octets "/tmp/ml-public.pem")
   (list (fn-record-string-octets "example"))
   (fn-record-string-octets "obligation")
   (fn-record-string-octets "subject")
   (fn-record-string-octets "release") 3))
 (list :hybrid-author 7
       (fn-record-string-octets "<hybrid@example.invalid>") '(65 13 10)
       *nhc-ed-signature* *nhc-ml-signature*
       (fn-record-string-octets "/tmp/ml-public.pem")
       (list (fn-record-string-octets "example"))
       (fn-record-string-octets "obligation")
       (fn-record-string-octets "subject")
       (fn-record-string-octets "release") 3))

(assert-equal
 (fn-native-hybrid-control-enroll-encode
  7 '(1) *nhc-ed-key* *nhc-ml-key*)
 :bad)
