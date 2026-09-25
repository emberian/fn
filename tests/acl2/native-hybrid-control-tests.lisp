(in-package "ACL2")
(include-book "../../books/native-hybrid-control")
(include-book "std/testing/assert-equal" :dir :system)
(include-book "../../books/codec-attach")

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
   7 '(65 13 10) *nhc-ed-signature* *nhc-ml-signature*
   (fn-record-string-octets "/tmp/ml-public.pem")))
 (list :hybrid-author 7 '(65 13 10) *nhc-ed-signature* *nhc-ml-signature*
       (fn-record-string-octets "/tmp/ml-public.pem")))

(assert-equal
 (fn-native-hybrid-control-enroll-encode
  7 '(1) *nhc-ed-key* *nhc-ml-key*)
 :bad)

(assert-equal
 (fn-native-hybrid-control-revoke-decode
  (fn-native-hybrid-control-revoke-encode 8 *nhc-principal*))
 (list :hybrid-revoke 8 *nhc-principal*))

(assert-equal
 (fn-native-hybrid-control-revoke-encode 8 '(1)) :bad)

(assert-equal
 (fn-native-hybrid-control-enroll-decode
  (fn-native-hybrid-control-revoke-encode 8 *nhc-principal*))
 nil)

; D27 (PRF-091): the hybrid payload cap is the author spec's width at the v1
; source ceiling.  A 65 535-octet source, refused before by the fixed 65 536
; payload cap, now round-trips; one octet more is past the v1 carrier.
(defconst *nhc-v1-source* (make-list 65535 :initial-element 65))
(assert-equal
 (fn-native-hybrid-control-author-decode
  (fn-native-hybrid-control-author-encode
   7 *nhc-v1-source* *nhc-ed-signature* *nhc-ml-signature*
   (fn-record-string-octets "/tmp/ml-public.pem")))
 (list :hybrid-author 7 *nhc-v1-source* *nhc-ed-signature* *nhc-ml-signature*
       (fn-record-string-octets "/tmp/ml-public.pem")))
(assert-equal
 (fn-native-hybrid-control-author-encode
  7 (cons 65 *nhc-v1-source*) *nhc-ed-signature* *nhc-ml-signature*
  (fn-record-string-octets "/tmp/ml-public.pem"))
 :bad)
(assert-event (< 65536 *fn-nhctrl-max-payload*))
; The hybrid read bound never falls below the ordinary one.
(assert-event (equal (fn-nhctrl-read-bound-for 1048576 4)
                     (fn-nctrl-read-bound-for 1048576 4)))
; Every hybrid frame is within the command-frame floor of the ordinary bound.
(assert-event (<= (+ *fn-frame-overhead-octets* *fn-nhctrl-max-payload*)
                  *fn-nctrl-max-command-frame*))
