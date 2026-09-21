; Reachable witnesses for the bounded FNCT local-control grammar.
(in-package "ACL2")
(include-book "../../books/native-control")

(defconst *fn-nctrl-test-msgid*
  (fn-record-string-octets "<control-1@example.invalid>"))
(defconst *fn-nctrl-test-groups*
  (list (fn-record-string-octets "fn.letters")
        (fn-record-string-octets "fn.local")))
(defconst *fn-nctrl-test-article*
  (fn-record-string-octets
   "From: author@example.invalid\r\nSubject: exact\r\n\r\nbody\r\n"))
; A defconst cannot call an attached function (:DOC ignored-attachment).
; Assertions evaluate the ground encoder with fn-frame-digest's attachment.
(assert-event
 (fn-cbor-octet-listp
  (fn-native-control-request-encode
   *fn-nctrl-test-msgid* *fn-nctrl-test-groups* *fn-nctrl-test-article*)))
(assert-event
 (<= (len (fn-native-control-request-encode
            *fn-nctrl-test-msgid* *fn-nctrl-test-groups*
            *fn-nctrl-test-article*))
     *fn-nctrl-max-frame*))
(assert-event
 (equal (fn-native-control-request-decode
         (fn-native-control-request-encode
          *fn-nctrl-test-msgid* *fn-nctrl-test-groups*
          *fn-nctrl-test-article*))
        (list :request *fn-nctrl-test-msgid* *fn-nctrl-test-groups*
              *fn-nctrl-test-article*)))

; A byte change and a missing required group are both rejected.
(assert-event
 (equal (car (fn-native-control-request-decode
              (cons 0
                    (cdr (fn-native-control-request-encode
                          *fn-nctrl-test-msgid* *fn-nctrl-test-groups*
                          *fn-nctrl-test-article*)))))
        :refused))
(assert-event
 (equal (fn-native-control-request-encode
         *fn-nctrl-test-msgid* nil *fn-nctrl-test-article*)
        :bad))

(assert-event
 (equal (fn-native-control-reply-decode
         (fn-native-control-reply-encode :accepted))
        :accepted))
(assert-event
 (equal (fn-native-control-reply-decode
         (fn-native-control-reply-encode :uncertain))
        :uncertain))
(assert-event (equal (fn-native-control-status-exit-code :accepted) 0))
(assert-event (equal (fn-native-control-status-exit-code :refused) 1))
(assert-event (equal (fn-native-control-status-exit-code :uncertain) 3))
(assert-event (equal (fn-native-control-status-exit-code :fault) 4))

(assert-event
 (equal (fn-native-control-lease-path
         (fn-record-string-octets "/run/fn/control.sock"))
        (fn-record-string-octets "/run/fn/control.sock.lock")))
(assert-event
 (equal (fn-native-control-lease-path nil) :bad))

; Losing the connection after a complete handoff cannot be called refusal.
(assert-event
 (equal (fn-native-control-transport-outcome :before-submission) :refused))
(assert-event
 (equal (fn-native-control-transport-outcome :after-submission) :uncertain))
