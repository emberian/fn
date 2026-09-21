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
(assert-event (equal (fn-native-control-max-active-clients) 16))

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

(defconst *fn-nctrl-admin-argv*
  (list (fn-record-string-octets "peer")
        (fn-record-string-octets "remove")
        (fn-record-string-octets "far")))
(assert-event
 (equal (fn-native-control-admin-decode
         (fn-native-control-admin-encode *fn-nctrl-admin-argv*))
        (list :admin *fn-nctrl-admin-argv*)))
(assert-event (equal (fn-native-control-admin-encode nil) :bad))

; Admin argv is an ordered vector, so the ordinary symmetric peer plan carries
; its repeated wildmat word and the full 512-octet word budget.
(defconst *fn-nctrl-admin-symmetric-argv*
  (list (fn-record-string-octets "peer")
        (fn-record-string-octets "add")
        (fn-record-string-octets "near")
        (fn-record-string-octets "path-id")
        (fn-record-string-octets "host.example")
        (fn-record-string-octets "119")
        (fn-record-string-octets "*")
        (fn-record-string-octets "*")
        (fn-record-string-octets "198.51.100.5")
        (fn-record-string-octets "true")))
(defconst *fn-nctrl-admin-512-octets*
  (append (fn-record-string-octets
           "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
          (fn-record-string-octets
           "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
          (fn-record-string-octets
           "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
          (fn-record-string-octets
           "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
          (fn-record-string-octets
           "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
          (fn-record-string-octets
           "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
          (fn-record-string-octets
           "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
          (fn-record-string-octets
           "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")))
(assert-event
 (equal (fn-native-control-admin-decode
         (fn-native-control-admin-encode *fn-nctrl-admin-symmetric-argv*))
        (list :admin *fn-nctrl-admin-symmetric-argv*)))
(assert-event
 (equal (fn-native-control-admin-decode
         (fn-native-control-admin-encode (list *fn-nctrl-admin-512-octets*)))
        (list :admin (list *fn-nctrl-admin-512-octets*))))
(assert-event
 (equal (fn-native-control-admin-encode
         (append *fn-nctrl-admin-symmetric-argv*
                 (list (fn-record-string-octets "extra"))))
        :bad))
(assert-event
 (equal (fn-native-control-admin-encode
         (list (append *fn-nctrl-admin-512-octets* '(97))))
        :bad))
(assert-event
 (equal (car (fn-native-control-admin-decode
              (fn-nctrl-seal
               *fn-nctrl-admin-kind*
               (append (fn-cbor-encode (cons :uint 11))
                       (fn-nctrl-admin-words-encode
                        (append *fn-nctrl-admin-symmetric-argv*
                                (list (fn-record-string-octets "extra"))))))))
        :refused))
(assert-event
 (equal (car (fn-native-control-admin-decode
              (fn-nctrl-seal
               *fn-nctrl-admin-kind*
               (append (fn-cbor-encode (cons :uint 1))
                       (fn-cbor-encode (cons :bytes '(128)))))))
        :refused))
(assert-event
 (equal (car (fn-native-control-admin-decode
              (fn-nctrl-seal *fn-nctrl-admin-kind*
                              (append (fn-nctrl-admin-argv-encode
                                       *fn-nctrl-admin-argv*)
                                      '(0)))))
        :refused))
(assert-event
 (equal (car (fn-native-control-admin-decode
              (fn-nctrl-seal *fn-nctrl-admin-kind* '(1 65))))
        :refused))
