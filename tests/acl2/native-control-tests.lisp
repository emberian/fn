; Reachable witnesses for the bounded FNCT local-control grammar.
(in-package "ACL2")
(include-book "../../books/native-control")
(include-book "../../books/codec-attach")

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

; The control surface has two words beyond the three outcomes, and this is
; the projection that decides what each one costs the caller.  :duplicate is
; a second submission of octets the node already holds: nothing new was
; created and nothing was refused, so it is an acceptance and exits 0.
; :busy is a refusal to act, so it exits 1.  Both words still reach the
; operator whole -- host/native/operator.lisp's fnn-operator-execute-post
; passes the status itself as the detail of fnn-operator-emit-status -- so
; `accepted operator post DUPLICATE' is not `accepted operator post
; ACCEPTED'.  The 2026-09-22 native matrix saw one submission answer with
; both words in two runs; the octets differed, not this projection
; (planning/evidence/native-duplicate-outcome-2026-09-22.md).
(assert-event (member-equal :duplicate *fn-nctrl-statuses*))
(assert-event (equal (fn-native-control-status-class :duplicate) :accepted))
(assert-event (equal (fn-native-control-status-exit-code :duplicate) 0))
(assert-event (equal (fn-native-control-status-class :busy) :refused))
(assert-event (equal (fn-native-control-status-exit-code :busy) 1))

; The word has to survive the sealed reply or the operator cannot print it.
(assert-event
 (equal (fn-native-control-reply-decode
         (fn-native-control-reply-encode :duplicate))
        :duplicate))
(assert-event
 (equal (fn-native-control-reply-decode
         (fn-native-control-reply-encode :refused))
        :refused))

; Teeth.  Exit 0 is not this function's default: it needs the status to be
; in the accepted class.  Drop that hypothesis -- ask for any other word in
; the vocabulary, or a word outside it -- and the conclusion fails.  The
; three outcomes keep three codes, and the duplicate takes the accepted
; one rather than a fourth of its own (D13).
(assert-event (equal (fn-native-control-status-exit-code :bogus) 4))
(assert-event (equal (fn-native-control-status-class :bogus) :fault))
(assert-event
 (not (equal (fn-native-control-status-exit-code :duplicate)
             (fn-native-control-status-exit-code :refused))))
(assert-event
 (not (equal (fn-native-control-status-exit-code :duplicate)
             (fn-native-control-status-exit-code :uncertain))))
(assert-event
 (not (equal (fn-native-control-status-exit-code :duplicate)
             (fn-native-control-status-exit-code :bogus))))
(assert-event
 (equal (fn-native-control-status-exit-code :duplicate)
        (fn-native-control-status-exit-code :accepted)))
(assert-event
 (not (equal (fn-native-control-status-exit-code :refused)
             (fn-native-control-status-exit-code :uncertain))))

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
(defconst *fn-nctrl-admin-tls-argv*
  (append *fn-nctrl-admin-symmetric-argv*
          (list (fn-record-string-octets "starttls")
                (fn-record-string-octets "host.example")
                (fn-record-string-octets "anchor.example"))))
(defun fn-nctrl-test-repeat-argv (count)
  (if (zp count)
      nil
    (cons (fn-record-string-octets "extra")
          (fn-nctrl-test-repeat-argv (1- count)))))
(defconst *fn-nctrl-admin-over-budget-argv*
  (fn-nctrl-test-repeat-argv (1+ *fn-native-admin-max-arguments*)))
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
 (or (< *fn-native-admin-max-arguments* (len *fn-nctrl-admin-tls-argv*))
     (equal (fn-native-control-admin-decode
             (fn-native-control-admin-encode *fn-nctrl-admin-tls-argv*))
            (list :admin *fn-nctrl-admin-tls-argv*))))
(assert-event
 (equal (fn-native-control-admin-decode
         (fn-native-control-admin-encode (list *fn-nctrl-admin-512-octets*)))
        (list :admin (list *fn-nctrl-admin-512-octets*))))
(assert-event
 (equal (fn-native-control-admin-encode
         *fn-nctrl-admin-over-budget-argv*)
        :bad))
(assert-event
 (equal (fn-native-control-admin-encode
         (list (append *fn-nctrl-admin-512-octets* '(97))))
        :bad))
(assert-event
 (equal (car (fn-native-control-admin-decode
              (fn-nctrl-seal
               *fn-nctrl-admin-kind*
               (append (fn-cbor-encode
                        (cons :uint (1+ *fn-native-admin-max-arguments*)))
                       (fn-nctrl-admin-words-encode
                        *fn-nctrl-admin-over-budget-argv*)))))
        :refused))
(assert-event
 (equal (fn-nctrl-admin-words-encode '(bad)) nil))
(assert-event
 (equal (fn-nctrl-admin-words-decode 'bad nil)
        (fn-record-parse-error :arguments)))
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
