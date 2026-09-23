(in-package "ACL2")
(include-book "../../books/consumer-local-control")

(defconst *ncl-id* '(7))
(defconst *ncl-cli-id* '(99)) ; c, printable CLI ID
(defconst *ncl-group* '(102 110 46 116 101 115 116))
(defconst *ncl-cursor*
  (fn-cp-cursor '(1) '(2) *ncl-id* '(108 111 99 97 108)
                *ncl-group* 1 0 1 2))
(defconst *ncl-token* (fn-cp-cursor-encode *ncl-cursor*))
(assert-event (<= *fn-ncl-poll-max-payload* *fn-frame-max-payload*))
(assert-event
 (equal (fn-ncl-request-decode (fn-ncl-request-encode :bootstrap nil nil))
        '(:consumer :bootstrap nil nil)))
(assert-event
 (equal (fn-ncl-request-decode
         (fn-ncl-request-encode :poll *ncl-id* nil))
        (list :consumer :poll *ncl-id* nil)))
(assert-event
 (equal (fn-ncl-cli-plan '(98 111 111 116 115 116 114 97 112)
                         (list '(47 116 109 112 47 99)))
        '(:run :bootstrap (47 116 109 112 47 99) nil nil nil)))
(assert-event
 (equal (fn-ncl-request-decode
         (fn-ncl-request-encode :register *ncl-id* *ncl-group*))
        (list :consumer :register *ncl-id* *ncl-group*)))
(assert-event
 (equal (fn-ncl-request-decode
         (fn-ncl-request-encode :ack *ncl-token* nil))
        (list :consumer :ack *ncl-token* nil)))
(assert-event
 (equal (fn-ncl-request-decode
         (fn-ncl-request-encode :position *ncl-id* nil))
        (list :consumer :position *ncl-id* nil)))
(assert-event
 (equal (fn-ncl-reply-decode
         (fn-ncl-reply-encode :accepted *ncl-token*))
        (list :consumer-reply :accepted *ncl-token*)))
(defconst *ncl-report*
  (fn-record-encode-impl
   (fn-record-make 0 0 0 "<poll@fn.test>" '(65) '("fn.test")
                   "poll-pin" "poll-content" "poll-release" 1 841000000)))
(assert-event
 (equal (fn-ncl-poll-reply-decode
         (fn-ncl-poll-reply-encode :accepted *ncl-token* *ncl-report*))
        (list :consumer-poll-reply :accepted *ncl-token* *ncl-report*)))
(assert-event
 (equal (fn-ncl-poll-reply-decode
         (fn-ncl-poll-reply-encode :accepted *ncl-token* nil))
        (list :consumer-poll-reply :accepted *ncl-token* nil)))
(assert-event
 (equal (fn-ncl-reply-decode (fn-ncl-reply-encode :uncertain nil))
        '(:consumer-reply :uncertain nil)))
(assert-event (equal (fn-ncl-request-encode :ack '(1 2 3) nil) :bad))
(assert-event
 (equal (fn-ncl-request-decode
         (fn-nctrl-seal *fn-ncl-request-kind* '(255)))
        '(:refused :kind)))
(assert-event (equal (fn-ncl-reply-encode :refused *ncl-token*) :bad))
(assert-event
 (equal (fn-ncl-cli-plan '(114 101 103 105 115 116 101 114)
                        (list '(47 116 109 112 47 99)
                              *ncl-cli-id* *ncl-group* '(47 116 109 112 47 116)))
        (list :run :register '(47 116 109 112 47 99)
              *ncl-cli-id* *ncl-group* '(47 116 109 112 47 116))))
(assert-event
 (equal (fn-ncl-cli-plan '(97 99 107)
                        (list '(47 116 109 112 47 99) '(47 116 109 112 47 116)))
        '(:run :ack (47 116 109 112 47 99) (47 116 109 112 47 116) nil nil)))
(assert-event
 (equal (fn-ncl-cli-plan '(97 99 107)
                        (list '(116 109 112 47 99) '(47 116 109 112 47 116)))
        '(:usage :control-path)))
(assert-event
 (equal (fn-ncl-cli-plan '(112 111 108 108)
                         (list '(47 116 109 112 47 99) *ncl-cli-id*
                               '(47 116 109 112 47 99 117)
                               '(47 116 109 112 47 114)))
        '(:run :poll (47 116 109 112 47 99) (99)
               (47 116 109 112 47 99 117)
               (47 116 109 112 47 114))))
