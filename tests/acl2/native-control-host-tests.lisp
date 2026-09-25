; The host wrappers call the exact ACL2 FNCT subjects.
(in-package "ACL2")
(include-book "../../host/native-control-host")
(include-book "../../books/codec-attach")

(defconst *fn-nctrl-host-msgid*
  (fn-record-string-octets "<host-control@example.invalid>"))
(defconst *fn-nctrl-host-groups*
  (list (fn-record-string-octets "fn.test")))
(defconst *fn-nctrl-host-article* '(65 13 10))
(assert-event
 (equal (fn-native-control-host-request-decode
         (fn-native-control-host-request-encode
          *fn-nctrl-host-msgid* *fn-nctrl-host-groups*
          *fn-nctrl-host-article*))
        (list :request *fn-nctrl-host-msgid* *fn-nctrl-host-groups*
              *fn-nctrl-host-article*)))
(assert-event
 (equal (fn-native-control-host-reply-decode
         (fn-native-control-host-reply-encode :duplicate))
        :duplicate))
(assert-event (equal (fn-native-control-host-status-class :busy) :refused))
(assert-event (equal (fn-native-control-host-status-exit-code :uncertain) 3))
(assert-event
 (equal (fn-native-control-host-topic-reply-decode
         (fn-native-control-host-topic-reply-encode :replayed-historical))
        '(:topic-reply :replayed-historical)))
(assert-event
 (equal (fn-native-control-host-topic-status-exit-code
         :replayed-historical) 0))
(assert-event
 (equal (fn-native-control-host-transport-outcome :after-submission)
        :uncertain))
(assert-event
 (equal (fn-native-control-host-lease-path
         (fn-record-string-octets "/tmp/fn.sock"))
        (fn-record-string-octets "/tmp/fn.sock.lock")))
; The client reads an article up to the FNCT article width; the owner reads
; a request under the profile's bound, never below the command frame.
(assert-event (equal (fn-native-control-host-max-article)
                     *fn-record-max-payload*))
(assert-event (< (fn-native-control-host-max-article) *fn-nctrl-max-frame*))
(assert-event (equal (fn-native-control-host-max-frame)
                     *fn-nctrl-max-command-frame*))
(assert-event (equal (fn-native-control-host-read-bound 32768 1)
                     (fn-native-control-host-max-frame)))
(assert-event (< (+ 1048576 (fn-native-control-host-max-frame))
                 (fn-native-control-host-read-bound 1310720 1)))
(assert-event (equal (fn-native-control-host-max-active-clients) 16))
