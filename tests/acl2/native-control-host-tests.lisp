; The host wrappers call the exact ACL2 FNCT subjects.
(in-package "ACL2")
(include-book "../../host/native-control-host")

(defconst *fn-nctrl-host-msgid*
  (fn-record-string-octets "<host-control@example.invalid>"))
(defconst *fn-nctrl-host-groups*
  (list (fn-record-string-octets "fn.test")))
(defconst *fn-nctrl-host-article* '(65 13 10))
(defconst *fn-nctrl-host-request*
  (fn-native-control-host-request-encode
   *fn-nctrl-host-msgid* *fn-nctrl-host-groups* *fn-nctrl-host-article*))

(assert-event
 (equal (fn-native-control-host-request-decode *fn-nctrl-host-request*)
        (list :request *fn-nctrl-host-msgid* *fn-nctrl-host-groups*
              *fn-nctrl-host-article*)))
(assert-event
 (equal (fn-native-control-host-reply-decode
         (fn-native-control-host-reply-encode :duplicate))
        :duplicate))
(assert-event (equal (fn-native-control-host-status-class :busy) :refused))
(assert-event (equal (fn-native-control-host-status-exit-code :uncertain) 3))
(assert-event
 (equal (fn-native-control-host-transport-outcome :after-submission)
        :uncertain))
(assert-event (< (fn-native-control-host-max-article)
                 (fn-native-control-host-max-frame)))
