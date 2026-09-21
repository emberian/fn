; The host wrapper calls the exact ACL2 operator subject.
(in-package "ACL2")
(include-book "../../host/native-operator-host")

(defconst *fn-nop-host-config*
  (append (fn-record-string-octets "[store]") (list 10)
          (fn-record-string-octets "path = \"/srv/fn\"") (list 10)))
(defconst *fn-nop-host-status-argv*
  (list (fn-record-string-octets "status")))
(defconst *fn-nop-host-result*
  (fn-native-operator-host-run *fn-nop-host-config* *fn-nop-host-status-argv*))
(assert-event (equal (fn-native-operator-result-status *fn-nop-host-result*) :accepted))
(assert-event (equal (fn-native-operator-result-command *fn-nop-host-result*) "status"))
(assert-event (equal (fn-native-operator-host-argv-max-arguments) 32))
(assert-event (equal (fn-native-operator-host-argv-max-octets) 512))
(assert-event (equal (fn-native-operator-host-result-native-action *fn-nop-host-result*)
                     :status))
(assert-event (equal (fn-native-operator-host-result-exit-code *fn-nop-host-result*) 0))
(assert-event (equal (fn-native-operator-host-result-config *fn-nop-host-result*)
                     (fn-native-operator-result-config *fn-nop-host-result*)))
(assert-event (equal (fn-native-operator-host-result-arguments *fn-nop-host-result*)
                     '(:status)))
