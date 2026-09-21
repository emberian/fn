; Teeth for the bounded native operator grammar and its config gate.
(in-package "ACL2")
(include-book "../../books/native-operator")

(defun fn-nop-test-argv (words)
  (if (consp words)
      (cons (fn-record-string-octets (car words))
            (fn-nop-test-argv (cdr words)))
    nil))

(defun fn-nop-test-lines (lines)
  (if (consp lines)
      (append (fn-record-string-octets (car lines)) (list 10)
              (fn-nop-test-lines (cdr lines)))
    nil))

(defconst *fn-nop-minimal-config*
  (fn-nop-test-lines '("[store]" "path = \"/srv/fn\"")))
(defconst *fn-nop-run*
  (fn-native-operator-run *fn-nop-minimal-config*
                          (fn-nop-test-argv '("run" "--once"))))
(assert-event (equal (fn-native-operator-result-status *fn-nop-run*) :accepted))
(assert-event (equal (fn-native-operator-result-command *fn-nop-run*) "run"))
(assert-event (equal (fn-native-operator-result-arguments *fn-nop-run*)
                     '(:run :once t)))
(assert-event (equal (fn-native-operator-exit-code *fn-nop-run*) 0))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("status"))))
                     :accepted))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("recover"))))
                     :accepted))

; Help is a config-free ACL2 action, including an absent/broken configuration.
(defconst *fn-nop-help-without-config*
  (fn-native-operator-run nil (fn-nop-test-argv '("help" "run"))))
(assert-event (equal (fn-native-operator-result-status *fn-nop-help-without-config*) :accepted))
(assert-event (equal (fn-native-operator-result-arguments *fn-nop-help-without-config*)
                     '(:help "run" "usage: fn operator CONFIG run [--once]")))
(assert-event (equal (fn-native-operator-result-native-action *fn-nop-help-without-config*)
                     :help))

(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run
                       *fn-nop-minimal-config*
                       (fn-nop-test-argv '("post" "--message-id" "<one@example.invalid>"
                                           "--payload" "/tmp/one.eml" "--group" "fn.letters"))))
                     :usage))

; Command teeth: repeated/conflicting runtime options and unsupported verbs lose a plan.
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("run" "--once" "--once"))))
                     :usage))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("status" "typo"))))
                     :usage))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("group" "create" "fn.letters"))))
                     :usage))

; Native-config owns type/range/repetition refusal before a command plan.
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run
                       (fn-nop-test-lines '("[store]" "path = \"/srv/fn\"" "[listener]" "port = \"1119\""))
                       (fn-nop-test-argv '("status"))))
                     :usage))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run
                       (fn-nop-test-lines '("[store]" "path = \"/srv/fn\"" "[listener]" "port = 70000"))
                       (fn-nop-test-argv '("status"))))
                     :usage))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run
                       (fn-nop-test-lines '("[store]" "path = \"/srv/fn\"" "[acl2]" "slots = \"4\""))
                       (fn-nop-test-argv '("status"))))
                     :usage))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run
                       (fn-nop-test-lines '("[store]" "path = \"/srv/fn\"" "[listener]" "port = 1119" "port = 1119"))
                       (fn-nop-test-argv '("status"))))
                     :usage))

; A parsed disabled posting profile is explicit unsupported usage until the
; owner consumes one ACL2 posting projection for served and control paths.
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run
                       (fn-nop-test-lines '("[store]" "path = \"/srv/fn\"" "[posting]" "enabled = false"))
                       (fn-nop-test-argv '("run"))))
                     :usage))

(assert-event (equal (fn-native-operator-exit-code
                      (fn-native-operator-run
                       (fn-nop-test-lines '("[store]" "path = \"/srv/fn\"" "[listener]" "port = \"1119\""))
                       (fn-nop-test-argv '("status"))))
                     5))

; Help bypasses the config gate even for malformed octets; non-help does not.
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run '(999)
                                              (fn-nop-test-argv '("help"))))
                     :accepted))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run '(999)
                                              (fn-nop-test-argv '("status"))))
                     :usage))

; Preflight is the sole config-read decision: help stays config-free, while
; valid non-help commands request configuration and malformed argv wins first.
(assert-event (equal (fn-native-operator-command-preflight
                      (fn-nop-test-argv '("help" "status")))
                     '(:accepted :plan "help" nil
                       (:help "status" "usage: fn operator CONFIG status"))))
(assert-event (fn-native-operator-preflight-needs-config-p
               (fn-native-operator-command-preflight
                (fn-nop-test-argv '("status")))))
(assert-event (equal (fn-native-operator-result-reason
                      (fn-native-operator-command-preflight '(999)))
                     :argv-bounds))
(assert-event (equal (fn-native-operator-result-reason
                      (fn-native-operator-run '(999) '(999)))
                     :argv-bounds))
