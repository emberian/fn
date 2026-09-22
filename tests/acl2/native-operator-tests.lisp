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

; TLS paths are now an executable native run profile.  ACL2 projects the
; exact paths; protected-only remains unavailable without such a pair.
(defconst *fn-nop-tls-run*
  (fn-native-operator-run
   (fn-nop-test-lines '("[store]" "path = \"/srv/fn\""
                        "[listener]" "tls_cert = \"/etc/fn/cert.pem\""
                        "tls_key = \"/etc/fn/key.pem\""
                        "[auth]" "protected_only = true"))
   (fn-nop-test-argv '("run" "--once"))))
(assert-event
 (equal (fn-native-operator-result-status *fn-nop-tls-run*) :accepted))
(assert-event
 (equal (fn-native-operator-result-run-tls-cert-octets *fn-nop-tls-run*)
        (fn-record-string-octets "/etc/fn/cert.pem")))
(assert-event
 (equal (fn-native-operator-result-run-tls-key-octets *fn-nop-tls-run*)
        (fn-record-string-octets "/etc/fn/key.pem")))
(assert-event
 (equal
  (fn-native-operator-result-status
   (fn-native-operator-run
    (fn-nop-test-lines '("[store]" "path = \"/srv/fn\""
                         "[auth]" "protected_only = true"))
    (fn-nop-test-argv '("run"))))
  :usage))

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
                     :accepted))

(defconst *fn-nop-post*
  (fn-native-operator-run
   *fn-nop-minimal-config*
   (fn-nop-test-argv '("post" "--message-id" "<one@example.invalid>"
                       "--payload" "/tmp/one.eml" "--group" "fn.letters"))))
(assert-event (equal (fn-native-operator-result-native-action *fn-nop-post*) :post))
(assert-event
 (equal (fn-native-operator-result-post-msgid-octets *fn-nop-post*)
        (fn-record-string-octets "<one@example.invalid>")))
(assert-event
 (equal (fn-native-operator-result-post-group-octets *fn-nop-post*)
        (list (fn-record-string-octets "fn.letters"))))

; Command teeth: repeated/conflicting runtime options and unsupported verbs lose a plan.
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("run" "--once" "--once"))))
                     :usage))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("status" "typo"))))
                     :usage))
(defconst *fn-nop-group-create*
  (fn-native-operator-run *fn-nop-minimal-config*
                          (fn-nop-test-argv '("group" "create" "fn.letters"))))
(assert-event (equal (fn-native-operator-result-status *fn-nop-group-create*) :accepted))
(assert-event (equal (fn-native-operator-result-native-action *fn-nop-group-create*) :admin))
(assert-event (equal (fn-native-admin-result-kind
                      (fn-native-operator-result-admin-plan *fn-nop-group-create*))
                     :create-group))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("group" "retire" "fn.letters"))))
                     :accepted))
(assert-event (equal (fn-native-admin-result-capacity
                      (fn-native-operator-result-admin-plan
                       (fn-native-operator-run *fn-nop-minimal-config*
                                               (fn-nop-test-argv '("capacity" "1048576")))))
                     1048576))
(assert-event (equal (fn-native-operator-exit-code
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("capacity" "01"))))
                     5))

(defconst *fn-nop-principal-list*
  (fn-native-operator-run *fn-nop-minimal-config*
                          (fn-nop-test-argv '("principal" "list"))))
(assert-event
 (equal (fn-native-operator-result-native-action *fn-nop-principal-list*)
        :principal))
(assert-event
 (equal (fn-native-auth-admin-action-kind
         (fn-native-operator-result-principal-plan *fn-nop-principal-list*))
        :list))
(assert-event
 (equal (fn-native-operator-result-principal-auth-path-octets
         *fn-nop-principal-list*)
        (fn-record-string-octets "/srv/fn/auth.toml")))
(assert-event
 (equal (fn-native-operator-result-status
         (fn-native-operator-run *fn-nop-minimal-config*
                                 (fn-nop-test-argv '("principal" "set-password"))))
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

; A valid config can be unsupported for the running owner while still
; allowing offline store administration.  Only RUN checks owner availability.
(defconst *fn-nop-full-unavailable-config*
  (fn-nop-test-lines '("[store]" "path = \"/srv/fn\""
                       "[listener]" "tls_cert = \"/etc/fn/cert.pem\"" "tls_key = \"/etc/fn/key.pem\""
                       "[auth]" "required = true" "protected_only = true"
                       "[posting]" "enabled = false")))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run *fn-nop-full-unavailable-config*
                                              (fn-nop-test-argv '("group" "create" "fn.offline"))))
                     :accepted))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run *fn-nop-full-unavailable-config*
                                              (fn-nop-test-argv '("status"))))
                     :accepted))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run *fn-nop-full-unavailable-config*
                                              (fn-nop-test-argv '("recover"))))
                     :accepted))
(assert-event (equal (fn-native-operator-result-reason
                      (fn-native-operator-run *fn-nop-full-unavailable-config*
                                              (fn-nop-test-argv '("run"))))
                     :unsupported-profile))

; The service may run with posting disabled, but POST is an explicit refusal.
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run
                       (fn-nop-test-lines '("[store]" "path = \"/srv/fn\"" "[posting]" "enabled = false"))
                       (fn-nop-test-argv '("run"))))
                     :accepted))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run
                       (fn-nop-test-lines '("[store]" "path = \"/srv/fn\""
                                            "[posting]" "enabled = false"))
                       (fn-nop-test-argv
                        '("post" "--message-id" "<one@example.invalid>"
                          "--payload" "/tmp/one.eml" "--group" "fn.letters"))))
                     :refused))

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

; `policy set path-identity' reaches the administrative plan through the
; public operator, and its help subject exists.
(defconst *fn-nop-policy*
  (fn-native-operator-run *fn-nop-minimal-config*
                          (fn-nop-test-argv '("policy" "set" "path-identity"
                                              "a.gate.example.invalid"))))
(assert-event (equal (fn-native-operator-result-status *fn-nop-policy*) :accepted))
(assert-event (equal (fn-native-operator-result-native-action *fn-nop-policy*) :admin))
(assert-event (equal (fn-native-admin-result-kind
                      (fn-native-operator-result-admin-plan *fn-nop-policy*))
                     :set-policy))
(assert-event (equal (fn-native-admin-result-value
                      (fn-native-operator-result-admin-plan *fn-nop-policy*))
                     (fn-record-string-octets "a.gate.example.invalid")))
(assert-event (equal (fn-native-operator-exit-code
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("policy" "get" "path-identity"))))
                     5))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run '(999)
                                              (fn-nop-test-argv '("help" "policy"))))
                     :accepted))
