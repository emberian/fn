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

; Offline store administration does not consult owner availability; only RUN
; does.  The full protected profile below carries the paired TLS paths, so
; since 9223873c (`adopt STARTTLS in native owner') the saved image CAN
; consume it and RUN is an accepted plan: the assertion here expected
; :unsupported-profile and was written against the availability rule that
; commit replaced, in the same book whose TLS block above already says so.
; The claim it was written for -- protected-only credentials with no TLS
; context are not a runnable profile -- is asserted below of
; `fn-native-config-operator-availablep', the function that decides it, and
; of the composed run.
(defconst *fn-nop-full-protected-config*
  (fn-nop-test-lines '("[store]" "path = \"/srv/fn\""
                       "[listener]" "tls_cert = \"/etc/fn/cert.pem\"" "tls_key = \"/etc/fn/key.pem\""
                       "[auth]" "required = true" "protected_only = true"
                       "[posting]" "enabled = false")))
(defconst *fn-nop-protected-without-tls-config*
  (fn-nop-test-lines '("[store]" "path = \"/srv/fn\""
                       "[auth]" "required = true" "protected_only = true"
                       "[posting]" "enabled = false")))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run *fn-nop-full-protected-config*
                                              (fn-nop-test-argv '("group" "create" "fn.offline"))))
                     :accepted))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run *fn-nop-full-protected-config*
                                              (fn-nop-test-argv '("status"))))
                     :accepted))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run *fn-nop-full-protected-config*
                                              (fn-nop-test-argv '("recover"))))
                     :accepted))
; The deciding function, on both profiles.
(assert-event (fn-native-config-operator-availablep
               (fn-ncfg-second
                (fn-native-config-load *fn-nop-full-protected-config*))))
(assert-event (not (fn-native-config-operator-availablep
                    (fn-ncfg-second
                     (fn-native-config-load
                      *fn-nop-protected-without-tls-config*)))))
; And the composed run, which reads that decision.
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run *fn-nop-full-protected-config*
                                              (fn-nop-test-argv '("run"))))
                     :accepted))
(assert-event (equal (fn-native-operator-result-reason
                      (fn-native-operator-run *fn-nop-full-protected-config*
                                              (fn-nop-test-argv '("run"))))
                     :plan))
(assert-event (equal (fn-native-operator-result-reason
                      (fn-native-operator-run
                       *fn-nop-protected-without-tls-config*
                       (fn-nop-test-argv '("run"))))
                     '(:unsupported-profile "protected_only")))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run
                       *fn-nop-protected-without-tls-config*
                       (fn-nop-test-argv '("run"))))
                     :usage))

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

; -----------------------------------------------------------------------------
; `init': the node stood up through the operator, with one binary.

(defconst *fn-nop-init*
  (fn-native-operator-run *fn-nop-minimal-config*
                          (fn-nop-test-argv '("init" "fn.letters" "fn.test"))))
(assert-event (equal (fn-native-operator-result-status *fn-nop-init*) :accepted))
(assert-event (equal (fn-native-operator-result-command *fn-nop-init*) "init"))
(assert-event (equal (fn-native-operator-result-native-action *fn-nop-init*) :init))
; The store is the configuration's, the groups are the operator's, and the
; raw initializer receives both from here rather than choosing either.
(assert-event (equal (fn-native-operator-result-init-store-octets *fn-nop-init*)
                     (fn-record-string-octets "/srv/fn")))
(assert-event (equal (fn-native-operator-result-init-group-octets *fn-nop-init*)
                     (list (fn-record-string-octets "fn.letters")
                           (fn-record-string-octets "fn.test"))))

; Teeth, one hypothesis at a time: a bare `init` names no group and is a
; usage error rather than a store with a guessed group table; a word that
; `fn-record-group-namep` does not admit is a usage error; a repeated name is
; one too, because the group table the store admits holds no duplicate; and
; more names than the record codec carries is one as well.  The predicate is
; the store's own -- the same one `group create` applies -- so this command
; does not own a second idea of what a group may be called.
(assert-event (equal (fn-native-operator-exit-code
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("init"))))
                     5))
; `fn-record-group-namep` bounds a name at *fn-record-max-group-name* octets.
(defconst *fn-nop-overlong-group* "ggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggg")
(assert-event (equal (length *fn-nop-overlong-group*)
                     (+ 1 *fn-record-max-group-name*)))
(assert-event (not (fn-record-group-namep *fn-nop-overlong-group*)))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run
                       *fn-nop-minimal-config*
                       (fn-nop-test-argv
                        (list "init" *fn-nop-overlong-group*))))
                     :usage))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run
                       *fn-nop-minimal-config*
                       (fn-nop-test-argv '("init" "fn.test" "fn.test"))))
                     :usage))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run
                       *fn-nop-minimal-config*
                       (fn-nop-test-argv
                        (cons "init"
                              '("g01" "g02" "g03" "g04" "g05" "g06" "g07" "g08"
                                "g09" "g10" "g11" "g12" "g13" "g14" "g15" "g16"
                                "g17")))))
                     :usage))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run
                       *fn-nop-minimal-config*
                       (fn-nop-test-argv
                        (cons "init"
                              '("g01" "g02" "g03" "g04" "g05" "g06" "g07" "g08"
                                "g09" "g10" "g11" "g12" "g13" "g14" "g15" "g16")))))
                     :accepted))
(assert-event (equal (fn-native-operator-result-init-group-octets
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("init"))))
                     nil))

; The physical observation and what ACL2 makes of it.  `writer.lock` is one
; of the names, so a store a live owner holds is refused on its presence and
; no lock is attempted to find that out.
(assert-event (consp (fn-native-operator-init-marker-octets)))
(assert-event (member-equal (fn-record-string-octets "writer.lock")
                            (fn-native-operator-init-marker-octets)))
(assert-event (member-equal (fn-record-string-octets "config.json")
                            (fn-native-operator-init-marker-octets)))

(defconst *fn-nop-init-fresh* (fn-native-operator-init-outcome *fn-nop-init* nil))
(assert-event (equal (fn-native-operator-result-status *fn-nop-init-fresh*) :accepted))
(assert-event (equal (fn-native-operator-result-reason *fn-nop-init-fresh*) :initialize))
(assert-event (equal (fn-native-operator-exit-code *fn-nop-init-fresh*) 0))

(defconst *fn-nop-init-existing*
  (fn-native-operator-init-outcome
   *fn-nop-init* (list (fn-record-string-octets "writer.lock"))))
(assert-event (equal (fn-native-operator-result-status *fn-nop-init-existing*) :refused))
(assert-event (equal (fn-native-operator-result-reason *fn-nop-init-existing*) :store-exists))
(assert-event (equal (fn-native-operator-exit-code *fn-nop-init-existing*) 1))
; Any one marker is enough; the refusal is not a count of them.
(assert-event (equal (fn-native-operator-exit-code
                      (fn-native-operator-init-outcome
                       *fn-nop-init*
                       (list (fn-record-string-octets "config.json"))))
                     1))
; Teeth: the initializer is unreachable from a plan that is not an accepted
; init plan, whatever a raw caller hands the outcome function.
(assert-event (equal (fn-native-operator-exit-code
                      (fn-native-operator-init-outcome
                       (fn-native-operator-run *fn-nop-minimal-config*
                                               (fn-nop-test-argv '("status")))
                       nil))
                     5))
(assert-event (equal (fn-native-operator-exit-code
                      (fn-native-operator-init-outcome
                       (fn-native-operator-run *fn-nop-minimal-config*
                                               (fn-nop-test-argv '("init")))
                       nil))
                     5))
; Three outcomes, three codes, from one command (D13).
(assert-event
 (equal (list (fn-native-operator-exit-code *fn-nop-init-fresh*)
              (fn-native-operator-exit-code *fn-nop-init-existing*)
              (fn-native-operator-exit-code
               (fn-native-operator-run *fn-nop-minimal-config*
                                       (fn-nop-test-argv '("init")))))
        '(0 1 5)))

; -----------------------------------------------------------------------------
; `peer list` rides the same administrative plan the other peer verbs do.

(defconst *fn-nop-peer-list*
  (fn-native-operator-run *fn-nop-minimal-config*
                          (fn-nop-test-argv '("peer" "list"))))
(assert-event (equal (fn-native-operator-result-status *fn-nop-peer-list*) :accepted))
(assert-event (equal (fn-native-operator-result-native-action *fn-nop-peer-list*) :admin))
(assert-event (fn-native-admin-result-queryp
               (fn-native-operator-result-admin-plan *fn-nop-peer-list*)))
(assert-event (not (fn-native-admin-result-queryp
                    (fn-native-operator-result-admin-plan
                     (fn-native-operator-run
                      *fn-nop-minimal-config*
                      (fn-nop-test-argv '("peer" "remove" "far")))))))
(assert-event (equal (fn-native-operator-exit-code
                      (fn-native-operator-run
                       *fn-nop-minimal-config*
                       (fn-nop-test-argv '("peer" "list" "far"))))
                     5))

; Help names both new subjects, and only from the ACL2 subject table.
(assert-event (fn-nop-help-subjectp "init"))
(assert-event (equal (fn-nop-help-text "init")
                     "usage: fn operator CONFIG init GROUP [GROUP...]"))
(assert-event (equal (fn-native-operator-result-arguments
                      (fn-native-operator-run nil (fn-nop-test-argv '("help" "init"))))
                     '(:help "init" "usage: fn operator CONFIG init GROUP [GROUP...]")))
(assert-event (not (fn-nop-help-subjectp "initialise")))

; The run refusal names the key, and an admitted log path reaches the run
; plan's projection.
(defconst *fn-nop-agent-config*
  (fn-nop-test-lines '("[store]" "path = \"/srv/fn\""
                       "[posting]" "agent = \"fn@hbox.ember.software\"")))
(assert-event (equal (fn-native-operator-result-reason
                      (fn-native-operator-run *fn-nop-agent-config*
                                              (fn-nop-test-argv '("run"))))
                     '(:unsupported-profile "agent")))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run *fn-nop-agent-config*
                                              (fn-nop-test-argv '("run"))))
                     :usage))
; Offline actions do not consult owner availability.
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run *fn-nop-agent-config*
                                              (fn-nop-test-argv '("status"))))
                     :accepted))
(defconst *fn-nop-log-config*
  (fn-nop-test-lines '("[store]" "path = \"/srv/fn\""
                       "[log]" "path = \"/var/log/fn/fn.log\"")))
(assert-event (equal (fn-native-operator-result-run-log-path-octets
                      (fn-native-operator-run *fn-nop-log-config*
                                              (fn-nop-test-argv '("run"))))
                     (fn-record-string-octets "/var/log/fn/fn.log")))
(assert-event (equal (fn-native-operator-result-run-log-path-octets
                      (fn-native-operator-run
                       (fn-nop-test-lines '("[store]" "path = \"/srv/fn\""))
                       (fn-nop-test-argv '("run"))))
                     nil))
