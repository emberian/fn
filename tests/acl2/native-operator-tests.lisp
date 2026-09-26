; Teeth for the bounded native operator grammar and its config gate.
(in-package "ACL2")
(include-book "../../books/native-operator")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

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
                       (:help "status" "usage: fn operator CONFIG status [--watch SECONDS] (asks the running owner over its control socket; offline, reads the store)"))))
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

; `store upgrade-profile [WORD] [--FIELD N ...]': an offline store action
; whose plan names the profile request (base and overrides); the verdict
; (upgrade or refusal) is the store's (books/store-profile-upgrade.lisp), so
; every well-formed request is a plan here.
(defconst *fn-nop-upgrade*
  (fn-native-operator-run *fn-nop-minimal-config*
                          (fn-nop-test-argv '("store" "upgrade-profile" "scale"))))
(assert-event (equal (fn-native-operator-result-status *fn-nop-upgrade*) :accepted))
(assert-event (equal (fn-native-operator-result-native-action *fn-nop-upgrade*)
                     :upgrade-profile))
(assert-event (equal (fn-native-operator-result-upgrade-profile *fn-nop-upgrade*)
                     '(:scale nil)))
(assert-event (equal (fn-native-operator-result-upgrade-profile
                      (fn-native-operator-run
                       *fn-nop-minimal-config*
                       (fn-nop-test-argv '("store" "upgrade-profile" "development"))))
                     '(:development nil)))
; With no word the base is the store's current profile: alone, the format 7
; to 8 step; with flags, the operator's raise of those fields.
(assert-event (equal (fn-native-operator-result-upgrade-profile
                      (fn-native-operator-run
                       *fn-nop-minimal-config*
                       (fn-nop-test-argv '("store" "upgrade-profile"))))
                     '(:current nil)))
(assert-event (equal (fn-native-operator-result-upgrade-profile
                      (fn-native-operator-run
                       *fn-nop-minimal-config*
                       (fn-nop-test-argv '("store" "upgrade-profile"
                                           "--max-transactions" "100000"
                                           "--max-article-octets" "20000"))))
                     '(:current ((2 . 100000) (5 . 20000)))))
; D31: the history requirement takes a word, never a decimal.
(assert-event (equal (fn-native-operator-result-upgrade-profile
                      (fn-native-operator-run
                       *fn-nop-minimal-config*
                       (fn-nop-test-argv '("store" "upgrade-profile"
                                           "--history-marker" "required"))))
                     '(:current ((14 . 1)))))
(assert-event (equal (fn-native-operator-exit-code
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("store" "upgrade-profile"
                                                                  "--history-marker" "1"))))
                     5))
(assert-event (equal (fn-native-operator-exit-code
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("store" "upgrade-profile"
                                                                  "--max-transactions" "required"))))
                     5))
; A repeated field, a value that is not a decimal frame natural, and an
; unknown flag are usage errors.
(assert-event (equal (fn-native-operator-exit-code
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("store" "upgrade-profile"
                                                                  "--max-transactions" "5"
                                                                  "--max-transactions" "6"))))
                     5))
(assert-event (equal (fn-native-operator-exit-code
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("store" "upgrade-profile"
                                                                  "--max-transactions" "18446744073709551616"))))
                     5))
(assert-event (equal (fn-native-operator-exit-code
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("store" "upgrade-profile"
                                                                  "--max-capacity" "5"))))
                     5))
; An init plan names no upgrade profile, and malformed store commands are
; usage: an unknown word, a missing word, an extra word, another subcommand.
(assert-event (equal (fn-native-operator-result-upgrade-profile *fn-nop-init*) nil))
(assert-event (equal (fn-native-operator-exit-code
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("store" "upgrade-profile" "huge"))))
                     5))
(assert-event (equal (fn-native-operator-exit-code
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("store" "upgrade-profile" "scale" "x"))))
                     5))
(assert-event (equal (fn-native-operator-exit-code
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("store" "downgrade"))))
                     5))

;
; `store compact': an offline store action with no argument; what it does to
; the store is `fn-cverb-decide' (books/store-compact-verb.lisp).
(defconst *fn-nop-compact*
  (fn-native-operator-run *fn-nop-minimal-config*
                          (fn-nop-test-argv '("store" "compact"))))
(assert-event (equal (fn-native-operator-result-status *fn-nop-compact*) :accepted))
(assert-event (equal (fn-native-operator-result-native-action *fn-nop-compact*) :compact))
(assert-event (equal (fn-native-operator-result-upgrade-profile *fn-nop-compact*) nil))
(assert-event (equal (fn-native-operator-result-native-action *fn-nop-upgrade*)
                     :upgrade-profile))
(assert-event (equal (fn-native-operator-exit-code
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("store" "compact" "now"))))
                     5))
; Teeth for fn-native-operator-run-store-compact-is-the-compact-action.
; Without the argv hypothesis: an accepted store plan that is not compact.
(local (must-fail
        (defthm fn-nop-compact-action-without-argv
          (equal (fn-native-operator-result-native-action *fn-nop-upgrade*) :compact))))
; Without acceptance: `store compact' under a configuration that does not
; load is usage, and its action is :none.
(defconst *fn-nop-compact-bad-config*
  (fn-native-operator-run (fn-nop-test-lines '("[store]" "path = 7"))
                          (fn-nop-test-argv '("store" "compact"))))
(assert-event (equal (fn-native-operator-result-status *fn-nop-compact-bad-config*) :usage))
(local (must-fail
        (defthm fn-nop-compact-action-without-acceptance
          (equal (fn-native-operator-result-native-action *fn-nop-compact-bad-config*)
                 :compact))))
; Tooth for fn-native-operator-run-compact-action-is-only-store-compact:
; without the :compact action the argv is any other command.
(local (must-fail
        (defthm fn-nop-compact-argv-without-action
          (equal (fn-nop-argument-texts
                  (fn-nop-test-argv '("store" "upgrade-profile" "scale")))
                 '("store" "compact")))))

;; `store reclaim [--dry-run]' (STO-017): offline store actions; what they
;; remove is `fn-rclp-decide' (books/store-reclaim-pack.lisp).
(defconst *fn-nop-reclaim*
  (fn-native-operator-run *fn-nop-minimal-config*
                          (fn-nop-test-argv '("store" "reclaim"))))
(defconst *fn-nop-reclaim-dry*
  (fn-native-operator-run *fn-nop-minimal-config*
                          (fn-nop-test-argv '("store" "reclaim" "--dry-run"))))
(assert-event (and (equal (fn-native-operator-result-status *fn-nop-reclaim*) :accepted)
                   (equal (fn-native-operator-result-native-action *fn-nop-reclaim*)
                          :reclaim)
                   (equal (fn-native-operator-result-status *fn-nop-reclaim-dry*) :accepted)
                   (equal (fn-native-operator-result-native-action *fn-nop-reclaim-dry*)
                          :reclaim-dry-run)))
(assert-event (equal (fn-native-operator-exit-code
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("store" "reclaim" "now"))))
                     5))
; Teeth for the two is-the-action keystones: without the argv an accepted
; store plan is another action; without acceptance the action is :none.
(local (must-fail
        (defthm fn-nop-reclaim-action-without-argv
          (equal (fn-native-operator-result-native-action *fn-nop-compact*) :reclaim))))
(local (must-fail
        (defthm fn-nop-reclaim-dry-action-without-argv
          (equal (fn-native-operator-result-native-action *fn-nop-reclaim*)
                 :reclaim-dry-run))))
(defconst *fn-nop-reclaim-bad-config*
  (fn-native-operator-run (fn-nop-test-lines '("[store]" "path = 7"))
                          (fn-nop-test-argv '("store" "reclaim"))))
(assert-event (equal (fn-native-operator-result-status *fn-nop-reclaim-bad-config*) :usage))
(local (must-fail
        (defthm fn-nop-reclaim-action-without-acceptance
          (equal (fn-native-operator-result-native-action *fn-nop-reclaim-bad-config*)
                 :reclaim))))
; Teeth for the two is-only keystones: another argv is not the command.
(local (must-fail
        (defthm fn-nop-reclaim-argv-without-action
          (equal (fn-nop-argument-texts (fn-nop-test-argv '("store" "compact")))
                 '("store" "reclaim")))))
(local (must-fail
        (defthm fn-nop-reclaim-dry-argv-without-action
          (equal (fn-nop-argument-texts (fn-nop-test-argv '("store" "reclaim")))
                 '("store" "reclaim" "--dry-run")))))

; `store checkpoint' (P3): an offline store action with no argument; it
; publishes the exact-state checkpoint (books/store-checkpoint-open.lisp).
(defconst *fn-nop-checkpoint*
  (fn-native-operator-run *fn-nop-minimal-config*
                          (fn-nop-test-argv '("store" "checkpoint"))))
(assert-event (equal (fn-native-operator-result-status *fn-nop-checkpoint*) :accepted))
(assert-event (equal (fn-native-operator-result-native-action *fn-nop-checkpoint*)
                     :checkpoint))
(assert-event (equal (fn-native-operator-result-native-action *fn-nop-compact*) :compact))
(assert-event (equal (fn-native-operator-exit-code
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("store" "checkpoint" "now"))))
                     5))
; Teeth for fn-native-operator-run-store-checkpoint-is-the-checkpoint-action.
; Without the argv hypothesis: an accepted store plan that is not checkpoint.
(local (must-fail
        (defthm fn-nop-checkpoint-action-without-argv
          (equal (fn-native-operator-result-native-action *fn-nop-compact*) :checkpoint))))
; Without acceptance: under a configuration that does not load it is usage.
(defconst *fn-nop-checkpoint-bad-config*
  (fn-native-operator-run (fn-nop-test-lines '("[store]" "path = 7"))
                          (fn-nop-test-argv '("store" "checkpoint"))))
(assert-event (equal (fn-native-operator-result-status *fn-nop-checkpoint-bad-config*) :usage))
(local (must-fail
        (defthm fn-nop-checkpoint-action-without-acceptance
          (equal (fn-native-operator-result-native-action *fn-nop-checkpoint-bad-config*)
                 :checkpoint))))
; Tooth for fn-native-operator-run-checkpoint-action-is-only-store-checkpoint.
(local (must-fail
        (defthm fn-nop-checkpoint-argv-without-action
          (equal (fn-nop-argument-texts
                  (fn-nop-test-argv '("store" "compact")))
                 '("store" "checkpoint")))))

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
(defconst *fn-nop-overlong-group*
  (coerce (make-list (+ 1 *fn-record-max-group-name*) :initial-element #\g)
          'string))
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
; D27: seventeen groups (over the pre-D27 16) are no longer a usage error;
; the group count's codec ceiling (65 535) is above what one argv can name,
; so what refuses a long `init' is the argv work bound
; (`*fn-nop-max-arguments*', 32 words).
(defconst *fn-nop-17-groups*
  '("g01" "g02" "g03" "g04" "g05" "g06" "g07" "g08"
    "g09" "g10" "g11" "g12" "g13" "g14" "g15" "g16" "g17"))
(assert-event (not (equal (fn-native-operator-result-status
                           (fn-native-operator-run
                            *fn-nop-minimal-config*
                            (fn-nop-test-argv (cons "init" *fn-nop-17-groups*))))
                          :usage)))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run
                       *fn-nop-minimal-config*
                       (fn-nop-test-argv
                        (cons "init"
                              (append *fn-nop-17-groups*
                                      '("g18" "g19" "g20" "g21" "g22" "g23"
                                        "g24" "g25" "g26" "g27" "g28" "g29"
                                        "g30" "g31" "g32"))))))
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

; The store profile: the D27 defaults unless the operator names a preset
; (`--profile development|scale') or fields.  An unnamed profile word is a
; usage error, not the default; `--profile` without a group is a usage error
; as before.
(assert-event (equal (fn-native-operator-result-init-profile *fn-nop-init*)
                     '(:default nil)))
; Fields: the request carries them, in the order named.
(defconst *fn-nop-init-fields*
  (fn-native-operator-run *fn-nop-minimal-config*
                          (fn-nop-test-argv
                           '("init" "--max-transactions" "1000"
                             "--max-article-octets" "20000" "fn.letters"))))
(assert-event (equal (fn-native-operator-result-init-profile *fn-nop-init-fields*)
                     '(:default ((2 . 1000) (5 . 20000)))))
(assert-event (equal (fn-native-operator-result-init-group-octets *fn-nop-init-fields*)
                     (list (fn-record-string-octets "fn.letters"))))
; A request that breaks a relation is refused at init, by the relation's
; name: a record ceiling below an event kind's, a history bound below the
; record ceiling, a zero transaction count.
(defconst *fn-nop-init-small-record*
  (fn-native-operator-run *fn-nop-minimal-config*
                          (fn-nop-test-argv
                           '("init" "--max-record-octets" "100" "fn.letters"))))
(assert-event (equal (fn-native-operator-result-status *fn-nop-init-small-record*)
                     :refused))
(assert-event (equal (fn-native-operator-result-reason *fn-nop-init-small-record*)
                     :max-record-octets-below-an-event-kind))
(assert-event (equal (fn-native-operator-result-init-profile *fn-nop-init-small-record*)
                     nil))
(assert-event (equal (fn-native-operator-result-reason
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv
                                               '("init" "--max-history-octets" "1000" "fn.letters"))))
                     :max-history-octets-below-max-record-octets))
(assert-event (equal (fn-native-operator-result-reason
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv
                                               '("init" "--max-transactions" "0" "fn.letters"))))
                     :max-transactions-outside-txid-width))
(defconst *fn-nop-init-scale*
  (fn-native-operator-run *fn-nop-minimal-config*
                          (fn-nop-test-argv
                           '("init" "--profile" "scale" "fn.letters"))))
(assert-event (equal (fn-native-operator-result-status *fn-nop-init-scale*)
                     :accepted))
(assert-event (equal (fn-native-operator-result-init-profile *fn-nop-init-scale*)
                     '(:scale nil)))
(assert-event (equal (fn-native-operator-result-init-group-octets *fn-nop-init-scale*)
                     (list (fn-record-string-octets "fn.letters"))))
(assert-event (equal (fn-native-operator-result-init-profile
                      (fn-native-operator-run
                       *fn-nop-minimal-config*
                       (fn-nop-test-argv
                        '("init" "--profile" "development" "fn.letters"))))
                     '(:development nil)))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run
                       *fn-nop-minimal-config*
                       (fn-nop-test-argv
                        '("init" "--profile" "huge" "fn.letters"))))
                     :usage))
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run
                       *fn-nop-minimal-config*
                       (fn-nop-test-argv '("init" "--profile" "scale"))))
                     :usage))
(assert-event (equal (fn-native-operator-result-init-profile
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
(defconst *fn-nop-bp-boundary*
  (fn-native-operator-run
   *fn-nop-minimal-config*
   (fn-nop-test-argv '("bp-boundary" "add" "dtn-peer"
                       "peer.example.invalid" "dtn://peer/" "4556"))))
(assert-event
 (and (equal (fn-native-operator-result-status *fn-nop-bp-boundary*)
             :accepted)
      (equal (fn-native-operator-result-native-action *fn-nop-bp-boundary*)
             :admin)))
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
                     "usage: fn operator CONFIG init [--profile development|scale|default] [--max-transactions N] [--max-history-octets N] [--max-record-octets N] [--max-article-octets N] [--max-groups-per-article N] [--max-group-name-octets N] [--max-open-suffix N] [--max-consumers N] [--max-bp-rows N] [--max-config-generations N] [--max-credentials N] [--max-policy-members N] GROUP [GROUP...]"))
(assert-event (equal (fn-native-operator-result-arguments
                      (fn-native-operator-run nil (fn-nop-test-argv '("help" "init"))))
                     '(:help "init" "usage: fn operator CONFIG init [--profile development|scale|default] [--max-transactions N] [--max-history-octets N] [--max-record-octets N] [--max-article-octets N] [--max-groups-per-article N] [--max-group-name-octets N] [--max-open-suffix N] [--max-consumers N] [--max-bp-rows N] [--max-config-generations N] [--max-credentials N] [--max-policy-members N] GROUP [GROUP...]")))
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

; -----------------------------------------------------------------------------
; RFC 5536 s3.1.4 reserved names at `init' and `group create'.  A reserved
; name in any position is a refusal (exit 1), not a usage error: the command
; line is well formed and the node declines it.  The predicate is
; `fn-native-admin-group-name-reservedp' (books/native-admin.lisp), the same
; one `group create' applies.
(defconst *fn-nop-init-example*
  (fn-native-operator-run *fn-nop-minimal-config*
                          (fn-nop-test-argv '("init" "example.test"))))
(assert-event (equal (fn-native-operator-result-status *fn-nop-init-example*)
                     :refused))
(assert-event (equal (fn-native-operator-result-reason *fn-nop-init-example*)
                     :reserved-group-name))
(assert-event (equal (fn-native-operator-exit-code *fn-nop-init-example*) 1))
(assert-event (null (fn-native-operator-result-init-group-octets
                     *fn-nop-init-example*)))
(assert-event (equal (fn-native-operator-result-native-action
                      *fn-nop-init-example*)
                     :none))
(assert-event (equal (fn-native-operator-result-reason
                      (fn-native-operator-run
                       *fn-nop-minimal-config*
                       (fn-nop-test-argv '("init" "fn.test" "Poster"))))
                     :reserved-group-name))
(defconst *fn-nop-create-poster*
  (fn-native-operator-run *fn-nop-minimal-config*
                          (fn-nop-test-argv '("group" "create" "poster"))))
(assert-event (equal (fn-native-operator-result-status *fn-nop-create-poster*)
                     :refused))
(assert-event (equal (fn-native-operator-result-reason *fn-nop-create-poster*)
                     '(:administration :reserved-group-name)))
(assert-event (equal (fn-native-operator-exit-code *fn-nop-create-poster*) 1))
; Other administrative refusals keep their usage tag.
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run
                       *fn-nop-minimal-config*
                       (fn-nop-test-argv '("group" "create" "fn..test"))))
                     :usage))
; Retiring a reserved name a store already carries stays a plan.
(assert-event (equal (fn-native-operator-result-status
                      (fn-native-operator-run
                       *fn-nop-minimal-config*
                       (fn-nop-test-argv '("group" "retire" "example.test"))))
                     :accepted))

; Teeth for `fn-native-operator-run-refuses-a-reserved-init-group', one
; `must-fail' per hypothesis; the witnesses are `group retire example.test'
; (first word not "init"), `init fn.test' with NAME outside the words, and
; `init fn.test' with NAME the unreserved fn.test -- each accepted above or
; in the `init' block.
(defconst *fn-nop-init-fn-test*
  (fn-native-operator-run *fn-nop-minimal-config*
                          (fn-nop-test-argv '("init" "fn.test"))))
(assert-event (equal (fn-native-operator-result-status *fn-nop-init-fn-test*)
                     :accepted))
(must-fail
 (defthm fn-nop-reserved-without-init
   (implies (and (member-equal name (cdr (fn-nop-argument-texts argv)))
                 (fn-native-admin-group-name-reservedp name))
            (not (equal (fn-native-operator-result-status
                         (fn-native-operator-run config argv))
                        :accepted)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-native-operator-run
                                    fn-native-operator-command-preflight
                                    fn-native-operator-preflight-needs-config-p
                                    fn-nop-parse-command fn-nop-parse-init
                                    fn-nop-usage fn-nop-refused fn-nop-result
                                    fn-native-operator-result-status)
                                   (fn-native-admin-group-name-reservedp
                                    fn-native-admin-some-group-name-reservedp
                                    fn-nop-parse-init-groups fn-nop-parse-profile-flags fn-bs-profile-resolve fn-nop-argument-texts
                                    fn-nop-argvp fn-native-config-load
                                    fn-ncfg-ascii-octetsp
                                    fn-native-config-operator-availablep))))))
(must-fail
 (defthm fn-nop-reserved-without-membership
   (implies (and (equal (car (fn-nop-argument-texts argv)) "init")
                 (fn-native-admin-group-name-reservedp name))
            (not (equal (fn-native-operator-result-status
                         (fn-native-operator-run config argv))
                        :accepted)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-native-operator-run
                                    fn-native-operator-command-preflight
                                    fn-native-operator-preflight-needs-config-p
                                    fn-nop-parse-command fn-nop-parse-init
                                    fn-nop-usage fn-nop-refused fn-nop-result
                                    fn-native-operator-result-status)
                                   (fn-native-admin-group-name-reservedp
                                    fn-native-admin-some-group-name-reservedp
                                    fn-nop-parse-init-groups fn-nop-parse-profile-flags fn-bs-profile-resolve fn-nop-argument-texts
                                    fn-nop-argvp fn-native-config-load
                                    fn-ncfg-ascii-octetsp
                                    fn-native-config-operator-availablep))))))
(must-fail
 (defthm fn-nop-init-refused-without-reservation
   (implies (and (equal (car (fn-nop-argument-texts argv)) "init")
                 (member-equal name (cdr (fn-nop-argument-texts argv))))
            (not (equal (fn-native-operator-result-status
                         (fn-native-operator-run config argv))
                        :accepted)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-native-operator-run
                                    fn-native-operator-command-preflight
                                    fn-native-operator-preflight-needs-config-p
                                    fn-nop-parse-command fn-nop-parse-init
                                    fn-nop-usage fn-nop-refused fn-nop-result
                                    fn-native-operator-result-status)
                                   (fn-native-admin-group-name-reservedp
                                    fn-native-admin-some-group-name-reservedp
                                    fn-nop-parse-init-groups fn-nop-parse-profile-flags fn-bs-profile-resolve fn-nop-argument-texts
                                    fn-nop-argvp fn-native-config-load
                                    fn-ncfg-ascii-octetsp
                                    fn-native-config-operator-availablep))))))

; The status report's grammar (books/native-live-status.lisp renders it):
; `status --watch N' carries N, `pins' and `obligations' are status actions
; of their own kind, and each carries the control socket the owner answers on.
(defconst *fn-nop-watch*
  (fn-native-operator-run *fn-nop-minimal-config*
                          (fn-nop-test-argv '("status" "--watch" "5"))))
(assert-event (equal (fn-native-operator-result-arguments *fn-nop-watch*)
                     '(:status :watch 5)))
(assert-event (equal (fn-native-operator-result-native-action *fn-nop-watch*) :status))
(assert-event (equal (fn-native-operator-result-status-watch *fn-nop-watch*) 5))
(assert-event (equal (fn-native-operator-result-status-kind *fn-nop-watch*) :status))
(assert-event (consp (fn-native-operator-result-status-control-path-octets *fn-nop-watch*)))
(assert-event (null (fn-native-operator-result-status-watch
                     (fn-native-operator-run *fn-nop-minimal-config*
                                             (fn-nop-test-argv '("status"))))))
(defconst *fn-nop-pins*
  (fn-native-operator-run *fn-nop-minimal-config* (fn-nop-test-argv '("pins"))))
(assert-event (equal (fn-native-operator-result-native-action *fn-nop-pins*) :status))
(assert-event (equal (fn-native-operator-result-status-kind *fn-nop-pins*) :pins))
(assert-event (equal (fn-native-operator-result-status-kind
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("obligations"))))
                     :obligations))
; A zero, a day and a second, and a word that is no number are usage (5).
(assert-event (equal (fn-native-operator-exit-code
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("status" "--watch" "0"))))
                     5))
(assert-event (equal (fn-native-operator-exit-code
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("status" "--watch" "86401"))))
                     5))
(assert-event (equal (fn-native-operator-result-status-watch
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("status" "--watch" "86400"))))
                     86400))
(assert-event (equal (fn-native-operator-exit-code
                      (fn-native-operator-run *fn-nop-minimal-config*
                                              (fn-nop-test-argv '("pins" "x"))))
                     5))

; -----------------------------------------------------------------------------
; The developer `store ROOT init' (PKT-103): fn-nop-developer-init, which
; host/native/io.lisp fnn-command-developer-init calls with the argv words.

; The words that became two groups on the large-article lane's store now set
; the profile field; without a base the development base applies.
(assert-event
 (equal (fn-nop-developer-init '("--profile" "default" "--max-article-octets" "65536"
                                 "fn.test"))
        '(:init ("fn.test") (:default ((5 . 65536))))))
(assert-event (equal (fn-nop-developer-init nil) '(:init nil (:development nil))))
(assert-event
 (equal (fn-nop-developer-init '("fn.test" "fn.other"))
        '(:init ("fn.test" "fn.other") (:development nil))))
; An unknown flag is refused, not created as a group; a field past the base's
; relations is refused by the relation's name.
(assert-event
 (equal (fn-nop-developer-init '("--no-such-flag" "fn.test"))
        '(:refused :flag-word-as-group)))
(assert-event
 (equal (fn-nop-developer-init '("fn.test" "--max-article-octets"))
        '(:refused :flag-word-as-group)))
(assert-event
 (equal (fn-nop-developer-init '("--max-article-octets" "65536" "fn.test"))
        '(:refused :max-record-octets-below-the-article-record)))
; The operator's init refuses the same word.
(assert-event
 (equal (fn-native-operator-result-status (fn-nop-parse-init '("--bogus" "fn.test") nil))
        :usage))
(assert-event
 (equal (fn-native-operator-result-reason (fn-nop-parse-init '("--bogus" "fn.test") nil))
        :flag-word-as-group))
; Teeth: without the :init hypothesis the statement fails (a refused plan's
; second element is its reason, not a group list, and the refusal was made
; because a group word was flag-shaped).
(must-fail
 (defthm nopt-developer-init-groups-are-not-flags-without-init
   (not (fn-nop-some-flag-wordp (cadr (fn-nop-developer-init words))))
   :hints (("Goal" :in-theory (disable fn-nop-parse-profile-flags
                                       fn-bs-profile-resolve)))))
