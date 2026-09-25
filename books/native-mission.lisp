; fn: a mission's store profile is the one its store opens with (PKT-097).
;
; `init' under a mission's fn.toml plans the mission's profile request
; (books/native-operator.lisp fn-nop-parse-init, fn-native-mission-request);
; host/native/operator.lisp fnn-operator-execute-init hands that request to
; fnn-command-init, whose config.json is host/store-host.lisp
; fn-store-metadata-config-frame, that is `fn-bs-config-frame-for-profile'.
; Every open decodes config.json with `fn-bs-config-decode'.

(in-package "ACL2")
(include-book "native-operator")
(include-book "store-profile-upgrade")

(defun fn-native-mission-profile (name)
  (declare (xargs :guard t))
  (fn-bs-profile-resolve (fn-native-mission-request name) nil))

; The frame `init' writes for a request that resolves to a valid profile
; with no history requirement is that profile's encoding.
(local
 (defthm fn-native-mission-valid-profile-is-not-invalid
   (implies (fn-bs-profile-validp v)
            (not (equal (car v) :invalid)))
   :hints (("Goal" :in-theory (enable fn-bs-profile-validp fn-bs-profile-invalid-reason)
            :expand ((fn-bs-meta-nth 0 v))))))

(local
 (defthm fn-native-mission-frame-is-the-encoding
   (implies (and (consp req)
                 (fn-bs-profile-validp (fn-bs-profile-resolve req nil))
                 (not (equal (fn-bs-pf 14 (fn-bs-profile-resolve req nil)) 1)))
            (equal (fn-bs-config-frame-for-profile req)
                   (fn-bs-config-encode (fn-bs-profile-resolve req nil))))
   :hints (("Goal" :in-theory (e/d (fn-bs-config-frame-for-profile
                                    fn-bs-profile-init-verdict)
                                   (fn-bs-config-encode fn-bs-profile-validp
                                    fn-bs-profile-resolve fn-bs-pf))))))

; KEYSTONE.  For each mission, the frame `init' writes decodes, at every
; later open, to the mission's profile, and that profile is admitted.
(defthm fn-native-mission-store-opens-with-its-profile
  (implies (member-equal name *fn-ncfg-mission-names*)
           (and (fn-bs-profile-admittedp (fn-native-mission-profile name))
                (equal (fn-bs-config-decode
                        (fn-bs-config-frame-for-profile
                         (fn-native-mission-request name)))
                       (fn-native-mission-profile name))))
  :hints (("Goal" :use ((:instance fn-native-mission-profiles-valid)
                        (:instance fn-native-mission-frame-is-the-encoding
                                   (req (fn-native-mission-request name)))
                        (:instance fn-bs-config-decode-of-encode
                                   (values (fn-native-mission-profile name))))
           :in-theory (e/d (fn-bs-profile-admittedp fn-bs-profile-of)
                           (fn-bs-config-decode fn-bs-config-encode
                            fn-bs-config-frame-for-profile
                            (:e fn-bs-config-frame-for-profile)
                            (:e fn-bs-profile-init-verdict)
                            (:e fn-bs-config-encode) (:e fn-bs-config-decode)
                            fn-bs-profile-validp fn-bs-profile-resolve
                            fn-native-mission-request (:e fn-native-mission-request)
                            fn-native-mission-profiles-valid
                            fn-native-mission-frame-is-the-encoding
                            fn-bs-config-decode-of-encode)))))

(local
 (progn
   (defthm fn-native-mission-command-of-result
     (equal (fn-native-operator-result-command (fn-nop-result status reason command config args))
            command))
   (defthm fn-native-mission-status-of-result
     (equal (fn-native-operator-result-status (fn-nop-result status reason command config args))
            status))
   (defthm fn-native-mission-command-of-administration
     (equal (fn-native-operator-result-command (fn-nop-parse-administration command argv config))
            command)
     :hints (("Goal" :in-theory (e/d (fn-nop-parse-administration fn-nop-usage fn-nop-refused)
                                     (fn-native-admin-plan fn-native-admin-result-status
                                      fn-native-admin-result-reason)))))
   (defthm fn-native-mission-command-of-store
     (equal (fn-native-operator-result-command (fn-nop-parse-store words config)) "store")
     :hints (("Goal" :in-theory (e/d (fn-nop-parse-store fn-nop-usage fn-nop-refused)
                                     (fn-nop-parse-profile-flags fn-nop-profile-preset-word)))))
   (defthm fn-native-mission-command-of-post
     (equal (fn-native-operator-result-command (fn-nop-parse-post words config)) "post")
     :hints (("Goal" :in-theory (e/d (fn-nop-parse-post fn-nop-usage fn-nop-refused)
                                     (fn-nop-parse-post-aux)))))
   (defthm fn-native-mission-command-of-peering
     (equal (fn-native-operator-result-command (fn-nop-parse-peering words config)) "peer")
     :hints (("Goal" :in-theory (enable fn-nop-parse-peering fn-nop-usage))))
   (defthm fn-native-mission-command-of-principal
     (equal (fn-native-operator-result-command (fn-nop-parse-principal argv config)) "principal")
     :hints (("Goal" :in-theory (e/d (fn-nop-parse-principal fn-nop-usage fn-nop-refused)
                                     (fn-native-auth-admin-parse-argv
                                      fn-native-auth-admin-plan-status
                                      fn-native-auth-admin-plan-reason)))))

   ; Under a mission, an accepted init plans the mission's request.
   (defthm fn-native-mission-parse-init-profile
     (implies (and (member-equal (fn-native-config-ops-mission config) *fn-ncfg-mission-names*)
                   (equal (fn-native-operator-result-status (fn-nop-parse-init words config))
                          :accepted))
              (equal (fn-native-operator-result-init-profile (fn-nop-parse-init words config))
                     (fn-native-mission-request (fn-native-config-ops-mission config))))
     :hints (("Goal" :in-theory (e/d (fn-nop-parse-init fn-nop-usage fn-nop-refused
                                      fn-native-operator-result-init-profile
                                      fn-native-operator-result-init-planp
                                      fn-native-operator-result-arguments)
                                     (fn-nop-parse-init-plain fn-nop-parse-init-groups
                                      fn-nop-some-flag-wordp
                                      fn-native-admin-some-group-name-reservedp)))))

   ; The one grammar branch whose plan is named init is `init'.
   (defthm fn-native-mission-parse-command-init
     (implies (equal (fn-native-operator-result-command
                      (fn-nop-parse-command words config argv))
                     "init")
              (equal (fn-nop-parse-command words config argv)
                     (fn-nop-parse-init (cdr words) config)))
     :hints (("Goal" :in-theory (e/d (fn-nop-parse-command fn-nop-usage fn-nop-refused)
                                     (fn-nop-parse-init fn-nop-parse-store fn-nop-parse-post
                                      fn-nop-parse-principal fn-nop-parse-administration
                                      fn-nop-parse-peering fn-nop-peering-verbp
                                      fn-nop-parse-run fn-native-config-show fn-nop-help-text
                                      fn-nop-help-subjectp fn-nop-watch-seconds
                                      fn-nop-result fn-native-operator-result-command
                                      fn-native-operator-result-status)))))

   ; `run' is the grammar's plan whenever the plan is init.
   (defthm fn-native-mission-run-init
     (implies (and (equal (car (fn-native-config-load config)) :accepted)
                   (equal (fn-native-operator-result-command
                           (fn-native-operator-run config argv))
                          "init"))
              (equal (fn-native-operator-run config argv)
                     (fn-nop-parse-command (fn-nop-argument-texts argv)
                                           (cadr (fn-native-config-load config)) argv)))
     :hints (("Goal" :in-theory (e/d (fn-native-operator-run
                                      fn-native-operator-command-preflight
                                      fn-native-operator-preflight-needs-config-p
                                      fn-nop-usage)
                                     (fn-nop-parse-command fn-nop-argument-texts
                                      fn-nop-argvp fn-native-config-load
                                      fn-ncfg-ascii-octetsp fn-nop-result
                                      fn-native-operator-result-command
                                      fn-native-operator-result-status
                                      fn-native-config-operator-availablep))
              :expand ((fn-nop-parse-command (fn-nop-argument-texts argv) nil argv)))))))

; KEYSTONE.  The subject is `fn-native-operator-run', which
; host/native-operator-host.lisp:19 calls.  Under a configuration naming a
; mission, an accepted `init' plans exactly the mission's profile request.
(defthm fn-native-operator-run-init-under-a-mission
  (let ((result (fn-native-operator-run config argv))
        (loaded (fn-native-config-load config)))
    (implies (and (equal (car loaded) :accepted)
                  (member-equal (fn-native-config-ops-mission (cadr loaded))
                                *fn-ncfg-mission-names*)
                  (equal (fn-native-operator-result-command result) "init")
                  (equal (fn-native-operator-result-status result) :accepted))
             (equal (fn-native-operator-result-init-profile result)
                    (fn-native-mission-request
                     (fn-native-config-ops-mission (cadr loaded))))))
  :hints (("Goal"
           :use ((:instance fn-native-mission-run-init)
                 (:instance fn-native-mission-parse-command-init
                            (words (fn-nop-argument-texts argv))
                            (config (cadr (fn-native-config-load config))))
                 (:instance fn-native-mission-parse-init-profile
                            (words (cdr (fn-nop-argument-texts argv)))
                            (config (cadr (fn-native-config-load config)))))
           :in-theory (disable fn-native-mission-run-init
                                      fn-native-mission-parse-command-init
                                      fn-native-mission-parse-init-profile
                                      fn-nop-argument-texts
                                      fn-native-operator-run fn-nop-parse-command
                                      fn-nop-parse-init fn-native-config-load
                                      fn-native-operator-result-init-profile
                                      fn-native-operator-result-command
                                      fn-native-operator-result-status
                                      fn-native-mission-request
                                      fn-native-config-ops-mission))))
