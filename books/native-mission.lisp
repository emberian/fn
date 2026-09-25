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
                        (:instance fn-bs-config-decode-of-encode
                                   (values (fn-native-mission-profile name))))
           :in-theory (e/d (fn-bs-config-frame-for-profile fn-bs-profile-init-verdict
                            fn-bs-profile-admittedp fn-bs-profile-of)
                           (fn-bs-config-decode fn-bs-config-encode
                            fn-bs-profile-validp fn-bs-profile-resolve
                            fn-native-mission-profiles-valid
                            fn-bs-config-decode-of-encode)))))

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
  :hints (("Goal" :in-theory (e/d (fn-native-operator-run
                                   fn-native-operator-command-preflight
                                   fn-native-operator-preflight-needs-config-p
                                   fn-nop-parse-command fn-nop-parse-init
                                   fn-nop-usage fn-nop-refused fn-nop-result
                                   fn-native-operator-result-status
                                   fn-native-operator-result-command
                                   fn-native-operator-result-init-profile
                                   fn-native-operator-result-init-planp
                                   fn-native-operator-result-arguments)
                                  (fn-native-admin-some-group-name-reservedp
                                   fn-nop-parse-init-groups fn-nop-argument-texts
                                   fn-nop-parse-init-plain fn-nop-some-flag-wordp
                                   fn-nop-argvp fn-native-config-load
                                   fn-ncfg-ascii-octetsp fn-nop-parse-store
                                   fn-nop-parse-post fn-nop-parse-run
                                   fn-nop-parse-principal fn-nop-parse-administration
                                   fn-native-config-show fn-nop-help-text
                                   fn-native-config-operator-availablep)))))
