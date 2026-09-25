; ACL2-facing boundary for native AUTHINFO credential administration.
;
; Raw Lisp transports bounded observations and executes only actions returned
; here.  It does not parse argv/TOML, derive principals or verifiers, select
; public report fields, or advance the mutable replacement machine itself.
(in-package "ACL2")
(include-book "../books/native-auth-admin")

(set-state-ok t)
(program)

(defun fn-native-auth-admin-host-parse-argv (argv)
  (fn-native-auth-admin-parse-argv argv))
(defun fn-native-auth-admin-host-plan-status (result)
  (fn-native-auth-admin-plan-status result))
(defun fn-native-auth-admin-host-plan-reason (result)
  (fn-native-auth-admin-plan-reason result))
(defun fn-native-auth-admin-host-plan-action (result)
  (fn-native-auth-admin-plan-action result))
(defun fn-native-auth-admin-host-action-kind (result)
  (fn-native-auth-admin-action-kind result))
(defun fn-native-auth-admin-host-action-name (result)
  (fn-native-auth-admin-action-name result))
(defun fn-native-auth-admin-host-action-principal-text (result)
  (fn-native-auth-admin-action-principal-text result))
(defun fn-native-auth-admin-host-action-principal-presentp (result)
  (fn-native-auth-admin-action-principal-presentp result))
(defun fn-native-auth-admin-host-action-postingp (result)
  (fn-native-auth-admin-action-postingp result))

(defun fn-native-auth-admin-host-list (octets presentp max-credentials)
  (fn-native-auth-admin-list octets presentp max-credentials))

(defun fn-native-auth-admin-host-action-signing-text (result)
  (fn-native-auth-admin-action-signing-text result))
(defun fn-native-auth-admin-host-bind (octets presentp name signing-text
                                             max-credentials)
  (fn-native-auth-admin-bind octets presentp name signing-text max-credentials))

(defun fn-native-auth-admin-host-set-password
  (octets presentp name secret confirmation salt
          principal-text principal-presentp postingp max-credentials)
  (fn-native-auth-admin-set-password
   octets presentp name secret confirmation salt
   principal-text principal-presentp postingp max-credentials))

(defun fn-native-auth-admin-host-result-status (result)
  (fn-native-auth-admin-result-status result))
(defun fn-native-auth-admin-host-result-reason (result)
  (fn-native-auth-admin-result-reason result))
(defun fn-native-auth-admin-host-result-octets (result)
  (fn-native-auth-admin-result-octets result))
(defun fn-native-auth-admin-host-result-report (result)
  (fn-native-auth-admin-result-report result))

(defun fn-native-auth-admin-host-max-octets (max-credentials)
  (fn-native-auth-max-octets max-credentials))
(defun fn-native-auth-admin-host-max-secret-octets ()
  *fn-native-auth-admin-max-secret-octets*)
(defun fn-native-auth-admin-host-salt-octets ()
  *fn-authsec-salt-octets*)

(defun fn-native-auth-admin-host-rp-start ()
  (fn-native-auth-admin-rp-start))
(defun fn-native-auth-admin-host-rp-action (phase)
  (fn-native-auth-admin-rp-action phase))
(defun fn-native-auth-admin-host-rp-step (phase event)
  (fn-native-auth-admin-rp-step phase event))
(defun fn-native-auth-admin-host-rp-outcome (phase)
  (fn-native-auth-admin-rp-outcome phase))

(defun fn-native-auth-admin-host-recovery-start (stage-presentp final-presentp)
  (fn-native-auth-admin-recovery-start stage-presentp final-presentp))
(defun fn-native-auth-admin-host-recovery-action (phase)
  (fn-native-auth-admin-recovery-action phase))
(defun fn-native-auth-admin-host-recovery-step (phase event)
  (fn-native-auth-admin-recovery-step phase event))
(defun fn-native-auth-admin-host-recovery-outcome (phase)
  (fn-native-auth-admin-recovery-outcome phase))

(logic)
