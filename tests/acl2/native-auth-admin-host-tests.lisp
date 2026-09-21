; Program-mode wrapper checks for native AUTHINFO administration.
(in-package "ACL2")
(include-book "../../host/native-auth-admin-host")

(assert-event
 (equal (fn-native-auth-admin-host-action-kind
         (fn-native-auth-admin-host-parse-argv
          (list (fn-record-string-octets "list"))))
        :list))
(assert-event
 (equal (fn-native-auth-admin-host-max-octets)
        *fn-native-auth-max-octets*))
(assert-event
 (equal (fn-native-auth-admin-host-salt-octets)
        *fn-authsec-salt-octets*))
(assert-event
 (equal (fn-native-auth-admin-host-recovery-outcome
         (fn-native-auth-admin-host-recovery-step
          (fn-native-auth-admin-host-recovery-start nil nil)
          '(:recovery-directory-result :ok)))
        :recovered))
