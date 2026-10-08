; ACL2-facing native operator boundary.
;
; The raw image is allowed to make bounded file/argv byte vectors and emit the
; returned tagged result.  It does not parse a command, choose defaults, or
; assign an exit code: fn-native-operator-run owns all three.
(in-package "ACL2")
(include-book "../books/native-operator")
(include-book "../books/native-operator-stage")

; Row S3 (lane operability-2): maintenance verbs on the running owner, the
; stopped store's status from its checkpoint header.
(include-book "../books/owner-maintenance-request")
(include-book "../books/definterface")

(defun fn-native-operator-host-preflight (argv-octets)
  (declare (xargs :mode :program))
  (fn-native-operator-command-preflight argv-octets))

(definterface fn-native-operator-host-preflight
  :class :program
  :exempt ((argv-octets "the argv preflight is the check: it refuses a malformed argv by name")))

(defun fn-native-operator-host-preflight-needs-config-p (result)
  (declare (xargs :mode :program))
  (fn-native-operator-preflight-needs-config-p result))

(definterface fn-native-operator-host-preflight-needs-config-p
  :class ::program)

(defun fn-native-operator-host-run (config-octets argv-octets)
  (declare (xargs :mode :program))
  (fn-native-operator-run config-octets argv-octets))

(defun fn-native-operator-host-run-at (cwd config-path config-octets argv-octets)
  (declare (xargs :mode :program
                  :guard (and (fn-cbor-octet-listp cwd) (fn-cbor-octet-listp config-path))))
  (fn-native-operator-run-at cwd config-path config-octets argv-octets))

(definterface fn-native-operator-host-run-at
  :class :program
  :kinds ((cwd fn-cbor-octet-listp) (config-path fn-cbor-octet-listp))
  :exempt ((argv-octets "a list of argument octet lists, preflighted (fn-native-operator-host-preflight)")
           (config-octets "read by fnn-operator-read-config, bounded; NIL when absent")))

(defun fn-native-operator-host-result-carry-fields (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-carry-fields result))

(definterface fn-native-operator-host-result-carry-fields
  :class ::program)

(defun fn-native-operator-host-result-compaction-argv (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-compaction-argv result))

(defun fn-native-operator-host-result-compaction-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-compaction-control-path-octets result))

;; Row S9: `retire' (books/native-retire.lisp).
(defun fn-native-operator-host-result-retire-argv (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-retire-argv result))

; Actual retire CLI projection consumed before observation starts.
(definterface fn-native-operator-host-result-retire-argv :class :program)

(defun fn-native-operator-host-result-retire-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-retire-control-path-octets result))

(definterface fn-native-operator-host-result-retire-control-path-octets
  :class ::program)

(defun fn-native-operator-host-result-reclaim-argv (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-reclaim-argv result))

(defun fn-native-operator-host-result-reclaim-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-reclaim-control-path-octets result))

(defun fn-native-operator-host-result-status (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-status result))

(definterface fn-native-operator-host-result-status
  :class ::program)

(defun fn-native-operator-host-result-reason (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-reason result))

(definterface fn-native-operator-host-result-reason
  :class ::program)

(defun fn-native-operator-host-result-command (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-command result))

(definterface fn-native-operator-host-result-command
  :class ::program)

(defun fn-native-operator-host-result-exit-code (result)
  (declare (xargs :mode :program))
  (fn-native-operator-exit-code result))

(definterface fn-native-operator-host-result-exit-code
  :class ::program)

(defun fn-native-operator-host-result-native-action (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-native-action result))

(definterface fn-native-operator-host-result-native-action
  :class ::program)

(defun fn-native-operator-host-result-rebind-policy (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-rebind-policy result))

(definterface fn-native-operator-host-result-rebind-policy
  :class ::program)

(defun fn-native-operator-host-result-archive-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-archive-path-octets result))

(definterface fn-native-operator-host-result-archive-path-octets
  :class ::program)

(defun fn-native-operator-host-result-import-request (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-import-request result))

(definterface fn-native-operator-host-result-import-request
  :class ::program)

(defun fn-native-operator-host-result-store-root (result)
  (declare (xargs :mode :program))
  (fn-native-config-store (fn-native-operator-result-config result)))

(definterface fn-native-operator-host-result-store-root
  :class ::program)

;; The accepted configuration also supplies next-run diagnostic policies.
(defun fn-native-operator-host-result-config (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-config result))

; STATUS/HEALTH project the accepted configuration, never run-only NIL fields.
(definterface fn-native-operator-host-result-config :class :program)

(defun fn-native-operator-host-result-arguments (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-arguments result))

(definterface fn-native-operator-host-result-arguments
  :class ::program)


(defun fn-native-operator-host-result-run-cold-resources (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-cold-resources result))

(definterface fn-native-operator-host-result-run-cold-resources
  :class ::program)

(defun fn-native-operator-host-result-run-output-resources (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-output-resources result))

(definterface fn-native-operator-host-result-run-output-resources
  :class :program)

(defun fn-native-operator-host-result-run-reclaim-live (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-reclaim-live result))

(definterface fn-native-operator-host-result-run-reclaim-live
  :class :program)

(defun fn-native-operator-host-result-run-store-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-store-octets result))

(definterface fn-native-operator-host-result-run-store-octets
  :class ::program)

(defun fn-native-operator-host-result-run-listener-host-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-listener-host-octets result))

(definterface fn-native-operator-host-result-run-listener-host-octets
  :class ::program)

(defun fn-native-operator-host-result-run-listener-port (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-listener-port result))

(definterface fn-native-operator-host-result-run-listener-port
  :class ::program)

(defun fn-native-operator-host-result-run-implicit-tls-port (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-implicit-tls-port result))

(definterface fn-native-operator-host-result-run-implicit-tls-port
  :class ::program)

(defun fn-native-operator-host-result-run-tls-cert-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-tls-cert-octets result))

(defun fn-native-operator-host-result-run-tls-key-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-tls-key-octets result))

(defun fn-native-operator-host-result-run-oncep (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-oncep result))

(definterface fn-native-operator-host-result-run-oncep
  :class ::program)

(defun fn-native-operator-host-result-run-max-connections (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-max-connections result))

(definterface fn-native-operator-host-result-run-max-connections
  :class ::program)

(defun fn-native-operator-host-result-run-auth-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-auth-path-octets result))

(definterface fn-native-operator-host-result-run-auth-path-octets
  :class ::program)

(defun fn-native-operator-host-result-run-auth-requiredp (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-auth-requiredp result))

(definterface fn-native-operator-host-result-run-auth-requiredp
  :class ::program)

(defun fn-native-operator-host-result-run-auth-protected-onlyp (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-auth-protected-onlyp result))

(definterface fn-native-operator-host-result-run-auth-protected-onlyp
  :class ::program)

(defun fn-native-operator-host-result-run-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-control-path-octets result))

(definterface fn-native-operator-host-result-run-control-path-octets
  :class ::program)

(defun fn-native-operator-host-result-run-posting-enabledp (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-posting-enabledp result))

(definterface fn-native-operator-host-result-run-posting-enabledp
  :class ::program)

(defun fn-native-operator-host-result-run-log-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-log-path-octets result))

(defun fn-native-operator-host-result-post-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-post-control-path-octets result))

(definterface fn-native-operator-host-result-post-control-path-octets
  :class ::program)

(defun fn-native-operator-host-result-moderate-request (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-moderate-request result))

(definterface fn-native-operator-host-result-moderate-request
  :class ::program)

(defun fn-native-operator-host-result-moderate-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-moderate-control-path-octets result))

(definterface fn-native-operator-host-result-moderate-control-path-octets
  :class ::program)

(defun fn-native-operator-host-result-post-msgid-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-post-msgid-octets result))

(definterface fn-native-operator-host-result-post-msgid-octets
  :class ::program)

(defun fn-native-operator-host-result-post-payload-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-post-payload-path-octets result))

(definterface fn-native-operator-host-result-post-payload-path-octets
  :class ::program)

(defun fn-native-operator-host-result-post-group-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-post-group-octets result))

(definterface fn-native-operator-host-result-post-group-octets
  :class ::program)

(defun fn-native-operator-host-result-admin-plan (result)
  "Exact accepted ACL2 native-admin plan; raw Lisp may only deliver it."
  (declare (xargs :mode :program))
  (fn-native-operator-result-admin-plan result))

(definterface fn-native-operator-host-result-admin-plan
  :class ::program)
(defun fn-native-operator-host-result-admin-argv (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-admin-argv result))

(definterface fn-native-operator-host-result-admin-argv
  :class ::program)
(defun fn-native-operator-host-result-admin-control-path-octets (result)
  (declare (xargs :mode :program))
  (if (fn-native-operator-result-admin-planp result)
      (fn-record-string-octets
       (fn-native-config-control-path (fn-native-operator-result-config result)))
    nil))

(definterface fn-native-operator-host-result-admin-control-path-octets
  :class ::program)

(defun fn-native-operator-host-result-principal-plan (result)
  "Exact accepted ACL2 credential administration plan."
  (declare (xargs :mode :program))
  (fn-native-operator-result-principal-plan result))

(definterface fn-native-operator-host-result-principal-plan
  :class ::program)

(defun fn-native-operator-host-result-principal-account-result (result)
  "PRF-388: the `account bind|unbind' result for a login the file lacks."
  (declare (xargs :mode :program))
  (fn-native-operator-result-principal-account-result result))

(definterface fn-native-operator-host-result-principal-account-result
  :class ::program)

(defun fn-native-operator-host-result-principal-auth-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-principal-auth-path-octets result))

(definterface fn-native-operator-host-result-principal-auth-path-octets
  :class ::program)

(defun fn-native-operator-host-result-principal-store-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-principal-store-octets result))

(definterface fn-native-operator-host-result-principal-store-octets
  :class ::program)

(defun fn-native-operator-host-result-principal-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-principal-control-path-octets result))

(definterface fn-native-operator-host-result-principal-control-path-octets
  :class ::program)

(defun fn-native-operator-host-init-marker-octets ()
  "The store entry names raw Lisp may lstat before an init plan runs."
  (declare (xargs :mode :program))
  (fn-native-operator-init-marker-octets))

(definterface fn-native-operator-host-init-marker-octets
  :class ::program)

(defun fn-native-operator-host-init-outcome (result observed)
  (declare (xargs :mode :program))
  (fn-native-operator-init-outcome result observed))

(definterface fn-native-operator-host-init-outcome
  :class ::program)

(defun fn-native-operator-host-result-init-profile (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-init-profile result))

(definterface fn-native-operator-host-result-init-profile
  :class ::program)

(defun fn-native-operator-host-result-init-budget (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-init-budget result))

(definterface fn-native-operator-host-result-init-budget
  :class ::program)

(defun fn-native-operator-host-result-init-sizing (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-init-sizing result))

(definterface fn-native-operator-host-result-init-sizing
  :class ::program)

(defun fn-native-operator-host-result-config-mission (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-config-mission result))

(definterface fn-native-operator-host-result-config-mission
  :class ::program)

(defun fn-native-operator-host-result-init-group-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-init-group-octets result))

(definterface fn-native-operator-host-result-init-group-octets
  :class ::program)

(defun fn-native-operator-host-result-status-kind (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-status-kind result))

(definterface fn-native-operator-host-result-status-kind
  :class ::program)
(defun fn-native-operator-host-result-status-watch (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-status-watch result))

(definterface fn-native-operator-host-result-status-watch
  :class ::program)
(defun fn-native-operator-host-result-status-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-status-control-path-octets result))

(definterface fn-native-operator-host-result-status-control-path-octets
  :class ::program)
(defun fn-native-operator-host-result-status-log-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-status-log-path-octets result))

(definterface fn-native-operator-host-result-status-log-path-octets
  :class ::program)
(defun fn-native-operator-host-result-health-min-percent (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-health-min-percent result))

(definterface fn-native-operator-host-result-health-min-percent
  :class ::program)

;; PKT-096 and PKT-097.
(defun fn-native-operator-host-preflight-needs-config-path-p (result)
  (declare (xargs :mode :program))
  (fn-native-operator-preflight-needs-config-path-p result))

(definterface fn-native-operator-host-preflight-needs-config-path-p
  :class ::program)

(defun fn-native-operator-host-mission-run (path-octets argv-octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp path-octets)))
  (fn-native-operator-mission-run path-octets argv-octets))

(definterface fn-native-operator-host-mission-run
  :class :program
  :kinds ((path-octets fn-cbor-octet-listp))
  :exempt ((argv-octets "a list of argument octet lists, preflighted by fn-native-operator-host-preflight")))

(defun fn-native-operator-host-mission-outcome (result existsp)
  (declare (xargs :mode :program))
  (fn-native-operator-mission-outcome result existsp))

(definterface fn-native-operator-host-mission-outcome
  :class ::program)

(defun fn-native-operator-host-result-mission-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-mission-octets result))

(definterface fn-native-operator-host-result-mission-octets
  :class ::program)

(defun fn-native-operator-host-result-mission-directory-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-mission-directory-octets result))

(definterface fn-native-operator-host-result-mission-directory-octets
  :class ::program)

(defun fn-native-operator-host-result-show-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-show-octets result))

(definterface fn-native-operator-host-result-show-octets
  :class ::program)

(defun fn-native-operator-host-store-outcome (result observed init-stage import-stage)
  (declare (xargs :mode :program))
  (fn-nsst-store-outcome result observed init-stage import-stage))

(definterface fn-native-operator-host-store-outcome
  :class ::program)

(defun fn-native-operator-host-control-outcome (result)
  (declare (xargs :mode :program))
  (fn-native-operator-control-outcome result))

(definterface fn-native-operator-host-control-outcome
  :class ::program)

(defun fn-native-operator-host-result-hint (result)
  (declare (xargs :mode :program))
  (fn-nsst-result-hint result))

(definterface fn-native-operator-host-result-hint
  :class ::program)

(defun fn-native-operator-host-result-inspect-msgid-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-inspect-msgid-octets result))

(definterface fn-native-operator-host-result-inspect-msgid-octets
  :class ::program)

; Row S3d: the group `store inspect --group GROUP' names, or nil.
(defun fn-native-operator-host-result-inspect-group (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-inspect-group result))

(definterface fn-native-operator-host-result-inspect-group
  :class ::program)

(defun fn-native-operator-host-inspect-report (msgid-octets foundp)
  (declare (xargs :mode :program))
  (fn-native-operator-inspect-report msgid-octets foundp))

(definterface fn-native-operator-host-inspect-report
  :class :program
  :exempt ((msgid-octets "the host passes a LIST of Message-IDs (msgid-list); the name is historical")))

;; PKT-597, PKT-786: `account hash LOGIN' (host/native/operator.lisp): the
;; login the plan admitted, the credential file it reads, and the value ACL2
;; computes from the node secret and the credential file the host read
;; (books/native-operator.lisp fn-nop-account-hash: LOGIN's account, then its
;; posting-account value), as text; nil when the octets the host read are not
;; a node secret, :credential-file-refused when the owner's load refuses the
;; credential file.
(defun fn-native-operator-host-result-account-hash-login (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-account-hash-login result))

(definterface fn-native-operator-host-result-account-hash-login
  :class ::program)
(defun fn-native-operator-host-result-account-hash-auth-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-account-hash-auth-path-octets result))

; host/native/operator.lisp dispatches it (lane correctness-remainder-3).
(definterface fn-native-operator-host-result-account-hash-auth-path-octets
  :class ::program)
(defun fn-native-operator-host-account-hash-text (secret login octets presentp
                                                         max-credentials)
  (declare (xargs :mode :program :guard (fn-cbor-octet-listp octets)))
  (cond ((not (and (fn-ns-ringp secret) (fn-ipp-login-wordp login))) nil)
        ((fn-nop-account-hash secret login octets presentp max-credentials)
         (fn-record-octets-string
          (fn-nop-account-hash secret login octets presentp max-credentials)))
        (t :credential-file-refused)))

(definterface fn-native-operator-host-account-hash-text
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

;; PRF-164: `account invite' (host/native/operator.lisp).
(defun fn-native-operator-host-result-account-invite-seconds (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-account-invite-seconds result))

(definterface fn-native-operator-host-result-account-invite-seconds
  :class ::program)
(defun fn-native-operator-host-result-account-control-path-octets (result)
  (declare (xargs :mode :program))
  (if (fn-native-operator-result-account-invite-seconds result)
      (fn-record-string-octets
       (fn-native-config-control-path (fn-native-operator-result-config result)))
    nil))

(definterface fn-native-operator-host-result-account-control-path-octets
  :class ::program)

; `tls reload' (PRF-212): the control socket host/native/tls-reload.lisp asks.
(defun fn-native-operator-host-result-tls-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-tls-control-path-octets result))

(definterface fn-native-operator-host-result-tls-control-path-octets
  :class ::program)

;; Row Q10a: the self-signed pair (books/tls-self-signed.lisp).  The host
;; generates the key, reads sixteen random octets and the wall clock, signs
;; the body ACL2 renders and writes the two PEM files ACL2 renders.
(defun fn-native-operator-host-result-self-signed (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-self-signed result))

(definterface fn-native-operator-host-result-self-signed
  :class :program)

(defun fn-native-operator-host-self-signed-outcome (result cert-exists key-exists)
  (declare (xargs :mode :program))
  (fn-native-operator-self-signed-outcome result cert-exists key-exists))

(definterface fn-native-operator-host-self-signed-outcome
  :class :program
  :exempt ((cert-exists "the host's lstat of tls_cert, a boolean ACL2 reads as observed")
           (key-exists "the host's lstat of tls_key, a boolean ACL2 reads as observed")))

(defun fn-tls-self-signed-host-plan (names days now-ms has-wall serial spki)
  (declare (xargs :mode :program
                  :guard (and (fn-cbor-octet-listp serial) (fn-cbor-octet-listp spki))))
  (fn-ssc-plan names days now-ms has-wall serial spki))

(definterface fn-tls-self-signed-host-plan
  :class :program
  :kinds ((serial fn-cbor-octet-listp) (spki fn-cbor-octet-listp))
  :exempt ((names "ACL2's own names from fn-native-operator-host-result-self-signed, handed back unchanged; fn-ssc-plan refuses a bad one by name")
           (days "ACL2's own days from the same request")
           (now-ms "the wall reading fn-otm-wall-reading returned")
           (has-wall "the wall reading's usable flag; fn-ssc-plan refuses :clock without it"))
  :keystones ((fn-ssc-plan-body-is-one-sequence :via fn-ssc-plan)))

(defun fn-tls-self-signed-host-serial-octets ()
  (declare (xargs :mode :program))
  *fn-ssc-serial-octets*)

(definterface fn-tls-self-signed-host-serial-octets
  :class :program)

(defun fn-tls-self-signed-host-certificate-pem (tbs sig)
  (declare (xargs :mode :program
                  :guard (and (fn-cbor-octet-listp tbs) (fn-cbor-octet-listp sig))))
  (fn-ssc-certificate-pem tbs sig))

(definterface fn-tls-self-signed-host-certificate-pem
  :class :program
  :kinds ((tbs fn-cbor-octet-listp) (sig fn-cbor-octet-listp))
  :keystones ((fn-ssc-certificate-pem-carries-the-body :via fn-ssc-certificate-pem)))

(defun fn-tls-self-signed-host-key-pem (der)
  (declare (xargs :mode :program :guard (fn-cbor-octet-listp der)))
  (fn-ssc-key-pem der))

(definterface fn-tls-self-signed-host-key-pem
  :class :program
  :kinds ((der fn-cbor-octet-listp))
  :keystones ((fn-ssc-key-pem-carries-the-key :via fn-ssc-key-pem)))

(defun fn-native-operator-host-self-signed-refused (result reason)
  (declare (xargs :mode :program))
  (fn-native-operator-self-signed-refused result reason))

(definterface fn-native-operator-host-self-signed-refused
  :class :program
  :exempt ((reason "the refusal word fn-tls-self-signed-host-plan or -pem returned; any other value is refused as :self-signed")))
