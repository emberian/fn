; ACL2-facing native operator boundary.
;
; The raw image is allowed to make bounded file/argv byte vectors and emit the
; returned tagged result.  It does not parse a command, choose defaults, or
; assign an exit code: fn-native-operator-run owns all three.
(in-package "ACL2")
; D61: the image attaches these (attach-stobj) before the generic they implement;
; a certified host file carries the same order in its own world (tools/host_check.py --attach-order).
(include-book "../books/payload-arena")
(include-book "../books/history-columns")
(include-book "../books/native-operator")
(include-book "../books/native-operator-stage")

; Row S3 (lane operability-2): maintenance verbs on the running owner, the
; stopped store's status from its checkpoint header.
(include-book "../books/owner-maintenance-request")
(include-book "../books/definterface")

(include-book "../books/entries-native-operator-host")

(definterface fn-native-operator-host-preflight
  :class :program
  :exempt ((argv-octets "the argv preflight is the check: it refuses a malformed argv by name")))

(definterface fn-native-operator-host-preflight-needs-config-p
  :class ::program)

(definterface fn-native-operator-host-run-at
  :class :program
  :kinds ((cwd fn-cbor-octet-listp) (config-path fn-cbor-octet-listp))
  :exempt ((argv-octets "a list of argument octet lists, preflighted (fn-native-operator-host-preflight)")
           (config-octets "read by fnn-operator-read-config, bounded; NIL when absent")))

(definterface fn-native-operator-host-result-carry-fields
  :class ::program)

;; Row S9: `retire' (books/native-retire.lisp).

; Actual retire CLI projection consumed before observation starts.
(definterface fn-native-operator-host-result-retire-argv :class :program)

(definterface fn-native-operator-host-result-retire-control-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-status
  :class ::program)

(definterface fn-native-operator-host-result-reason
  :class ::program)

(definterface fn-native-operator-host-result-command
  :class ::program)

(definterface fn-native-operator-host-result-exit-code
  :class ::program)

(definterface fn-native-operator-host-result-native-action
  :class ::program)

(definterface fn-native-operator-host-result-rebind-policy
  :class ::program)

(definterface fn-native-operator-host-result-archive-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-import-request
  :class ::program)

(defun fn-native-operator-host-result-store-root (result)
  (declare (xargs :mode :program))
  (fn-native-config-store (fn-native-operator-result-config result)))

(definterface fn-native-operator-host-result-store-root
  :class ::program)

;; The accepted configuration also supplies next-run diagnostic policies.

; STATUS/HEALTH project the accepted configuration, never run-only NIL fields.
(definterface fn-native-operator-host-result-config :class :program)

(definterface fn-native-operator-host-result-arguments
  :class ::program)


(definterface fn-native-operator-host-result-run-cold-resources
  :class ::program)

(definterface fn-native-operator-host-result-run-output-resources
  :class :program)

(definterface fn-native-operator-host-result-run-reclaim-live
  :class :program)

(definterface fn-native-operator-host-result-run-store-octets
  :class ::program)

(definterface fn-native-operator-host-result-run-listener-host-octets
  :class ::program)

(definterface fn-native-operator-host-result-run-listener-port
  :class ::program)

(definterface fn-native-operator-host-result-run-implicit-tls-port
  :class ::program)

(definterface fn-native-operator-host-result-run-oncep
  :class ::program)

(definterface fn-native-operator-host-result-run-max-connections
  :class ::program)

(definterface fn-native-operator-host-result-run-auth-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-run-auth-requiredp
  :class ::program)

(definterface fn-native-operator-host-result-run-auth-protected-onlyp
  :class ::program)

(definterface fn-native-operator-host-result-run-control-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-run-posting-enabledp
  :class ::program)

(definterface fn-native-operator-host-result-post-control-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-moderate-request
  :class ::program)

(definterface fn-native-operator-host-result-moderate-control-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-post-msgid-octets
  :class ::program)

(definterface fn-native-operator-host-result-post-payload-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-post-group-octets
  :class ::program)

(definterface fn-native-operator-host-result-admin-plan
  :class ::program)

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

(definterface fn-native-operator-host-result-principal-plan
  :class ::program)

(definterface fn-native-operator-host-result-principal-account-result
  :class ::program)

(definterface fn-native-operator-host-result-principal-auth-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-principal-store-octets
  :class ::program)

(definterface fn-native-operator-host-result-principal-control-path-octets
  :class ::program)

(definterface fn-native-operator-host-init-marker-octets
  :class ::program)

(definterface fn-native-operator-host-init-outcome
  :class ::program)

(definterface fn-native-operator-host-result-init-profile
  :class ::program)

(definterface fn-native-operator-host-result-init-budget
  :class ::program)

(definterface fn-native-operator-host-result-init-sizing
  :class ::program)

(definterface fn-native-operator-host-result-config-mission
  :class ::program)

(definterface fn-native-operator-host-result-init-group-octets
  :class ::program)

(definterface fn-native-operator-host-result-status-kind
  :class ::program)

(definterface fn-native-operator-host-result-status-watch
  :class ::program)

(definterface fn-native-operator-host-result-status-control-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-status-log-path-octets
  :class ::program)

(definterface fn-native-operator-host-result-health-min-percent
  :class ::program)

;; PKT-096 and PKT-097.

(definterface fn-native-operator-host-preflight-needs-config-path-p
  :class ::program)

(definterface fn-native-operator-host-mission-run
  :class :program
  :kinds ((path-octets fn-cbor-octet-listp))
  :exempt ((argv-octets "a list of argument octet lists, preflighted by fn-native-operator-host-preflight")))

(definterface fn-native-operator-host-mission-outcome
  :class ::program)

(definterface fn-native-operator-host-result-mission-octets
  :class ::program)

(definterface fn-native-operator-host-result-mission-directory-octets
  :class ::program)

(definterface fn-native-operator-host-result-show-octets
  :class ::program)

(definterface fn-native-operator-host-store-outcome
  :class ::program)

(definterface fn-native-operator-host-control-outcome
  :class ::program)

(definterface fn-native-operator-host-result-hint
  :class ::program)

(definterface fn-native-operator-host-result-inspect-msgid-octets
  :class ::program)

; Row S3d: the group `store inspect --group GROUP' names, or nil.

(definterface fn-native-operator-host-result-inspect-group
  :class ::program)

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

(definterface fn-native-operator-host-result-account-hash-login
  :class ::program)

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

(definterface fn-native-operator-host-result-tls-control-path-octets
  :class ::program)

;; Row Q10a: the self-signed pair (books/tls-self-signed.lisp).  The host
;; generates the key, reads sixteen random octets and the wall clock, signs
;; the body ACL2 renders and writes the two PEM files ACL2 renders.

(definterface fn-native-operator-host-result-self-signed
  :class :program)

(definterface fn-native-operator-host-self-signed-outcome
  :class :program)

(definterface fn-tls-self-signed-host-plan
  :class :program
  :kinds ((serial fn-cbor-octet-listp) (spki fn-cbor-octet-listp))
  :keystones ((fn-ssc-plan-body-is-one-sequence :via fn-ssc-plan)))

(defun fn-tls-self-signed-host-serial-octets ()
  (declare (xargs :mode :program))
  *fn-ssc-serial-octets*)

(definterface fn-tls-self-signed-host-serial-octets
  :class :program)

(definterface fn-tls-self-signed-host-certificate-pem
  :class :program
  :kinds ((tbs fn-cbor-octet-listp) (sig fn-cbor-octet-listp))
  :keystones ((fn-ssc-certificate-pem-carries-the-body :via fn-ssc-certificate-pem)))

(definterface fn-tls-self-signed-host-key-pem
  :class :program
  :kinds ((der fn-cbor-octet-listp))
  :keystones ((fn-ssc-key-pem-carries-the-key :via fn-ssc-key-pem)))

(definterface fn-native-operator-host-self-signed-refused
  :class :program)
