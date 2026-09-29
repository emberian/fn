; ACL2-facing native operator boundary.
;
; The raw image is allowed to make bounded file/argv byte vectors and emit the
; returned tagged result.  It does not parse a command, choose defaults, or
; assign an exit code: fn-native-operator-run owns all three.
(in-package "ACL2")
(include-book "../books/native-operator")
; Row S3 (lane operability-2): maintenance verbs on the running owner, the
; stopped store's status from its checkpoint header.
(include-book "../books/owner-maintenance-request")

(defun fn-native-operator-host-preflight (argv-octets)
  (declare (xargs :mode :program))
  (fn-native-operator-command-preflight argv-octets))

(defun fn-native-operator-host-preflight-needs-config-p (result)
  (declare (xargs :mode :program))
  (fn-native-operator-preflight-needs-config-p result))

(defun fn-native-operator-host-run (config-octets argv-octets)
  (declare (xargs :mode :program))
  (fn-native-operator-run config-octets argv-octets))

(defun fn-native-operator-host-result-carry-fields (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-carry-fields result))

(defun fn-native-operator-host-result-compaction-argv (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-compaction-argv result))

(defun fn-native-operator-host-result-compaction-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-compaction-control-path-octets result))

(defun fn-native-operator-host-result-reclaim-argv (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-reclaim-argv result))

(defun fn-native-operator-host-result-reclaim-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-reclaim-control-path-octets result))

(defun fn-native-operator-host-result-status (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-status result))

(defun fn-native-operator-host-result-reason (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-reason result))

(defun fn-native-operator-host-result-command (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-command result))

(defun fn-native-operator-host-result-exit-code (result)
  (declare (xargs :mode :program))
  (fn-native-operator-exit-code result))

(defun fn-native-operator-host-result-native-action (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-native-action result))

(defun fn-native-operator-host-result-rebind-policy (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-rebind-policy result))

(defun fn-native-operator-host-result-archive-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-archive-path-octets result))

(defun fn-native-operator-host-result-import-request (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-import-request result))

(defun fn-native-operator-host-result-store-root (result)
  (declare (xargs :mode :program))
  (fn-native-config-store (fn-native-operator-result-config result)))

;; test-only (tools/host_callers.py): tests/acl2/native-operator-host-tests.lisp
(defun fn-native-operator-host-result-config (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-config result))

(defun fn-native-operator-host-result-arguments (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-arguments result))


(defun fn-native-operator-host-result-run-store-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-store-octets result))

(defun fn-native-operator-host-result-run-listener-host-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-listener-host-octets result))

(defun fn-native-operator-host-result-run-listener-port (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-listener-port result))

(defun fn-native-operator-host-result-run-implicit-tls-port (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-implicit-tls-port result))

(defun fn-native-operator-host-result-run-tls-cert-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-tls-cert-octets result))

(defun fn-native-operator-host-result-run-tls-key-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-tls-key-octets result))

(defun fn-native-operator-host-result-run-oncep (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-oncep result))

(defun fn-native-operator-host-result-run-max-connections (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-max-connections result))

(defun fn-native-operator-host-result-run-auth-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-auth-path-octets result))

(defun fn-native-operator-host-result-run-auth-requiredp (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-auth-requiredp result))

(defun fn-native-operator-host-result-run-auth-protected-onlyp (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-auth-protected-onlyp result))

(defun fn-native-operator-host-result-run-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-control-path-octets result))

(defun fn-native-operator-host-result-run-posting-enabledp (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-posting-enabledp result))

(defun fn-native-operator-host-result-run-log-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-run-log-path-octets result))

(defun fn-native-operator-host-result-post-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-post-control-path-octets result))

(defun fn-native-operator-host-result-moderate-request (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-moderate-request result))

(defun fn-native-operator-host-result-moderate-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-moderate-control-path-octets result))

(defun fn-native-operator-host-result-post-msgid-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-post-msgid-octets result))

(defun fn-native-operator-host-result-post-payload-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-post-payload-path-octets result))

(defun fn-native-operator-host-result-post-group-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-post-group-octets result))

(defun fn-native-operator-host-result-admin-plan (result)
  "Exact accepted ACL2 native-admin plan; raw Lisp may only deliver it."
  (declare (xargs :mode :program))
  (fn-native-operator-result-admin-plan result))
(defun fn-native-operator-host-result-admin-argv (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-admin-argv result))
(defun fn-native-operator-host-result-admin-control-path-octets (result)
  (declare (xargs :mode :program))
  (if (fn-native-operator-result-admin-planp result)
      (fn-record-string-octets
       (fn-native-config-control-path (fn-native-operator-result-config result)))
    nil))

(defun fn-native-operator-host-result-principal-plan (result)
  "Exact accepted ACL2 credential administration plan."
  (declare (xargs :mode :program))
  (fn-native-operator-result-principal-plan result))

(defun fn-native-operator-host-result-principal-account-result (result)
  "PRF-388: the `account bind|unbind' result for a login the file lacks."
  (declare (xargs :mode :program))
  (fn-native-operator-result-principal-account-result result))

(defun fn-native-operator-host-result-principal-auth-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-principal-auth-path-octets result))

(defun fn-native-operator-host-result-principal-store-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-principal-store-octets result))

(defun fn-native-operator-host-result-principal-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-principal-control-path-octets result))

(defun fn-native-operator-host-init-marker-octets ()
  "The store entry names raw Lisp may lstat before an init plan runs."
  (declare (xargs :mode :program))
  (fn-native-operator-init-marker-octets))

(defun fn-native-operator-host-init-outcome (result observed)
  (declare (xargs :mode :program))
  (fn-native-operator-init-outcome result observed))

(defun fn-native-operator-host-result-init-profile (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-init-profile result))

(defun fn-native-operator-host-result-config-mission (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-config-mission result))

(defun fn-native-operator-host-result-init-group-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-init-group-octets result))

(defun fn-native-operator-host-result-status-kind (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-status-kind result))
(defun fn-native-operator-host-result-status-watch (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-status-watch result))
(defun fn-native-operator-host-result-status-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-status-control-path-octets result))
(defun fn-native-operator-host-result-status-log-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-status-log-path-octets result))
(defun fn-native-operator-host-result-health-min-percent (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-health-min-percent result))

;; PKT-096 and PKT-097.
(defun fn-native-operator-host-preflight-needs-config-path-p (result)
  (declare (xargs :mode :program))
  (fn-native-operator-preflight-needs-config-path-p result))

(defun fn-native-operator-host-mission-run (path-octets argv-octets)
  (declare (xargs :mode :program
                  :guard (fn-cbor-octet-listp path-octets)))
  (fn-native-operator-mission-run path-octets argv-octets))

(defun fn-native-operator-host-mission-outcome (result existsp)
  (declare (xargs :mode :program))
  (fn-native-operator-mission-outcome result existsp))

(defun fn-native-operator-host-result-mission-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-mission-octets result))

(defun fn-native-operator-host-result-mission-directory-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-mission-directory-octets result))

(defun fn-native-operator-host-result-show-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-show-octets result))

(defun fn-native-operator-host-store-outcome (result observed)
  (declare (xargs :mode :program))
  (fn-native-operator-store-outcome result observed))

(defun fn-native-operator-host-control-outcome (result)
  (declare (xargs :mode :program))
  (fn-native-operator-control-outcome result))

(defun fn-native-operator-host-result-hint (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-hint result))

(defun fn-native-operator-host-result-inspect-msgid-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-inspect-msgid-octets result))

; Row S3d: the group `store inspect --group GROUP' names, or nil.
(defun fn-native-operator-host-result-inspect-group (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-inspect-group result))

(defun fn-native-operator-host-inspect-report (msgid-octets foundp)
  (declare (xargs :mode :program))
  (fn-native-operator-inspect-report msgid-octets foundp))

;; PKT-597: `account hash LOGIN' (host/native/operator.lisp): the login the
;; plan admitted, and the value ACL2 computes from the node secret the host
;; read (books/injection-info-policy.lisp fn-ipp-account-hash), as text;
;; nil when the octets the host read are not a node secret.
(defun fn-native-operator-host-result-account-hash-login (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-account-hash-login result))
(defun fn-native-operator-host-account-hash-text (secret login)
  (declare (xargs :mode :program))
  (if (and (fn-ns-ringp secret) (fn-ipp-login-wordp login))
      (fn-record-octets-string (fn-ipp-account-hash secret login))
    nil))

;; PRF-164: `account invite' (host/native/operator.lisp).
(defun fn-native-operator-host-result-account-invite-seconds (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-account-invite-seconds result))
(defun fn-native-operator-host-result-account-control-path-octets (result)
  (declare (xargs :mode :program))
  (if (fn-native-operator-result-account-invite-seconds result)
      (fn-record-string-octets
       (fn-native-config-control-path (fn-native-operator-result-config result)))
    nil))

; `tls reload' (PRF-212): the control socket host/native/tls-reload.lisp asks.
(defun fn-native-operator-host-result-tls-control-path-octets (result)
  (declare (xargs :mode :program))
  (fn-native-operator-result-tls-control-path-octets result))
