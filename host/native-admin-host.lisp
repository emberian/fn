; Program bridge for the native administrative plan.
(in-package "ACL2")
(include-book "../books/native-admin")
(include-book "../books/accounts")
(ld "store-node-host.lisp" :ld-error-action :error)
(ld "owner-host.lisp" :ld-error-action :error)

(defun fn-native-admin-host-plan (argv) (fn-native-admin-plan argv))
(defun fn-native-admin-host-status (result) (fn-native-admin-result-status result))
(defun fn-native-admin-host-reason (result) (fn-native-admin-result-reason result))
(defun fn-native-admin-host-queryp (result) (fn-native-admin-result-queryp result))
(defun fn-native-admin-host-owner-requestp (result)
  (fn-native-admin-result-owner-requestp result))
(defun fn-native-admin-host-reclaim-mode (result)
  (fn-native-admin-result-reclaim-mode result))
(defun fn-native-admin-host-report-kind (result)
  (fn-native-admin-result-report-kind result))
(defun fn-native-admin-host-query-report (plan state)
  ; `peer list' or `control list' over the configuration the store just
  ; replayed; books/native-admin.lisp selects and renders.
  (declare (xargs :stobjs state :mode :program))
  (value (fn-native-admin-query-report
          plan (fn-cfg-value (f-get-global 'fn-store-cfg state)))))
(defun fn-native-admin-host-owner-reconfigure (id plan fn-arena state)
  ; The live arm.  The delta list, labels as strings, is ACL2's
  ; (`fn-native-admin-plan-deltas', books/native-admin.lisp); this bridge
  ; only hands it to the owner's staging step.
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  ; PRF-099: an :extend-peer plan's delta is built over the live owner's
  ; peer table (`fn-native-admin-plan-deltas-over').
  ;; PRF-164: an `account invite' plan's pending row expires from the live
  ;; owner's clock, a milliseconds reading (fn-acct-admin-deltas,
  ;; fn-acct-live-invite-reading; PRF-374).
  (let ((deltas (if (equal (fn-native-admin-result-kind plan) :account-invite)
                    (fn-acct-admin-deltas
                     plan (fn-acct-live-invite-reading
                           (fn-own-clock (fn-owner-core state))))
                  (fn-native-admin-plan-deltas-over
                   plan (fn-cfg-peers (fn-cfg-value (fn-owner-config state)))))))
    (cond
     ;; PRF-388 (PKT-560): `account bind|unbind' is planned over the live
     ;; owner's configuration (books/login-binding-live.lisp
     ;; fn-lb-account-bind-plan): its record, or a refusal by name.
     ((equal (fn-native-admin-result-kind plan) :account-bind)
      (let ((account-plan (fn-lb-account-bind-plan
                           (fn-native-admin-result-name plan)
                           (fn-native-admin-result-value plan)
                           (fn-cfg-value (fn-owner-config state)))))
        (if (equal (car account-plan) :ok)
            (fn-owner-reconfigure-deltas id (cadr account-plan) fn-arena state)
          (value (fn-ores-config-refused (cadr account-plan))))))
     ;; PKT-709: a bind of a consumer name no registration declared is
     ;; refused by name (books/consumer-owner-local.lisp fn-col-bind-refusal).
     ((and (equal (fn-native-admin-result-kind plan) :consumer-bind)
           (fn-col-bind-refusal (fn-sn-consumer (fn-own-store (fn-owner-core state)))
                                (fn-native-admin-result-name plan)
                                (fn-native-admin-result-value plan)))
      (value (fn-ores-config-refused
              (fn-col-bind-refusal (fn-sn-consumer (fn-own-store (fn-owner-core state)))
                                   (fn-native-admin-result-name plan)
                                   (fn-native-admin-result-value plan)))))
     (deltas
      (fn-owner-reconfigure-deltas id deltas fn-arena state))
     ;; No delta for this plan over the live owner's tables: the result
     ;; says so, never a previous request's reason (PKT-453 (a)).
     ;; Row S5: `peer set''s refusal over the live record, or
     ;; :no-such-peer, by ACL2's name (fn-native-admin-plan-refusal-over).
     (t (value (fn-ores-config-refused
                (fn-native-admin-plan-refusal-over
                 plan (fn-cfg-peers (fn-cfg-value (fn-owner-config state))))))))))
(defun fn-native-admin-host-apply (plan stamp state)
  ;; STAMP is the record stamp fn-native-admin-clock-observation built
  ;; (host/native/admin.lisp fnn-admin-clock-plan); every record this
  ;; builds carries it unchanged (PRF-378, PRF-379).
  (declare (xargs :stobjs state :mode :program))
  (let ((kind (fn-native-admin-result-kind plan)))
    (cond ;; PRF-388 (PKT-560): offline, `account bind|unbind' over the
          ;; opened Store's configuration (fn-lb-account-bind-plan).
          ((equal kind :account-bind)
           (let ((account-plan (fn-lb-account-bind-plan
                                (fn-native-admin-result-name plan)
                                (fn-native-admin-result-value plan)
                                (fn-cfg-value (f-get-global 'fn-store-cfg state)))))
             (if (equal (car account-plan) :ok)
                 (fn-store-cfg-peer-delta-record (cadr account-plan) stamp state)
               (let ((state (f-put-global 'fn-store-cfg-last-reason
                                          (cadr account-plan) state)))
                 (value :refused)))))
          ;; PKT-709: offline, a bind of an unregistered consumer name is
          ;; refused by name over the opened Store (fn-col-bind-refusal).
          ((and (equal kind :consumer-bind)
                (fn-col-bind-refusal (fn-sn-consumer (f-get-global 'fn-store-sn state))
                                     (fn-native-admin-result-name plan)
                                     (fn-native-admin-result-value plan)))
           (let ((state (f-put-global
                         'fn-store-cfg-last-reason
                         (fn-col-bind-refusal (fn-sn-consumer (f-get-global 'fn-store-sn state))
                                              (fn-native-admin-result-name plan)
                                              (fn-native-admin-result-value plan))
                         state)))
             (value :refused)))
          ((member-equal kind '(:set-bp-boundary :set-bp-route :remove-bp-route
                                :grant-control :revoke-control :set-retention
                                ;; Q14: a group's expiry policy (quota rows).
                                :set-expiry
                                ;; PRF-161: an exposure limit row.
                                :set-exposure
                                ;; PRF-235/236: a transit hygiene limit row.
                                :set-transit-limit
                                ;; O2: a group's LIST ACTIVE status.
                                :set-group-status
                                ;; P3: a group's moderation (code 23).
                                :set-group-moderation
                                ;; PRF-195: a description or the message.
                                :set-group-description :set-motd
                                ;; PRF-222: a login's group access.
                                :account-access
                                ;; public-node-2: an account's deletion.
                                :account-delete
                                ;; PRF-234: a consumer's account binding.
                                :consumer-bind
                                ;; PRF-243: the default subscription list.
                                :set-default-subscriptions
                                ;; PKT-575: the operator's withdrawal row.
                                :withdraw-article))
           (fn-store-cfg-peer-delta-record
            (fn-native-admin-plan-deltas plan) stamp state))
          ; PRF-099: `peer carries' / `peer budget' over the replayed table.
          ((equal kind :extend-peer)
           (let ((deltas (fn-native-admin-plan-deltas-over
                          plan (fn-cfg-peers
                                (fn-cfg-value (f-get-global 'fn-store-cfg state))))))
             (if deltas
                 (fn-store-cfg-peer-delta-record deltas stamp state)
               (let ((state (f-put-global 'fn-store-cfg-last-reason
                                          (fn-native-admin-plan-refusal-over
                                           plan (fn-cfg-peers
                                                 (fn-cfg-value
                                                  (f-get-global 'fn-store-cfg state))))
                                          state)))
                 (value :refused)))))
          ;; PRF-164: offline, the pending row expires from the record's
          ;; own stamp, the observation fn-store-cfg-peer-delta-record
          ;; writes (milliseconds, PRF-378).  PRF-379: a stamp with no wall
          ;; claim refuses by name (fn-acct-offline-invite-refusal), never
          ;; a code born expired.
          ((equal kind :account-invite)
           (let ((refusal (fn-acct-offline-invite-refusal plan stamp)))
             (if refusal
                 (let ((state (f-put-global 'fn-store-cfg-last-reason refusal
                                            state)))
                   (value :refused))
               (fn-store-cfg-peer-delta-record
                (fn-acct-admin-deltas plan (fn-acct-offline-invite-reading stamp))
                stamp state))))
          ((equal kind :set-peer)
           (fn-store-cfg-peer-delta-record
            (list (fn-native-admin-set-peer-delta plan))
            stamp state))
          ((equal kind :remove-peer)
           (fn-store-cfg-remove-peer (fn-native-admin-result-name plan)
                                     stamp state))
          ((equal kind :set-policy)
           (fn-store-cfg-set-policy (fn-native-admin-result-name plan)
                                    (fn-native-admin-result-value plan)
                                    stamp state))
          (t (fn-store-cfg-reconfigure
              kind (fn-native-admin-result-name plan)
              (fn-native-admin-result-capacity plan)
              stamp state)))))
(defun fn-native-admin-host-config-name (generation)
  (fn-native-admin-config-name generation))
(defun fn-native-admin-host-clock-observation (monotonic wall has-wall)
  (fn-native-admin-clock-observation monotonic wall has-wall))
(defun fn-native-admin-host-clock-status (result)
  (fn-native-admin-clock-status result))
(defun fn-native-admin-host-clock-stamp (result)
  (fn-native-admin-clock-stamp result))
(defun fn-native-admin-host-publication-status (result)
  (fn-native-admin-publication-status result))
(defun fn-native-admin-host-publication-reason (result)
  (fn-native-admin-publication-reason result))
(defun fn-native-admin-host-publication-generation (result)
  (fn-native-admin-publication-generation result))
(defun fn-native-admin-host-publication-name (result)
  (fn-native-admin-publication-name result))
(defun fn-native-admin-host-publication-jpub (result)
  (fn-native-admin-publication-jpub result))

;;; ---------------------------------------------------------------------
;;; Invitation-code accounts (PRF-164, PKT-439).  Every decision is
;;; books/accounts.lisp's and books/nntp-auth.lisp's; these name them.

;; The operator's side: the code's text from the host's CSPRNG octets, its
;; digest, and the digest-only admin argv.  The code is never an argument.
(defun fn-acct-host-entropy-octets () *fn-acct-code-entropy-octets*)
(defun fn-acct-host-salt-octets () *fn-authsec-salt-octets*)
(defun fn-acct-host-code-text (entropy) (fn-acct-code-text entropy))
(defun fn-acct-host-code-digest-text (code-octets)
  (declare (xargs :guard (fn-cbor-octet-listp code-octets) :verify-guards nil))
  (fn-acct-code-digest-text code-octets))
(defun fn-acct-host-invite-argv (digest seconds)
  (list (fn-record-string-octets "account")
        (fn-record-string-octets "invite")
        (fn-record-string-octets digest)
        (fn-record-string-octets (fn-acct-decimal-text seconds))))

;; The owner's side.  Whether connection ID holds for an XREDEEM
;; (books/nntp-auth.lisp fn-auth-redeem-waitp).
(defun fn-acct-host-owner-redeem-waitingp (id state)
  (declare (xargs :stobjs state :mode :program))
  (let ((conn (fn-own-find-conn id (fn-own-conns (fn-owner-core state)))))
    (value (and conn (fn-auth-redeem-waitp (fn-own-conn-session conn)) t))))

;; The stage fnn-owner-live-reconfigure-locked runs under the owner mutex:
;; the bounded plan over the LIVE configuration value, at the owner's clock,
;; with the request the holding session keeps, the host's salt, the
;; connection-independent credential table (auth.toml's rows, then the
;; redeemed rows: fn-auth-config-with-accounts) and the profile's
;; max-credentials BOUND.  Only a :redeem plan stages its one delta.
(defun fn-acct-host-owner-redeem-stage (pcid id salt bound fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (let* ((conn (fn-own-find-conn id (fn-own-conns (fn-owner-core state))))
         (req (and conn (fn-auth-redeem-waitp (fn-own-conn-session conn))
                   (fn-auth-redeem-request (fn-own-conn-session conn))))
         (v (fn-cfg-value (fn-owner-config state)))
         (creds (fn-auth-config-creds
                 (fn-auth-config-with-accounts (fn-owner-auth state) v)))
         (plan (if (and (true-listp req) (equal (len req) 3))
                   (fn-acct-redeem-bounded-plan
                    v (fn-own-clock (fn-owner-core state))
                    (first req) (second req) (third req) salt
                    (and (fn-auth-find-cred (second req) creds) t)
                    (len creds) bound)
                 (list :refused :account-no-request)))
         (state (f-put-global 'fn-acct-redeem-plan plan state)))
    (if (equal (car plan) :redeem)
        (fn-owner-reconfigure-deltas pcid (list (fn-acct-plan-delta plan))
                                     fn-arena state)
      ;; The plan's own reason (a previous request's reason used to stand
      ;; in the retired reason slot here).
      (value (fn-ores-config-refused (cadr plan))))))

(defun fn-acct-host-owner-redeem-word (published state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-acct-redeem-word (f-get-global 'fn-acct-redeem-plan state)
                              published)))

;; The one service-log line: the outcome and the reason class, never the
;; code, its digest, the login's password or the verifier.
(defun fn-acct-host-owner-redeem-log-line (published state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((plan (f-get-global 'fn-acct-redeem-plan state))
         (word (fn-acct-redeem-word plan published))
         (reason (if (and (consp plan) (equal (car plan) :refused)
                          (consp (cdr plan)) (symbolp (cadr plan)))
                     (symbol-name (cadr plan))
                   (if (and (consp plan) (symbolp (car plan)))
                       (symbol-name (car plan)) "UNKNOWN"))))
    (value (fn-record-string-octets
            (concatenate 'string "account redeem "
                         (if (equal word :bound) "bound" "refused")
                         " " (string-downcase reason)
                         (if (and (equal (car plan) :redeem)
                                  (not (equal published :accepted)))
                             " publication-refused" ""))))))

;; The host's re-entry after the publication: the (:account-outcome WORD)
;; event through the same owner step (:tls-established) takes.
(defun fn-owner-account-outcome (id word fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :mode :program))
  (let ((owner (fn-owner-core state)))
    (if (not (fn-own-find-conn id (fn-own-conns owner)))
        (value :unknown)
      (let* ((result (fn-ocfg-read-step (fn-owner-ocfg state)
                                        id (list :account-outcome word) fn-arena))
             (state (fn-owner-install-ocfg (cdr result) state))
             (state (fn-owner-install-effects (car result) state)))
        (value :ok)))))
