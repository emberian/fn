; Program bridge for the native administrative plan.
(in-package "ACL2")
(include-book "../books/native-admin")
(ld "store-node-host.lisp" :ld-error-action :error)
(ld "owner-host.lisp" :ld-error-action :error)

(defun fn-native-admin-host-plan (argv) (fn-native-admin-plan argv))
(defun fn-native-admin-host-status (result) (fn-native-admin-result-status result))
(defun fn-native-admin-host-reason (result) (fn-native-admin-result-reason result))
(defun fn-native-admin-host-kind (result) (fn-native-admin-result-kind result))
(defun fn-native-admin-host-name (result) (fn-native-admin-result-name result))
(defun fn-native-admin-host-capacity (result) (fn-native-admin-result-capacity result))
(defun fn-native-admin-host-peer (result) (fn-native-admin-result-peer result))
(defun fn-native-admin-host-value (result) (fn-native-admin-result-value result))
(defun fn-native-admin-host-queryp (result) (fn-native-admin-result-queryp result))
(defun fn-native-admin-host-report-kind (result)
  (fn-native-admin-result-report-kind result))
(defun fn-native-admin-host-peer-report (state)
  ; The `peer list' report over the configuration the store just replayed.
  ; The rows are the replayed value's own; this bridge selects no peer,
  ; orders nothing, and renders no field: books/native-admin.lisp does all
  ; three and raw Lisp only writes the octets out.
  (declare (xargs :stobjs state :mode :program))
  (value (fn-native-admin-peer-report
          (fn-cfg-peers (fn-cfg-value (f-get-global 'fn-store-cfg state))))))
(defun fn-native-admin-host-query-report (plan state)
  ; `peer list' or `control list' over the configuration the store just
  ; replayed; books/native-admin.lisp selects and renders.
  (declare (xargs :stobjs state :mode :program))
  (value (fn-native-admin-query-report
          plan (fn-cfg-value (f-get-global 'fn-store-cfg state)))))
(defun fn-native-admin-host-owner-reconfigure (id plan state)
  ; The live arm.  The delta list, labels as strings, is ACL2's
  ; (`fn-native-admin-plan-deltas', books/native-admin.lisp); this bridge
  ; only hands it to the owner's staging step.
  (declare (xargs :stobjs state :mode :program))
  ; PRF-099: an :extend-peer plan's delta is built over the live owner's
  ; peer table (`fn-native-admin-plan-deltas-over').
  ;; PRF-164: an `account invite' plan's pending row expires from the live
  ;; owner's clock (fn-native-admin-account-deltas).
  (let ((deltas (if (equal (fn-native-admin-result-kind plan) :account-invite)
                    (fn-native-admin-account-deltas
                     plan (fn-own-clock (fn-owner-core state)))
                  (fn-native-admin-plan-deltas-over
                   plan (fn-cfg-peers (fn-cfg-value (fn-owner-config state)))))))
    (if deltas
        (fn-owner-reconfigure-deltas id deltas state)
      (value :refused))))
(defun fn-native-admin-host-apply (plan monotonic wall state)
  (declare (xargs :stobjs state :mode :program))
  (let ((kind (fn-native-admin-result-kind plan)))
    (cond ((member-equal kind '(:set-bp-boundary :set-bp-route :remove-bp-route
                                :grant-control :revoke-control :set-retention
                                ;; PRF-161: an exposure limit row.
                                :set-exposure))
           (fn-store-cfg-peer-delta-record
            (fn-native-admin-plan-deltas plan) monotonic wall state))
          ; PRF-099: `peer carries' / `peer budget' over the replayed table.
          ((equal kind :extend-peer)
           (let ((deltas (fn-native-admin-plan-deltas-over
                          plan (fn-cfg-peers
                                (fn-cfg-value (f-get-global 'fn-store-cfg state))))))
             (if deltas
                 (fn-store-cfg-peer-delta-record deltas monotonic wall state)
               (let ((state (f-put-global 'fn-store-cfg-last-reason :no-such-peer
                                          state)))
                 (value :refused)))))
          ;; PRF-164: offline, the pending row expires from the record's
          ;; own stamp (the one fn-store-cfg-peer-delta-record builds).
          ((equal kind :account-invite)
           (let ((deltas (fn-native-admin-account-deltas
                          plan (fn-clock-observation (nfix monotonic) (nfix wall)
                                                     0 t))))
             (if deltas
                 (fn-store-cfg-peer-delta-record deltas monotonic wall state)
               (let ((state (f-put-global 'fn-store-cfg-last-reason :no-clock
                                          state)))
                 (value :refused)))))
          ((equal kind :set-peer)
           (fn-store-cfg-peer-delta-record
            (list (fn-native-admin-set-peer-delta plan))
            monotonic wall state))
          ((equal kind :remove-peer)
           (fn-store-cfg-remove-peer (fn-native-admin-result-name plan)
                                     monotonic wall state))
          ((equal kind :set-policy)
           (fn-store-cfg-set-policy (fn-native-admin-result-name plan)
                                    (fn-native-admin-result-value plan)
                                    monotonic wall state))
          (t (fn-store-cfg-reconfigure
              kind (fn-native-admin-result-name plan)
              (fn-native-admin-result-capacity plan)
              monotonic wall state)))))
(defun fn-native-admin-host-config-name (generation)
  (fn-native-admin-config-name generation))
(defun fn-native-admin-host-clock-observation (monotonic wall)
  (fn-native-admin-clock-observation monotonic wall))
(defun fn-native-admin-host-clock-status (result)
  (fn-native-admin-clock-status result))
(defun fn-native-admin-host-clock-stamp (result)
  (fn-native-admin-clock-stamp result))
(defun fn-native-admin-host-clock-monotonic (stamp)
  (fn-clock-monotonic stamp))
(defun fn-native-admin-host-clock-wall (stamp)
  (fn-clock-wall stamp))
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
(defun fn-acct-host-code-text (entropy) (fn-acct-code-text entropy))
(defun fn-acct-host-code-digest-text (code-octets)
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
(defun fn-acct-host-owner-redeem-stage (pcid id salt bound state)
  (declare (xargs :stobjs state :mode :program))
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
                                     state)
      (value :refused))))

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
(defun fn-owner-account-outcome (id word state)
  (declare (xargs :stobjs state :mode :program))
  (let ((owner (fn-owner-core state)))
    (if (not (fn-own-find-conn id (fn-own-conns owner)))
        (value :unknown)
      (let* ((result (fn-ocfg-read-step (fn-owner-ocfg state)
                                        id (list :account-outcome word)))
             (state (fn-owner-install-ocfg (cdr result) state))
             (state (fn-owner-install-effects (car result) state)))
        (value :ok)))))
