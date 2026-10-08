;; The split of fn-native-admin-plan (books/native-admin.lisp) into seven guard-verified
;; chunks is the original cond cut at every seventh arm.  This book proves it:
;; fn-native-admin-plan-old-cond is the original cond, verbatim (books/native-admin.lisp
;; at origin/integrate/20261008x, train 51); chunk K answers what the old cond answers whenever no
;; earlier chunk selects an arm, one lemma per chunk, composed at the end.
;; In each -out proof, earlier selectors stay opaque: the next chunk's
;; theorem supplies precisely those hypotheses.  Only the current selector
;; and chunk open, in a minimal theory, so validators cannot multiply the
;; fall-through clauses.  The -in proofs suppress preprocessing for the
;; same reason; chunk 7 benefits from preprocessing its all-negative case.
(in-package "ACL2")
(include-book "../../books/native-admin")
(include-book "must-fail-checked")

(defun fn-native-admin-plan-old-cond (argv)
  (declare (xargs :guard t :verify-guards nil))
  (let ((words (fn-native-admin-words argv)))
      (cond
       ((and (equal (len words) 3)
             (equal (car words) "group")
             (equal (cadr words) "create")
             (fn-native-admin-group-name-reservedp (caddr words)))
        (fn-native-admin-result :refused :reserved-group-name nil nil 0 nil nil))
       ((and (equal (len words) 3)
             (equal (car words) "group")
             (equal (cadr words) "create")
             (fn-record-group-namep (caddr words)))
        (fn-native-admin-result :accepted nil :create-group (caddr argv) 0 nil nil))
       ((and (equal (len words) 4) (equal (car words) "group")
             (equal (cadr words) "authority"))
        (cond ((fn-native-admin-group-name-reservedp (caddr words))
               (fn-native-admin-result :refused :reserved-group-name nil nil 0 nil nil))
              ((not (fn-record-group-namep (caddr words)))
               (fn-native-admin-result :refused :group-name nil nil 0 nil nil))
              ((not (or (equal (cadddr words) "ungoverned")
                        (fn-cfg-principal-hexp (cadddr words))))
               (fn-native-admin-result :refused :principal nil nil 0 nil nil))
              (t (fn-native-admin-result :accepted nil :set-group-authority
                                        (caddr argv) 0 nil
                                        (if (equal (cadddr words) "ungoverned") nil
                                          (cadddr argv))))))
       ; O2 (books/group-status.lisp): `group policy NAME n|y' sets the
       ; group's LIST ACTIVE status (RFC 3977 section 7.6.3): "n" closes it
       ; to local posting, "y" opens it.  A durable :set-group-status
       ; configuration record (code 21), offline or live.
       ((and (equal (len words) 4)
             (equal (car words) "group")
             (equal (cadr words) "policy")
             (fn-record-group-namep (caddr words))
             (member-equal (cadddr words) '("y" "n")))
        (fn-native-admin-result :accepted nil :set-group-status (caddr argv) 0
                                nil (cadddr argv)))
       ((and (equal (len words) 3)
             (equal (car words) "group")
             (equal (cadr words) "retire")
             (fn-record-group-namep (caddr words)))
        (fn-native-admin-result :accepted nil :remove-group (caddr argv) 0 nil nil))
       ((and (equal (len words) 2)
             (equal (car words) "capacity")
             (fn-native-admin-decimalp (cadr words)))
        (fn-native-admin-result :accepted nil :set-capacity nil
                                (fn-native-admin-decimal-value
                                 (coerce (cadr words) 'list)) nil nil))
       ; The node's own RFC 5537 section 3.2 <path-identity>.  It is the one
       ; policy slot peering needs: `fn-peer-local-identity' (books/peer-inbound)
       ; reads it, and while it is unset a node cannot recognise its own name
       ; in a Path, so section 3.5 loop suppression cannot fire (measured on
       ; the native v0 matrix, 2026-09-22: V0-TRANSIT-LOOP accepted 235).  The
       ; value must itself be a <path-identity>; the same recognizer admits a
       ; peer's identity in `fn-native-admin-peer-plan'.  The slot is a durable
       ; `:set-policy' configuration record, not a configuration-file key, for
       ; the reason packaging/fn.toml.example gives for served groups.
       ((and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (equal (caddr words) "path-identity")
             (fn-path-identityp (cadddr argv)))
        (fn-native-admin-result :accepted nil :set-policy (caddr argv) 0 nil
                                (cadddr argv)))
       ; PKT-597 (books/injection-info-policy.lisp): the mailbox the node's
       ; Injection-Info names as mail-complaints-to (RFC 5536 section
       ; 3.2.8), a durable `:set-policy' row like path-identity, applied
       ; live; the value must be an <addr-spec> of two dot-atoms, so it
       ; stands in the header's quoted-string as it is.
       ((fn-native-admin-complaints-wordsp words argv)
        (fn-native-admin-result :accepted nil :set-policy (caddr argv) 0 nil
                                (cadddr argv)))
       ; The served POST posting policy (books/login-binding.lisp):
       ; `bound-logins' refuses a bound login's article unless it is signed
       ; by the login's bound principal; `open' is the default behaviour.
       ; A durable `:set-policy' record like path-identity, applied live.
       ((and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (equal (caddr words) "posting-policy")
             (member-equal (cadddr words) '("bound-logins" "open")))
        (fn-native-admin-result :accepted nil :set-policy (caddr argv) 0 nil
                                (cadddr argv)))
       ; PRF-161 (books/public-exposure.lisp): what an unauthenticated
       ; session may do, a durable `:set-policy' record applied live.
       ((and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (equal (caddr words) *fn-exp-policy-slot*)
             (fn-exp-anonymous-wordp (cadddr words)))
        (fn-native-admin-result :accepted nil :set-policy (caddr argv) 0 nil
                                (cadddr argv)))
       ; PRF-211: the trusted range exempt from exposure-per-address, a
       ; durable `:set-policy' row applied live; the word is admitted only
       ; when every range in it parses (fn-exp-trusted-wordp), and `none'
       ; clears it.
       ((and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (equal (caddr words) *fn-exp-trusted-slot*)
             (fn-exp-trusted-wordp (cadddr words)))
        (fn-native-admin-result :accepted nil :set-policy (caddr argv) 0 nil
                                (cadddr argv)))
       ; PRF-986 (row W2a): `policy set tls-handshake-source-overrides
       ; WORD', the per-source handshake allowances for known shared
       ; addresses (a carrier NAT), a durable `:set-policy' row applied live
       ; (host fn-owner-handshake-limits reads it through
       ; fn-hsb-config-overrides).  The word is admitted exactly when the
       ; owner's parse lists it (`none' clears it); otherwise refused by
       ; the parse's name, :override-address or :overrides-full (past the
       ; profile's tls-handshake-source-overrides entries).
       ((and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (equal (caddr words) *fn-hsb-overrides-slot*))
        (let ((r (fn-hsb-overrides-of-word
                  (cadddr words) (fn-profile-limit :tls-handshake-source-overrides))))
          (if (member-equal r '(:override-address :overrides-full))
              (fn-native-admin-result :refused r nil nil 0 nil nil)
            (fn-native-admin-result :accepted nil :set-policy (caddr argv) 0 nil
                                    (cadddr argv)))))
       ; PRF-986 item 4 (books/tls-proxy.lisp): `policy set
       ; tls-proxy-trusted-peers WORD', the transport peers whose PROXY
       ; header the implicit-TLS listener reads (no other peer's octets are
       ; ever read as one); the syntax of exposure-trusted, `none' clears.
       ((and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (equal (caddr words) *fn-pxy-peers-slot*)
             (fn-exp-trusted-wordp (cadddr words)))
        (fn-native-admin-result :accepted nil :set-policy (caddr argv) 0 nil
                                (cadddr argv)))
       ; PRF-161: a limit of the public reader port, a `:set-limit' row
       ; (SLOT, "") staged, published and replayed like the retention rule.
       ((and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (fn-exp-limit-slotp (caddr words))
             (fn-native-admin-decimalp (cadddr words)))
        (fn-native-admin-result :accepted nil :set-exposure (caddr argv)
                                (fn-native-admin-decimal-value
                                 (coerce (cadddr words) 'list))
                                nil nil))
       ; PRF-235 / PRF-236 (books/relay-checks.lisp): `policy set
       ; relay-date-skew SECONDS' (RFC 5537 section 3.6 step 2's margin, at
       ; most its 86400) and `policy set refused-offer-capacity N' (the
       ; refused-offer memory's bound), each a `:set-limit' row keyed
       ; (SLOT, ""), staged, published and replayed like the exposure limits.
       ((and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (fn-rck-limit-slotp (caddr words))
             (fn-native-admin-decimalp (cadddr words))
             (fn-rck-limit-valuep (caddr words)
                                  (fn-native-admin-decimal-value
                                   (coerce (cadddr words) 'list))))
        (fn-native-admin-result :accepted nil :set-transit-limit (caddr argv)
                                (fn-native-admin-decimal-value
                                 (coerce (cadddr words) 'list))
                                nil nil))
       ; Lane log-2: the record log's batch bounds, `policy set
       ; log-batch-records N' and `policy set log-batch-octets N'
       ; (books/owner-log-route.lisp fn-olr-bmax / fn-olr-omax read these
       ; `:set-limit' rows), each keyed (SLOT, ""), staged, published and
       ; replayed like the transit limits.  A bound is positive and under the
       ; row's ceiling.  Lane time-model-2 (PRF-311): the disk's profile
       ; fields ride the same rows, `policy set barrier-deadline-ms N' (D),
       ; `barrier-stall-ms N' (H; read as at least D,
       ; books/owner-time-model.lisp fn-otm-limits) and `clock-event-ms N'
       ; (the committer's cadence), each positive milliseconds; a batch in
       ; flight keeps the limits it was issued with, the next one reads the
       ; new row.  Lane compression-extents-2: `policy set
       ; compress-min-octets N', the compression threshold, rides the same
       ; row kind; an article record appended after it with a payload span
       ; of at least N octets is offered to the encoder.
       ((and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (member-equal (caddr words) '("log-batch-records" "log-batch-octets"
                                           "barrier-deadline-ms" "barrier-stall-ms"
                                           "clock-event-ms" "compress-min-octets"
                                           ;; PRF-359: the operator's free-space
                                           ;; reserve (books/owner-time-model.lisp
                                           ;; fn-otm-space-need).
                                           "disk-reserve-octets"
                                           ;; PRF-986 (PKT-639): the TLS
                                           ;; handshake budget
                                           ;; (books/tls-handshake-budget.lisp
                                           ;; fn-hsb-limits), each positive.
                                           "tls-handshakes-per-source-per-minute"
                                           "tls-handshakes-in-flight"
                                           "tls-handshake-ms"))
             (fn-native-admin-decimalp (cadddr words))
             ; Lane compression-extents-2 (PRF-341): `compress-min-octets'
             ; (books/payload-lz-append.lisp fn-lzr-config-min) also admits
             ; 0, which is off, as no row is.
             (or (posp (fn-native-admin-decimal-value (coerce (cadddr words) 'list)))
                 (equal (caddr words) "compress-min-octets"))
             (<= (fn-native-admin-decimal-value (coerce (cadddr words) 'list))
                 (fn-cfg-limit-ceiling (caddr words))))
        (fn-native-admin-result :accepted nil :set-transit-limit (caddr argv)
                                (fn-native-admin-decimal-value
                                 (coerce (cadddr words) 'list))
                                nil nil))
       ; Row S1 (books/limits-live.lisp, PRF-940): the store's live limits,
       ; `policy set max-transactions|max-history-octets|max-article-octets
       ; N', one `:set-limit' row (FIELD, "") folded over the sealed profile
       ; (fn-lim-effective).  The host asks ACL2's fn-lim-decide before it
       ; stages anything: applied now, at the next start, or refused by name.
       ((and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (member-equal (caddr words) '("max-transactions" "max-history-octets"
                                           "max-article-octets"))
             (fn-native-admin-naturalp (cadddr words)))
        (fn-native-admin-result :accepted nil :set-store-limit (caddr argv)
                                (fn-native-admin-decimal-value
                                 (coerce (cadddr words) 'list))
                                nil nil))

       ; Row S10 (lane operability-2): `policy set KEY VALUE' that no arm
       ; above took is refused by name, not by the usage line: a counted
       ; key with a value that is no decimal count, else a key the node
       ; does not have.  (A known key with a wrong non-numeric value keeps
       ; the usage line: the line names the values.)
       ((and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (fn-native-admin-counted-policy-keyp (caddr words))
             (not (fn-native-admin-decimalp (cadddr words))))
        (fn-native-admin-result :refused :policy-value-not-a-number nil nil 0 nil nil))
       ((and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (not (fn-native-admin-known-policy-keyp (caddr words))))
        (fn-native-admin-result :refused :unknown-policy-key nil nil 0 nil nil))
       ((and (consp words) (equal (car words) "policy"))
        (fn-native-admin-result :refused :policy nil nil 0 nil nil))
       ; D13 (STO-014): the operator's content-retention rule.  Two
       ; `:set-limit' rows (books/reclaim-rule), staged, published and
       ; replayed as every other configuration record.  The default, with
       ; no row, is keep-forever.
       ((and (member-equal (len words) '(3 4))
             (equal (car words) "retention")
             (equal (cadr words) "set")
             (fn-rcl-rule-of-words (caddr words)
                                   (fn-native-admin-retention-days words)))
        (fn-native-admin-result :accepted nil :set-retention (caddr argv)
                                (nfix (fn-native-admin-retention-days words))
                                nil nil))
       ; Q14 (books/expiry-policy): the operator's per-group expiry policy,
       ; `retention expire TARGET clear' or `retention expire TARGET [keep
       ; DAYS] [default DAYS] [purge DAYS] [octets N]', TARGET a group name
       ; or "*" (every group without its own).  Five quota rows keyed
       ; (SCOPE, TARGET), staged, published and replayed as every other
       ; configuration record; `clear' writes the unset policy.
       ((and (<= 4 (len words))
             (equal (car words) "retention")
             (equal (cadr words) "expire")
             (fn-xpy-targetp (caddr words))
             (fn-xpy-words-policy (cdddr words)))
        (fn-native-admin-result :accepted nil :set-expiry (caddr argv) 0 nil
                                (fn-xpy-words-policy (cdddr words))))
       ((and (consp words) (equal (car words) "retention"))
        (fn-native-admin-result :refused :retention nil nil 0 nil nil))
       ((and (consp words) (equal (car words) "peer"))
        (cond
         ; `peer list' is the table's read side.  It carries no name, no
         ; capacity and no record: it is a query over the durable
         ; configuration, and `fn-native-admin-result-queryp' below is what
         ; keeps its executor off the writer lock and off the owner mutex.
         ((and (equal (len words) 2) (equal (cadr words) "list"))
          (fn-native-admin-result :accepted nil :list-peers nil 0 nil nil))
         ((and (equal (len words) 3)
               (equal (cadr words) "remove")
               (stringp (caddr words))
               (not (equal (caddr words) "")))
          (fn-native-admin-result :accepted nil :remove-peer (caddr argv) 0 nil nil))
         ((and (consp (cdr words))
               (member-equal (cadr words) '("budget" "carries" "pull" "pull-login" "distributions"
                                            "catch-up" "feed" "set")))
          (fn-native-admin-peer-extend-plan words))
         (t (fn-native-admin-peer-plan words))))
       ; PRF-164 (PKT-439): invitation-code accounts.  `account list' is a
       ; query (no digest or verifier is rendered, books/account-list.lisp
       ; `fn-acct-kinds-list-report').  `account invite DIGEST SECONDS' is the
       ; form the operator's `account invite [--expires SECONDS]' sends
       ; after ACL2 rendered the code and its digest on the operator's side
       ; (host/native/operator.lisp): the code itself never reaches this
       ; argv, the owner or any record.
       ((and (equal (len words) 2)
             (equal (car words) "account")
             (equal (cadr words) "list"))
        (fn-native-admin-result :accepted nil :list-accounts nil 0 nil nil))
       ((and (equal (len words) 4)
             (equal (car words) "account")
             (equal (cadr words) "invite")
             (fn-cfg-account-digestp (caddr words))
             (fn-native-admin-decimalp (cadddr words))
             (posp (fn-native-admin-decimal-value
                    (coerce (cadddr words) 'list))))
        (fn-native-admin-result :accepted nil :account-invite (caddr argv)
                                (fn-native-admin-decimal-value
                                 (coerce (cadddr words) 'list))
                                nil nil))
       ; PRF-222 (NNT-046): group access.  `account access show' is the
       ; `account list' report, whose access lines are the rules
       ; (books/account-list.lisp).  `account access LOGIN --read R --post P'
       ; and `account access --anonymous --read R --post P' stage one
       ; :account-access record (code 22), offline or live.
       ((and (equal (len words) 3)
             (equal (car words) "account")
             (equal (cadr words) "access")
             (equal (caddr words) "show"))
        (fn-native-admin-result :accepted nil :list-accounts nil 0 nil nil))
       ((and (<= 3 (len words))
             (equal (car words) "account")
             (equal (cadr words) "access"))
        (fn-native-admin-access-plan (cddr words) (cddr argv)))
       ; public-node-2: `account delete LOGIN' stages one :account-delete
       ; record (code 27), offline or live; the configuration admits it
       ; only while LOGIN holds an account and no obligation
       ; (books/accounts.lisp
       ; fn-acct-delete-is-admitted-exactly-when-held-and-unobligated).
       ((and (equal (len words) 3)
             (equal (car words) "account")
             (equal (cadr words) "delete"))
        (if (fn-cfg-account-loginp (caddr words))
            (fn-native-admin-result :accepted nil :account-delete (caddr argv)
                                    0 nil nil)
          (fn-native-admin-result :refused :account-login nil nil 0 nil nil)))
       ; PRF-388 (PKT-560): `account bind LOGIN HEX' and `account unbind
       ; LOGIN', the vector `principal bind|unbind' sends for a login the
       ; credential file does not hold (books/native-operator.lisp
       ; fn-native-operator-result-principal-account-result).  One
       ; :login-binding record (code 17), offline or live, which
       ; books/login-binding-live.lisp fn-lb-account-bind-plan admits only
       ; while LOGIN holds a redeemed account; HEX is the principal's 64
       ; lowercase hexadecimal digits.
       ((and (equal (len words) 4)
             (equal (car words) "account")
             (equal (cadr words) "bind"))
        (cond ((not (fn-cfg-account-loginp (caddr words)))
               (fn-native-admin-result :refused :account-login nil nil 0 nil nil))
              ((not (fn-cfg-hex-textp (cadddr words) 64))
               (fn-native-admin-result :refused :principal nil nil 0 nil nil))
              (t (fn-native-admin-result :accepted nil :account-bind (caddr argv)
                                         0 nil (cadddr argv)))))
       ((and (equal (len words) 3)
             (equal (car words) "account")
             (equal (cadr words) "unbind"))
        (if (fn-cfg-account-loginp (caddr words))
            (fn-native-admin-result :accepted nil :account-bind (caddr argv)
                                    0 nil nil)
          (fn-native-admin-result :refused :account-login nil nil 0 nil nil)))
       ((and (consp words) (equal (car words) "account"))
        (fn-native-admin-result :refused :account nil nil 0 nil nil))
       ; PRF-234: consumer bindings (books/consumer-bound.lisp).  `consumer
       ; show' is the `account list' report, whose consumer lines are the
       ; bindings.
       ((and (consp words) (equal (car words) "consumer"))
        (fn-native-admin-consumer-plan (cdr words) (cdr argv)))
       ; PKT-575 (CT3): the node operator's withdrawal authorization, the
       ; :withdraw-article record (code 26): `article withdraw-record CAUSE
       ; TARGET REASON'.  The owner's `article withdraw' and `moderation
       ; reject' name this vector (books/moderation-verbs.lisp
       ; `fn-mvb-withdraw-plan') before injecting CAUSE; the row alone
       ; withdraws nothing.
       ((and (equal (len words) 5)
             (equal (car words) "article")
             (equal (cadr words) "withdraw-record"))
        (fn-native-admin-result :accepted nil :withdraw-article (caddr argv) 0
                                (cadddr argv) (car (cddddr argv))))
       ((and (consp words) (equal (car words) "control"))
        (fn-native-admin-control-plan words argv))
       ((and (<= 3 (len words))
             (equal (car words) "group")
             (equal (cadr words) "describe"))
        (fn-native-admin-describe-plan words argv))
       ((and (<= 4 (len words))
             (equal (car words) "group")
             (equal (cadr words) "moderate"))
        (fn-native-admin-moderate-plan words argv))
       ; PRF-243 (RFC 6048 section 2.6): `group subscribe-default [NAME ...]'
       ; sets the list LIST SUBSCRIPTIONS recommends, in order; no NAME
       ; clears it.  One :set-default-subscriptions record (code 25); that
       ; each NAME is a live group named once is the delta's admission.
       ((and (<= 2 (len words))
             (equal (car words) "group")
             (equal (cadr words) "subscribe-default"))
        (if (fn-native-admin-group-namesp (nthcdr 2 words))
            (fn-native-admin-result :accepted nil :set-default-subscriptions
                                    nil 0 nil (nthcdr 2 (true-list-fix argv)))
          (fn-native-admin-result :refused :group-name nil nil 0 nil nil)))
       ((and (consp words) (equal (car words) "motd"))
        (fn-native-admin-motd-plan words argv))
       ((and (consp words) (equal (car words) "bp-boundary"))
        (fn-native-admin-bp-boundary-plan words))
       ((and (consp words) (equal (car words) "bp-route"))
        (fn-bprt-admin-plan words))
       ; PKT-868: what `store compact' and `store checkpoint' send a running
       ; owner (host/native/operator.lisp fnn-operator-execute-compaction): a
       ; request for its publication, no configuration record
       ; (fn-native-admin-result-owner-requestp; books/owner-compact-request).
       ; Q16's reclaim modes use the same work-class/plan declaration.
       ((fn-nco-store-plan-kind argv)
        (fn-native-admin-result :accepted nil (fn-nco-store-plan-kind argv) nil 0 nil nil))
       ; Row S3 (lane operability-2): what `store inspect ID' sends a running
       ; owner (host/native/operator.lisp fnn-operator-execute-inspect): a
       ; request for its own lookup of ID, no configuration record
       ; (books/owner-maintenance-request.lisp fn-omr-inspect-word).
       ((and (equal (fn-ncfg-first words) "inspect")
             (equal (fn-ncfg-second words) "request")
             (stringp (fn-ncfg-nth 2 words))
             (null (fn-ncfg-rest (fn-ncfg-rest (fn-ncfg-rest words)))))
        (fn-native-admin-result :accepted nil :request-inspect nil 0 nil
                                (fn-ncfg-nth 2 words)))
       ; Row S3b (lane operability-7): what `store export DIR' sends a
       ; running owner (host/native/operator.lisp
       ; fnn-operator-execute-export-live): a request for its own export of
       ; the captured history into DIR (the operator's grammar admitted an
       ; absolute path, fn-nop-archive-pathp), and the status poll that
       ; follows it (books/owner-export-request.lisp fn-oex-request-word,
       ; fn-oex-status-word).  No configuration record.
       ((and (equal (fn-ncfg-first words) "export")
             (equal (fn-ncfg-second words) "request")
             (stringp (fn-ncfg-nth 2 words))
             (null (fn-ncfg-rest (fn-ncfg-rest (fn-ncfg-rest words)))))
        (fn-native-admin-result :accepted nil :request-export nil 0 nil
                                (fn-ncfg-nth 2 words)))
       ((equal words '("export" "status"))
        (fn-native-admin-result :accepted nil :request-export-status nil 0 nil nil))
       (t (fn-native-admin-result :refused :syntax nil nil nil nil nil)))))

(defun fn-native-admin-plan-old (argv)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-native-admin-argvp argv))
      (fn-native-admin-result :refused :argv nil nil nil nil nil)
    (fn-native-admin-plan-old-cond argv)))

(defun fn-native-admin-plan-sel-1 (argv)
  (declare (xargs :guard t :verify-guards nil))
  (let ((words (fn-native-admin-words argv)))
    (or (and (equal (len words) 3)
             (equal (car words) "group")
             (equal (cadr words) "create")
             (fn-native-admin-group-name-reservedp (caddr words))) (and (equal (len words) 3)
             (equal (car words) "group")
             (equal (cadr words) "create")
             (fn-record-group-namep (caddr words))) (and (equal (len words) 4) (equal (car words) "group")
             (equal (cadr words) "authority")) (and (equal (len words) 4)
             (equal (car words) "group")
             (equal (cadr words) "policy")
             (fn-record-group-namep (caddr words))
             (member-equal (cadddr words) '("y" "n"))) (and (equal (len words) 3)
             (equal (car words) "group")
             (equal (cadr words) "retire")
             (fn-record-group-namep (caddr words))) (and (equal (len words) 2)
             (equal (car words) "capacity")
             (fn-native-admin-decimalp (cadr words))) (and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (equal (caddr words) "path-identity")
             (fn-path-identityp (cadddr argv))))))

(defun fn-native-admin-plan-sel-2 (argv)
  (declare (xargs :guard t :verify-guards nil))
  (let ((words (fn-native-admin-words argv)))
    (or (fn-native-admin-complaints-wordsp words argv) (and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (equal (caddr words) "posting-policy")
             (member-equal (cadddr words) '("bound-logins" "open"))) (and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (equal (caddr words) *fn-exp-policy-slot*)
             (fn-exp-anonymous-wordp (cadddr words))) (and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (equal (caddr words) *fn-exp-trusted-slot*)
             (fn-exp-trusted-wordp (cadddr words))) (and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (equal (caddr words) *fn-hsb-overrides-slot*)) (and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (equal (caddr words) *fn-pxy-peers-slot*)
             (fn-exp-trusted-wordp (cadddr words))) (and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (fn-exp-limit-slotp (caddr words))
             (fn-native-admin-decimalp (cadddr words))))))

(defun fn-native-admin-plan-sel-3 (argv)
  (declare (xargs :guard t :verify-guards nil))
  (let ((words (fn-native-admin-words argv)))
    (or (and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (fn-rck-limit-slotp (caddr words))
             (fn-native-admin-decimalp (cadddr words))
             (fn-rck-limit-valuep (caddr words)
                                  (fn-native-admin-decimal-value
                                   (coerce (cadddr words) 'list)))) (and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (member-equal (caddr words) '("log-batch-records" "log-batch-octets"
                                           "barrier-deadline-ms" "barrier-stall-ms"
                                           "clock-event-ms" "compress-min-octets"
                                           ;; PRF-359: the operator's free-space
                                           ;; reserve (books/owner-time-model.lisp
                                           ;; fn-otm-space-need).
                                           "disk-reserve-octets"
                                           ;; PRF-986 (PKT-639): the TLS
                                           ;; handshake budget
                                           ;; (books/tls-handshake-budget.lisp
                                           ;; fn-hsb-limits), each positive.
                                           "tls-handshakes-per-source-per-minute"
                                           "tls-handshakes-in-flight"
                                           "tls-handshake-ms"))
             (fn-native-admin-decimalp (cadddr words))
             ; Lane compression-extents-2 (PRF-341): `compress-min-octets'
             ; (books/payload-lz-append.lisp fn-lzr-config-min) also admits
             ; 0, which is off, as no row is.
             (or (posp (fn-native-admin-decimal-value (coerce (cadddr words) 'list)))
                 (equal (caddr words) "compress-min-octets"))
             (<= (fn-native-admin-decimal-value (coerce (cadddr words) 'list))
                 (fn-cfg-limit-ceiling (caddr words)))) (and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (member-equal (caddr words) '("max-transactions" "max-history-octets"
                                           "max-article-octets"))
             (fn-native-admin-naturalp (cadddr words))) (and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (fn-native-admin-counted-policy-keyp (caddr words))
             (not (fn-native-admin-decimalp (cadddr words)))) (and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (not (fn-native-admin-known-policy-keyp (caddr words)))) (and (consp words) (equal (car words) "policy")) (and (member-equal (len words) '(3 4))
             (equal (car words) "retention")
             (equal (cadr words) "set")
             (fn-rcl-rule-of-words (caddr words)
                                   (fn-native-admin-retention-days words))))))

(defun fn-native-admin-plan-sel-4 (argv)
  (declare (xargs :guard t :verify-guards nil))
  (let ((words (fn-native-admin-words argv)))
    (or (and (<= 4 (len words))
             (equal (car words) "retention")
             (equal (cadr words) "expire")
             (fn-xpy-targetp (caddr words))
             (fn-xpy-words-policy (cdddr words))) (and (consp words) (equal (car words) "retention")) (and (consp words) (equal (car words) "peer")) (and (equal (len words) 2)
             (equal (car words) "account")
             (equal (cadr words) "list")) (and (equal (len words) 4)
             (equal (car words) "account")
             (equal (cadr words) "invite")
             (fn-cfg-account-digestp (caddr words))
             (fn-native-admin-decimalp (cadddr words))
             (posp (fn-native-admin-decimal-value
                    (coerce (cadddr words) 'list)))) (and (equal (len words) 3)
             (equal (car words) "account")
             (equal (cadr words) "access")
             (equal (caddr words) "show")) (and (<= 3 (len words))
             (equal (car words) "account")
             (equal (cadr words) "access")))))

(defun fn-native-admin-plan-sel-5 (argv)
  (declare (xargs :guard t :verify-guards nil))
  (let ((words (fn-native-admin-words argv)))
    (or (and (equal (len words) 3)
             (equal (car words) "account")
             (equal (cadr words) "delete")) (and (equal (len words) 4)
             (equal (car words) "account")
             (equal (cadr words) "bind")) (and (equal (len words) 3)
             (equal (car words) "account")
             (equal (cadr words) "unbind")) (and (consp words) (equal (car words) "account")) (and (consp words) (equal (car words) "consumer")) (and (equal (len words) 5)
             (equal (car words) "article")
             (equal (cadr words) "withdraw-record")) (and (consp words) (equal (car words) "control")))))

(defun fn-native-admin-plan-sel-6 (argv)
  (declare (xargs :guard t :verify-guards nil))
  (let ((words (fn-native-admin-words argv)))
    (or (and (<= 3 (len words))
             (equal (car words) "group")
             (equal (cadr words) "describe"))
        (and (<= 4 (len words))
             (equal (car words) "group")
             (equal (cadr words) "moderate"))
        (and (<= 2 (len words))
             (equal (car words) "group")
             (equal (cadr words) "subscribe-default"))
        (and (consp words) (equal (car words) "motd"))
        (and (consp words) (equal (car words) "bp-boundary"))
        (and (consp words) (equal (car words) "bp-route"))
        (fn-nco-store-plan-kind argv))))

(defun fn-native-admin-plan-sel-7 (argv)
  (declare (xargs :guard t :verify-guards nil))
  (let ((words (fn-native-admin-words argv)))
    (or (and (equal (fn-ncfg-first words) "inspect")
             (equal (fn-ncfg-second words) "request")
             (stringp (fn-ncfg-nth 2 words))
             (null (fn-ncfg-rest (fn-ncfg-rest (fn-ncfg-rest words)))))
        (and (equal (fn-ncfg-first words) "export")
             (equal (fn-ncfg-second words) "request")
             (stringp (fn-ncfg-nth 2 words))
             (null (fn-ncfg-rest (fn-ncfg-rest (fn-ncfg-rest words)))))
        (equal words '("export" "status"))
        t)))

(in-theory (disable fn-native-admin-plan-old-cond fn-native-admin-plan-old fn-native-admin-plan-sel-1 fn-native-admin-plan-sel-2 fn-native-admin-plan-sel-3 fn-native-admin-plan-sel-4 fn-native-admin-plan-sel-5 fn-native-admin-plan-sel-6 fn-native-admin-plan-sel-7 fn-native-admin-plan-arms-1 fn-native-admin-plan-arms-2 fn-native-admin-plan-arms-3 fn-native-admin-plan-arms-4 fn-native-admin-plan-arms-5 fn-native-admin-plan-arms-6 fn-native-admin-plan-arms-7))

(defthm fn-native-admin-plan-chunk-7
  (implies (and (not (fn-native-admin-plan-sel-1 argv)) (not (fn-native-admin-plan-sel-2 argv)) (not (fn-native-admin-plan-sel-3 argv)) (not (fn-native-admin-plan-sel-4 argv)) (not (fn-native-admin-plan-sel-5 argv)) (not (fn-native-admin-plan-sel-6 argv)))
           (equal (fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-7 argv)))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-7 argv) (fn-native-admin-plan-sel-1 argv) (fn-native-admin-plan-sel-2 argv) (fn-native-admin-plan-sel-3 argv) (fn-native-admin-plan-sel-4 argv) (fn-native-admin-plan-sel-5 argv) (fn-native-admin-plan-sel-6 argv)))))

(defthm fn-native-admin-plan-chunk-6-in
  (implies (and (not (fn-native-admin-plan-sel-1 argv)) (not (fn-native-admin-plan-sel-2 argv)) (not (fn-native-admin-plan-sel-3 argv)) (not (fn-native-admin-plan-sel-4 argv)) (not (fn-native-admin-plan-sel-5 argv)) (fn-native-admin-plan-sel-6 argv))
           (equal (fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-6 argv)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :expand ((fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-6 argv) (fn-native-admin-plan-sel-6 argv) (fn-native-admin-plan-sel-1 argv) (fn-native-admin-plan-sel-2 argv) (fn-native-admin-plan-sel-3 argv) (fn-native-admin-plan-sel-4 argv) (fn-native-admin-plan-sel-5 argv)))))

(defthm fn-native-admin-plan-chunk-6-out
  (implies (and (not (fn-native-admin-plan-sel-1 argv)) (not (fn-native-admin-plan-sel-2 argv)) (not (fn-native-admin-plan-sel-3 argv)) (not (fn-native-admin-plan-sel-4 argv)) (not (fn-native-admin-plan-sel-5 argv)) (not (fn-native-admin-plan-sel-6 argv)))
           (equal (fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-6 argv)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(not implies)) :do-not '(preprocess) :use fn-native-admin-plan-chunk-7
           :expand ((fn-native-admin-plan-arms-6 argv) (fn-native-admin-plan-sel-6 argv)))))

(defthm fn-native-admin-plan-chunk-6
  (implies (and (not (fn-native-admin-plan-sel-1 argv)) (not (fn-native-admin-plan-sel-2 argv)) (not (fn-native-admin-plan-sel-3 argv)) (not (fn-native-admin-plan-sel-4 argv)) (not (fn-native-admin-plan-sel-5 argv)))
           (equal (fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-6 argv)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :use (fn-native-admin-plan-chunk-6-in fn-native-admin-plan-chunk-6-out))))

(defthm fn-native-admin-plan-chunk-5-in
  (implies (and (not (fn-native-admin-plan-sel-1 argv)) (not (fn-native-admin-plan-sel-2 argv)) (not (fn-native-admin-plan-sel-3 argv)) (not (fn-native-admin-plan-sel-4 argv)) (fn-native-admin-plan-sel-5 argv))
           (equal (fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-5 argv)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :expand ((fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-5 argv) (fn-native-admin-plan-sel-5 argv) (fn-native-admin-plan-sel-1 argv) (fn-native-admin-plan-sel-2 argv) (fn-native-admin-plan-sel-3 argv) (fn-native-admin-plan-sel-4 argv)))))

(defthm fn-native-admin-plan-chunk-5-out
  (implies (and (not (fn-native-admin-plan-sel-1 argv)) (not (fn-native-admin-plan-sel-2 argv)) (not (fn-native-admin-plan-sel-3 argv)) (not (fn-native-admin-plan-sel-4 argv)) (not (fn-native-admin-plan-sel-5 argv)))
           (equal (fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-5 argv)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(not implies)) :do-not '(preprocess) :use fn-native-admin-plan-chunk-6
           :expand ((fn-native-admin-plan-arms-5 argv) (fn-native-admin-plan-sel-5 argv)))))

(defthm fn-native-admin-plan-chunk-5
  (implies (and (not (fn-native-admin-plan-sel-1 argv)) (not (fn-native-admin-plan-sel-2 argv)) (not (fn-native-admin-plan-sel-3 argv)) (not (fn-native-admin-plan-sel-4 argv)))
           (equal (fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-5 argv)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :use (fn-native-admin-plan-chunk-5-in fn-native-admin-plan-chunk-5-out))))

(defthm fn-native-admin-plan-chunk-4-in
  (implies (and (not (fn-native-admin-plan-sel-1 argv)) (not (fn-native-admin-plan-sel-2 argv)) (not (fn-native-admin-plan-sel-3 argv)) (fn-native-admin-plan-sel-4 argv))
           (equal (fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-4 argv)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :expand ((fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-4 argv) (fn-native-admin-plan-sel-4 argv) (fn-native-admin-plan-sel-1 argv) (fn-native-admin-plan-sel-2 argv) (fn-native-admin-plan-sel-3 argv)))))

(defthm fn-native-admin-plan-chunk-4-out
  (implies (and (not (fn-native-admin-plan-sel-1 argv)) (not (fn-native-admin-plan-sel-2 argv)) (not (fn-native-admin-plan-sel-3 argv)) (not (fn-native-admin-plan-sel-4 argv)))
           (equal (fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-4 argv)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(not implies)) :do-not '(preprocess) :use fn-native-admin-plan-chunk-5
           :expand ((fn-native-admin-plan-arms-4 argv) (fn-native-admin-plan-sel-4 argv)))))

(defthm fn-native-admin-plan-chunk-4
  (implies (and (not (fn-native-admin-plan-sel-1 argv)) (not (fn-native-admin-plan-sel-2 argv)) (not (fn-native-admin-plan-sel-3 argv)))
           (equal (fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-4 argv)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :use (fn-native-admin-plan-chunk-4-in fn-native-admin-plan-chunk-4-out))))

(defthm fn-native-admin-plan-chunk-3-in
  (implies (and (not (fn-native-admin-plan-sel-1 argv)) (not (fn-native-admin-plan-sel-2 argv)) (fn-native-admin-plan-sel-3 argv))
           (equal (fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-3 argv)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :expand ((fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-3 argv) (fn-native-admin-plan-sel-3 argv) (fn-native-admin-plan-sel-1 argv) (fn-native-admin-plan-sel-2 argv)))))

(defthm fn-native-admin-plan-chunk-3-out
  (implies (and (not (fn-native-admin-plan-sel-1 argv)) (not (fn-native-admin-plan-sel-2 argv)) (not (fn-native-admin-plan-sel-3 argv)))
           (equal (fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-3 argv)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(not implies)) :do-not '(preprocess) :use fn-native-admin-plan-chunk-4
           :expand ((fn-native-admin-plan-arms-3 argv) (fn-native-admin-plan-sel-3 argv)))))

(defthm fn-native-admin-plan-chunk-3
  (implies (and (not (fn-native-admin-plan-sel-1 argv)) (not (fn-native-admin-plan-sel-2 argv)))
           (equal (fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-3 argv)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :use (fn-native-admin-plan-chunk-3-in fn-native-admin-plan-chunk-3-out))))

(defthm fn-native-admin-plan-chunk-2-in
  (implies (and (not (fn-native-admin-plan-sel-1 argv)) (fn-native-admin-plan-sel-2 argv))
           (equal (fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-2 argv)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :expand ((fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-2 argv) (fn-native-admin-plan-sel-2 argv) (fn-native-admin-plan-sel-1 argv)))))

(defthm fn-native-admin-plan-chunk-2-out
  (implies (and (not (fn-native-admin-plan-sel-1 argv)) (not (fn-native-admin-plan-sel-2 argv)))
           (equal (fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-2 argv)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(not implies)) :do-not '(preprocess) :use fn-native-admin-plan-chunk-3
           :expand ((fn-native-admin-plan-arms-2 argv) (fn-native-admin-plan-sel-2 argv)))))

(defthm fn-native-admin-plan-chunk-2
  (implies (and (not (fn-native-admin-plan-sel-1 argv)))
           (equal (fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-2 argv)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :use (fn-native-admin-plan-chunk-2-in fn-native-admin-plan-chunk-2-out))))

(defthm fn-native-admin-plan-chunk-1-in
  (implies (and (fn-native-admin-plan-sel-1 argv))
           (equal (fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-1 argv)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :expand ((fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-1 argv) (fn-native-admin-plan-sel-1 argv) ))))

(defthm fn-native-admin-plan-chunk-1-out
  (implies (and (not (fn-native-admin-plan-sel-1 argv)))
           (equal (fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-1 argv)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(not implies)) :do-not '(preprocess) :use fn-native-admin-plan-chunk-2
           :expand ((fn-native-admin-plan-arms-1 argv) (fn-native-admin-plan-sel-1 argv)))))

(defthm fn-native-admin-plan-chunk-1
  (implies t
           (equal (fn-native-admin-plan-old-cond argv) (fn-native-admin-plan-arms-1 argv)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :use (fn-native-admin-plan-chunk-1-in fn-native-admin-plan-chunk-1-out))))

(defthm fn-native-admin-plan-is-the-old-plan
  (equal (fn-native-admin-plan argv) (fn-native-admin-plan-old argv))
  :hints (("Goal" :do-not '(preprocess) :use fn-native-admin-plan-chunk-1
           :expand ((fn-native-admin-plan argv) (fn-native-admin-plan-old argv)))))
