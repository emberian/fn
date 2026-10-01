; fn: the redemption's admission bound counts the table itself (PKT-399, row
; Q3d (iv) of build/coordinator/COMPLETE-BEFORE-6.6.0.md).
;
; host/native-admin-host.lisp fn-acct-host-owner-redeem-stage computed USED =
; (len creds) of the connection-independent credential table and TAKENP in
; program mode and passed both to fn-acct-redeem-bounded-plan, whose keystone
; holds for any natural USED: nothing proved USED was the table's size (a host
; value the decision compares).  fn-arc-redeem-plan derives both from the
; table the host already holds: auth.toml's credentials (the owner's AUTHINFO
; configuration) followed by the redeemed accounts of the live configuration
; value (fn-auth-config-with-accounts; fn-auth-account-creds keeps a row only
; when its mark is 1 and it denotes a credential, so a pending invitation
; (mark 0) and a login-to-principal binding (mark 2) are never counted).
; The host passes tables, not numbers (GEN: the host rewire waits for stage
; 0; then host_check --load).
;
; KEYSTONE fn-arc-redeem-refuses-exactly-past-the-operator-bound: where the
; unbounded plan redeems, fn-arc-redeem-plan redeems exactly when auth.toml's
; credentials plus the redeemed accounts number fewer than BOUND (the store
; profile's max-credentials, field 12), and otherwise refuses with
; :account-credential-bound.  A plan that does not redeem is unchanged.
(in-package "ACL2")
(include-book "accounts")
(include-book "nntp-auth")

; The credential table the redemption is admitted against.
(defun fn-arc-creds (auth v)
  (declare (xargs :guard t))
  (fn-auth-config-creds (fn-auth-config-with-accounts auth v)))

; The plan the owner stages: the bounded plan over the counted table.
(defun fn-arc-redeem-plan (v auth stamp code login password salt bound)
  (declare (xargs :guard t))
  (let ((creds (fn-arc-creds auth v)))
    (fn-acct-redeem-bounded-plan v stamp code login password salt
                                 (and (fn-auth-find-cred login creds) t)
                                 (len creds) bound)))

(local (defthm fn-arc-creds-count
  (implies (fn-auth-configp auth)
           (equal (len (fn-arc-creds auth v))
                  (+ (len (fn-auth-config-creds auth))
                     (len (fn-auth-account-creds (fn-cfg-accounts v))))))
  :hints (("Goal" :in-theory (e/d (fn-arc-creds fn-auth-config-with-accounts)
                                  (fn-auth-account-creds))))))

; KEYSTONE (PKT-399).
(defthm fn-arc-redeem-refuses-exactly-past-the-operator-bound
  (let ((takenp (and (fn-auth-find-cred login (fn-arc-creds auth v)) t)))
    (implies (fn-auth-configp auth)
             (equal (fn-arc-redeem-plan v auth stamp code login password salt bound)
                    (if (and (equal (car (fn-acct-redeem-plan v stamp code login password
                                                              salt takenp))
                                    :redeem)
                             (not (< (+ (len (fn-auth-config-creds auth))
                                        (len (fn-auth-account-creds (fn-cfg-accounts v))))
                                     (nfix bound))))
                        (list :refused :account-credential-bound)
                      (fn-acct-redeem-plan v stamp code login password salt takenp)))))
  :hints (("Goal" :in-theory (e/d (fn-arc-redeem-plan fn-acct-redeem-bounded-plan)
                                  (fn-acct-redeem-plan fn-arc-creds
                                   fn-auth-account-creds fn-auth-find-cred)))))
