; Teeth for PRF-164's credential snapshot (books/nntp-auth.lisp
; fn-auth-config-with-accounts): one credential table, auth.toml's rows
; first, then one credential per redeemed row of the pinned configuration.
; Values computed through the crypto seam are zero-argument macros
; (tests/acl2/auth-secret-tests.lisp).
(in-package "ACL2")
(include-book "../../books/nntp-auth")
(include-book "../../books/crypto-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *as-salt* (make-list 16 :initial-element 7))
(defconst *as-password* (fn-record-string-octets "correct horse"))
(defconst *as-login* (fn-record-string-octets "robin"))
(defconst *as-stamp* (fn-clock-observation 5 1700000000 2 t))
(defconst *as-code* (fn-record-string-octets "k3y-friend-0001-7f3a"))

(defmacro as-v1 ()
  '(fn-cfg-apply-delta (fn-cfg-empty-value) 1 *as-stamp*
                       (fn-cfg-account-invite (fn-acct-code-digest-text *as-code*)
                                              "operator" "2000000000")))
(defmacro as-v2 ()
  '(fn-cfg-apply-delta
    (as-v1) 2 *as-stamp*
    (fn-acct-plan-delta (fn-acct-redeem-plan (as-v1) *as-stamp* *as-code*
                                             *as-login* *as-password*
                                             *as-salt* nil))))
; auth.toml's table: one operator credential, "ember".
(defmacro as-operator-cred ()
  '(fn-auth-make-cred (fn-record-string-octets "ember")
                      (fn-acct-local-principal (fn-record-string-octets "ember"))
                      (fn-authsec-enrol *as-salt* (fn-record-string-octets "pw"))
                      t))
(defmacro as-acfg () '(fn-auth-make-config t t t (list (as-operator-cred))))
(defmacro as-snap (v) `(fn-auth-config-with-accounts (as-acfg) ,v))

(assert-event (fn-auth-configp (as-acfg)))
(assert-event (fn-auth-configp (as-snap (as-v2))))

; KEYSTONE fn-auth-config-with-accounts-finds-the-redeemed-credential:
; reachable witness.  auth.toml does not name robin; the snapshot finds the
; redeemed row's credential with robin's local principal, and its verifier
; checks robin's password.
(assert-event (not (fn-auth-find-cred *as-login*
                                      (fn-auth-config-creds (as-acfg)))))
(assert-event
 (equal (fn-auth-find-cred *as-login* (fn-auth-config-creds (as-snap (as-v2))))
        (fn-auth-make-cred *as-login* (fn-acct-local-principal *as-login*)
                           (fn-authsec-enrol *as-salt* *as-password*) t)))
(assert-event
 (fn-auth-checkp (fn-auth-find-cred *as-login*
                                    (fn-auth-config-creds (as-snap (as-v2))))
                 *as-password*))
; A pending row is no credential: before the redeem robin is unknown.
(assert-event (not (fn-auth-find-cred *as-login*
                                      (fn-auth-config-creds (as-snap (as-v1))))))
; Removal of the not-in-auth.toml hypothesis: a login auth.toml names keeps
; the operator's credential (fn-auth-config-with-accounts-keeps-the-operators-credential).
(assert-event
 (equal (fn-auth-find-cred (fn-record-string-octets "ember")
                           (fn-auth-config-creds (as-snap (as-v2))))
        (as-operator-cred)))
(must-fail
 (assert-event
  (equal (fn-auth-find-cred (fn-record-string-octets "ember")
                            (fn-auth-config-creds (as-snap (as-v2))))
         (fn-auth-find-cred (fn-record-string-octets "ember")
                            (fn-auth-account-creds
                             (fn-cfg-accounts (as-v2)))))))
; Removal of fn-auth-configp: a malformed policy is passed through unchanged.
(assert-event (equal (fn-auth-config-with-accounts :junk (as-v2)) :junk))
