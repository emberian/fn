; Teeth for PRF-164's credential snapshot (books/nntp-auth.lisp
; fn-auth-config-with-accounts): one credential table, auth.toml's rows
; first, then one credential per redeemed row of the pinned configuration.
; Values computed through the crypto seam are zero-argument macros
; (tests/acl2/auth-secret-tests.lisp).
(in-package "ACL2")
(include-book "../../books/nntp-auth")
(include-book "../../books/crypto-attach")
(include-book "must-fail-checked")

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
(must-fail-checked
 (assert-event
  (equal (fn-auth-find-cred (fn-record-string-octets "ember")
                            (fn-auth-config-creds (as-snap (as-v2))))
         (fn-auth-find-cred (fn-record-string-octets "ember")
                            (fn-auth-account-creds
                             (fn-cfg-accounts (as-v2)))))))
; Removal of fn-auth-configp: a malformed policy is passed through unchanged.
(assert-event (equal (fn-auth-config-with-accounts :junk (as-v2)) :junk))

; -----------------------------------------------------------------------------
; KEYSTONE fn-auth-config-with-accounts-after-an-account-delete-offers-only-the-operators-credential
; (public-node-2).  No hypothesis: the witness is one account deleted, the
; tooth is the same statement over another delta.
(defmacro as-del (login) `(fn-cfg-account-delete ,login))
(defmacro as-v3 () '(fn-cfg-apply-delta (as-v2) 3 *as-stamp* (as-del "robin")))
; Before: the snapshot finds robin's redeemed credential.
(assert-event (fn-auth-find-cred *as-login* (fn-auth-config-creds (as-snap (as-v2)))))
; After: robin is found nowhere (auth.toml does not name robin), and a new
; connection's AUTHINFO PASS as robin would find no credential: 481.
(assert-event (null (fn-cfg-delta-reason (as-v2) 3 *as-stamp* 0 0 (as-del "robin"))))
(assert-event (null (fn-auth-find-cred *as-login* (fn-auth-config-creds (as-snap (as-v3))))))
(assert-event (null (fn-auth-find-cred *as-login* (fn-auth-config-creds (as-acfg)))))
; auth.toml's credential for a login is kept: deleting "ember" (no redeemed
; row) leaves the operator's credential found.
(assert-event (equal (fn-auth-find-cred
                      (fn-record-string-octets "ember")
                      (fn-auth-config-creds
                       (as-snap (fn-cfg-apply-delta (as-v2) 3 *as-stamp* (as-del "ember")))))
                     (as-operator-cred)))
; The tooth: over an access rule for robin instead of the deletion, robin's
; credential is still offered, so the statement is the deletion's.
(must-fail-checked
 (defthm as-delete-keystone-over-another-delta
   (equal (fn-auth-find-cred
           (fn-record-string-octets login)
           (fn-auth-config-creds
            (fn-auth-config-with-accounts
             acfg (fn-cfg-apply-delta v gen stamp
                                      (fn-cfg-account-access login "*" "*")))))
          (fn-auth-find-cred (fn-record-string-octets login)
                             (fn-auth-config-creds acfg)))))
(assert-event (fn-auth-find-cred
               *as-login*
               (fn-auth-config-creds
                (as-snap (fn-cfg-apply-delta (as-v2) 3 *as-stamp*
                                             (fn-cfg-account-access "robin" "*" "*"))))))

; -----------------------------------------------------------------------------
; fn-auth-config-with-accounts-is-a-config (the snapshot the host's
; connection takes is a policy).  Positive witness: auth.toml's policy and
; the configuration with robin's redeemed row.
(assert-event (fn-auth-configp (as-acfg)))
(assert-event (fn-auth-configp (fn-auth-config-with-accounts (as-acfg) (as-v2))))
; Hypothesis removed: a malformed policy stays malformed.
(assert-event (not (fn-auth-configp :junk)))
(must-fail-checked
 (assert-event (fn-auth-configp (fn-auth-config-with-accounts :junk (as-v2)))))

; fn-auth-account-creds-find-the-row.  Positive witness: robin's redeemed
; row (n = 1, a well-formed credential), alone and ahead of another row.
(defmacro as-row () '(car (fn-cfg-accounts (as-v2))))
(defmacro as-row-login () '(fn-record-string-octets (fn-cfg-row-b (as-row))))
(assert-event (and (equal (fn-cfg-row-n (as-row)) 1)
                   (fn-auth-credp (fn-auth-account-cred (as-row)))))
(assert-event (equal (fn-auth-find-cred (as-row-login) (fn-auth-account-creds (list (as-row))))
                     (fn-auth-account-cred (as-row))))
(assert-event (equal (fn-auth-find-cred (as-row-login)
                                        (fn-auth-account-creds
                                         (list (as-row) (car (fn-cfg-accounts (as-v1))))))
                     (fn-auth-account-cred (as-row))))
; Hypothesis (equal (fn-cfg-row-n row) 1) removed: the same row with state
; 2 keeps a well-formed credential and is not found.
(defmacro as-row-2 () '(update-nth 3 2 (as-row)))
(assert-event (and (not (equal (fn-cfg-row-n (as-row-2)) 1))
                   (fn-auth-credp (fn-auth-account-cred (as-row-2)))))
(must-fail-checked
 (assert-event (equal (fn-auth-find-cred (as-row-login) (fn-auth-account-creds (list (as-row-2))))
                      (fn-auth-account-cred (as-row-2)))))
; Hypothesis (fn-auth-credp (fn-auth-account-cred row)) removed: a redeemed
; row whose verifier text does not decode is not found.
(defmacro as-row-junk () '(update-nth 2 "junk" (as-row)))
(assert-event (and (equal (fn-cfg-row-n (as-row-junk)) 1)
                   (not (fn-auth-credp (fn-auth-account-cred (as-row-junk))))))
(must-fail-checked
 (assert-event (equal (fn-auth-find-cred (as-row-login) (fn-auth-account-creds (list (as-row-junk))))
                      (fn-auth-account-cred (as-row-junk)))))

; fn-acct-bound-row-succeeds.  Positive witness: robin's redeemed row is
; bound, another invite is admitted at generation 3, and the row after it
; is the same row (a successor).
(defmacro as-digest () '(fn-acct-code-digest-text *as-code*))
(defmacro as-invite-2 ()
  '(fn-cfg-account-invite (fn-acct-code-digest-text (fn-record-string-octets "k3y-friend-0002-aaaa"))
                          "operator" "2000000000"))
(defmacro as-succeeds (v gen deltas)
  `(fn-acct-row-successorp
    (fn-cfg-account-row (fn-cfg-accounts ,v) (as-digest))
    (fn-cfg-account-row (fn-cfg-accounts (fn-cfg-apply ,v ,gen *as-stamp* ,deltas)) (as-digest))))
(assert-event (and (fn-acct-boundp (fn-cfg-accounts (as-v2)) (as-digest))
                   (fn-cfg-admissiblep (as-v2) 3 *as-stamp* 0 510 (list (as-invite-2)))))
(assert-event (as-succeeds (as-v2) 3 (list (as-invite-2))))
; Hypothesis fn-acct-boundp removed: the pending row of generation 1 is not
; bound; the admitted redeem changes it into a row that is no successor.
(defmacro as-redeem () '(fn-acct-plan-delta (fn-acct-redeem-plan (as-v1) *as-stamp* *as-code*
                                                                 *as-login* *as-password*
                                                                 *as-salt* nil)))
(assert-event (and (not (fn-acct-boundp (fn-cfg-accounts (as-v1)) (as-digest)))
                   (fn-cfg-admissiblep (as-v1) 2 *as-stamp* 0 510 (list (as-redeem)))))
(must-fail-checked (assert-event (as-succeeds (as-v1) 2 (list (as-redeem)))))
; Hypothesis fn-cfg-admissiblep removed: re-inviting robin's digest is
; refused (:account-digest-reused); applied anyway it replaces the bound row.
(defmacro as-reinvite () '(fn-cfg-account-invite (as-digest) "operator" "2000000000"))
(assert-event (and (fn-acct-boundp (fn-cfg-accounts (as-v2)) (as-digest))
                   (equal (fn-cfg-admissible-reason (as-v2) 3 *as-stamp* 0 510 (list (as-reinvite)))
                          :account-digest-reused)))
(must-fail-checked (assert-event (as-succeeds (as-v2) 3 (list (as-reinvite)))))
