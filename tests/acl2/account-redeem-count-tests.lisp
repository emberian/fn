;; Teeth for books/account-redeem-count (PKT-399): the keystone's antecedent
;; and conclusion on a live configuration holding a redeemed account (mark 1),
;; a pending invitation (mark 0) and a login-to-principal binding (mark 2);
;; its one hypothesis removed (CORRUPTED); a labelled mutation.  crypto-attach
;; makes the code digest SHA-256, so every value computed through it is a
;; zero-argument macro, not a `defconst' (tests/acl2/accounts-tests.lisp).
(in-package "ACL2")
(include-book "../../books/account-redeem-count")
(include-book "../../books/crypto-attach")
(include-book "must-fail-checked")

(defconst *arct-code* (fn-record-string-octets "k3y-friend-0001-7f3a"))
(defconst *arct-code-2* (fn-record-string-octets "k3y-friend-0002-19c4"))
(defconst *arct-login* (fn-record-string-octets "robin"))
(defconst *arct-login-2* (fn-record-string-octets "mallory"))
(defconst *arct-password* (fn-record-string-octets "correct horse"))
(defconst *arct-salt* (make-list 16 :initial-element 7))
(defconst *arct-stamp* (fn-clock-observation 5 1700000000 2 t))
(defmacro arct-v1 ()
  '
  (fn-cfg-apply-delta (fn-cfg-empty-value) 1 *arct-stamp*
                      (fn-cfg-account-invite (fn-acct-code-digest-text *arct-code*)
                                             "operator" "2000000000")))
(defmacro arct-v2 ()
  '
  (fn-cfg-apply-delta (arct-v1) 2 *arct-stamp*
                      (fn-acct-plan-delta
                       (fn-acct-redeem-plan (arct-v1) *arct-stamp* *arct-code* *arct-login*
                                            *arct-password* *arct-salt* nil))))
(defmacro arct-v3 ()
  '
  (fn-cfg-apply-delta (arct-v2) 3 *arct-stamp*
                      (fn-cfg-account-invite (fn-acct-code-digest-text *arct-code-2*)
                                             "operator" "2000000000")))
(defmacro arct-v4 ()
  '
  (fn-cfg-apply-delta (arct-v3) 4 *arct-stamp*
                      (fn-cfg-login-binding
                       "robin"
                       "0000000000000000000000000000000000000000000000000000000000000000")))
(defconst *arct-auth* (fn-auth-make-config nil nil nil nil))

;; The keystone's two sides, for one table and one bound.
(defmacro arct-plan (auth bound)
  `(fn-arc-redeem-plan (arct-v4) ,auth *arct-stamp* *arct-code-2* *arct-login-2*
                       *arct-password* *arct-salt* ,bound))
(defmacro arct-spec (auth bound)
  `(let ((takenp (and (fn-auth-find-cred *arct-login-2* (fn-arc-creds ,auth (arct-v4))) t)))
     (if (and (equal (car (fn-acct-redeem-plan (arct-v4) *arct-stamp* *arct-code-2*
                                               *arct-login-2* *arct-password* *arct-salt*
                                               takenp))
                     :redeem)
              (not (< (+ (len (fn-auth-config-creds ,auth))
                         (len (fn-auth-account-creds (fn-cfg-accounts (arct-v4)))))
                      (nfix ,bound))))
         (list :refused :account-credential-bound)
       (fn-acct-redeem-plan (arct-v4) *arct-stamp* *arct-code-2* *arct-login-2*
                            *arct-password* *arct-salt* takenp))))

;; fn-arc-redeem-refuses-exactly-past-the-operator-bound, REACHABLE positive:
;; the live value holds three account rows, and only the redeemed one is a
;; credential: the pending invitation and the binding are not counted.
(assert-event (fn-auth-configp *arct-auth*))
(assert-event (equal (len (fn-cfg-accounts (arct-v4))) 3))
(assert-event (equal (len (fn-arc-creds *arct-auth* (arct-v4))) 1))
(assert-event (equal (car (fn-acct-redeem-plan (arct-v4) *arct-stamp* *arct-code-2*
                                               *arct-login-2* *arct-password* *arct-salt*
                                               nil))
                     :redeem))
;; Under the bound (2) the plan redeems; at it (1) it refuses; both equal
;; the statement's right-hand side.
(assert-event (equal (car (arct-plan *arct-auth* 2)) :redeem))
(assert-event (equal (arct-plan *arct-auth* 2) (arct-spec *arct-auth* 2)))
(assert-event (equal (arct-plan *arct-auth* 1) '(:refused :account-credential-bound)))
(assert-event (equal (arct-plan *arct-auth* 1) (arct-spec *arct-auth* 1)))
;; auth.toml's credentials count too: one there and one redeemed reach 2.
(defmacro arct-auth-2 ()
  '(fn-auth-make-config nil nil nil
                       (list (fn-auth-make-cred (fn-record-string-octets "oper")
                                                (fn-acct-local-principal
                                                 (fn-record-string-octets "oper"))
                                                (fn-auth-cred-secret
                                                 (car (fn-arc-creds *arct-auth* (arct-v4))))
                                                t))))
(assert-event (fn-auth-configp (arct-auth-2)))
(assert-event (equal (len (fn-arc-creds (arct-auth-2) (arct-v4))) 2))
(assert-event (equal (arct-plan (arct-auth-2) 2) '(:refused :account-credential-bound)))
(assert-event (equal (arct-plan (arct-auth-2) 2) (arct-spec (arct-auth-2) 2)))

;; Hypothesis removal (CORRUPTED): an AUTHINFO configuration whose credential
;; slot holds no credentials is no configuration, so the live accounts are
;; not appended; the statement counts 3 + 1 against BOUND 4 and refuses,
;; while the plan counts the slot's 3 and redeems.
(defconst *arct-auth-bad* (list :fn-auth-config nil nil nil '(1 2 3)))
(assert-event (not (fn-auth-configp *arct-auth-bad*)))
(assert-event (equal (car (arct-plan *arct-auth-bad* 4)) :redeem))
(assert-event (equal (arct-spec *arct-auth-bad* 4) '(:refused :account-credential-bound)))
(must-fail-checked
 (defthm arct-without-configp
   (let ((takenp (and (fn-auth-find-cred login (fn-arc-creds auth v)) t)))
     (equal (fn-arc-redeem-plan v auth stamp code login password salt bound)
            (if (and (equal (car (fn-acct-redeem-plan v stamp code login password
                                                      salt takenp))
                            :redeem)
                     (not (< (+ (len (fn-auth-config-creds auth))
                                (len (fn-auth-account-creds (fn-cfg-accounts v))))
                             (nfix bound))))
                (list :refused :account-credential-bound)
              (fn-acct-redeem-plan v stamp code login password salt takenp))))
   :hints (("Goal" :in-theory (disable fn-acct-redeem-plan fn-auth-account-creds)))))

;; MUTATION: count every account row (the pending invitation and the binding
;; included).  At BOUND 2 the mutated count (3) refuses what the plan redeems.
(assert-event (not (< (len (fn-cfg-accounts (arct-v4))) 2)))
(assert-event (equal (car (arct-plan *arct-auth* 2)) :redeem))
