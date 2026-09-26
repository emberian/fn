; Teeth for PRF-164 (books/accounts.lisp and the accounts slot of
; books/config.lisp).  Per keystone: a reachable witness asserting the
; antecedent and the conclusion, and per hypothesis a removal witness showing
; the conclusion failing where the hypothesis fails (AGENTS.md, "Teeth ship
; with each keystone").  crypto-attach makes the digest SHA-256, so every
; value computed through it is a zero-argument macro, not a `defconst'
; (tests/acl2/auth-secret-tests.lisp).
(in-package "ACL2")
(include-book "../../books/accounts")
(include-book "../../books/crypto-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *at-code* (fn-record-string-octets "k3y-friend-0001-7f3a"))
(defconst *at-code-2* (fn-record-string-octets "k3y-friend-0002-19c4"))
(defconst *at-login* (fn-record-string-octets "robin"))
(defconst *at-login-2* (fn-record-string-octets "mallory"))
(defconst *at-password* (fn-record-string-octets "correct horse"))
(defconst *at-salt* (make-list 16 :initial-element 7))
(defconst *at-salt-2* (make-list 16 :initial-element 9))
(defconst *at-stamp* (fn-clock-observation 5 1700000000 2 t))
(defconst *at-stamp-late* (fn-clock-observation 9 1999999999 2 t))
(defconst *at-stamp-no-wall* (fn-clock-observation 9 0 0 nil))

(defmacro at-digest () '(fn-acct-code-digest-text *at-code*))
(defmacro at-digest-2 () '(fn-acct-code-digest-text *at-code-2*))
(defmacro at-invite ()
  '(fn-cfg-account-invite (at-digest) "operator" "2000000000"))
(defmacro at-invite-2 ()
  '(fn-cfg-account-invite (at-digest-2) "operator" "2000000000"))
(defmacro at-v0 () '(fn-cfg-empty-value))
(defmacro at-v1 () '(fn-cfg-apply-delta (at-v0) 1 *at-stamp* (at-invite)))
(defmacro at-plan1 ()
  '(fn-acct-redeem-plan (at-v1) *at-stamp* *at-code* *at-login*
                        *at-password* *at-salt* nil))
(defmacro at-v2 ()
  '(fn-cfg-apply-delta (at-v1) 2 *at-stamp* (fn-acct-plan-delta (at-plan1))))
(defmacro at-row (v digest) `(fn-cfg-account-row (fn-cfg-accounts ,v) ,digest))

; The representation: a digest is 64 hex characters, a verifier's text 96,
; and the text is the verifier.
(assert-event (fn-cfg-account-digestp (at-digest)))
(assert-event (fn-cfg-account-verifier-hexp
               (fn-acct-verifier-text (fn-authsec-enrol *at-salt* *at-password*))))
(assert-event (equal (fn-acct-text-verifier
                      (fn-acct-verifier-text
                       (fn-authsec-enrol *at-salt* *at-password*)))
                     (fn-authsec-enrol *at-salt* *at-password*)))

; -----------------------------------------------------------------------------
; The codec: every old kind encodes byte-identically.  The literal is the
; encoding computed at dev 17ff24aa (the nine-slot configuration) of one
; record carrying one delta of each of the fourteen kinds it knew.
(defconst *at-old-deltas*
  (list (fn-cfg-create-group "local.test" "fn-policy-default-1")
        (fn-cfg-remove-group "local.test")
        (fn-cfg-set-capacity 100)
        (fn-cfg-set-quota "group" "local.test" 7)
        (fn-cfg-set-policy "retention" "keep")
        (fn-cfg-set-listeners (list (fn-cfg-row-make "reader" "127.0.0.1:119" "" 0)))
        (fn-cfg-set-peers (list (fn-cfg-row-make "p" "x" "y" 1)))
        (fn-cfg-set-limit "max-payload" 1000)
        (fn-cfg-set-peer "p" (list (fn-cfg-row-make "p" "eid" "ipn:1.0" 0)))
        (fn-cfg-remove-peer "p")
        (fn-cfg-grant-control "local.*" "ab" "cancel")
        (fn-cfg-revoke-control "local.*" "ab")
        (fn-cfg-issue-invitation "n1" "i" "s")
        (fn-cfg-consume-invitation "n1" "a" "s")))
(assert-event
 (equal (fn-cfg-encode (fn-cfg-record-make 3 9 2 *at-old-deltas*
                                           (fn-clock-observation 5 1700000000 2 t)))
        '(70 102 110 45 99 102 103 0 24 102 3 9 2 5 26 101 83 241 0 2 1 14 1
          74 108 111 99 97 108 46 116 101 115 116 83 102 110 45 112 111 108
          105 99 121 45 100 101 102 97 117 108 116 45 49 0 0 2 74 108 111 99
          97 108 46 116 101 115 116 64 0 0 3 64 64 24 100 0 4 69 103 114 111
          117 112 74 108 111 99 97 108 46 116 101 115 116 7 0 5 73 114 101
          116 101 110 116 105 111 110 68 107 101 101 112 0 0 6 64 64 0 1 70
          114 101 97 100 101 114 77 49 50 55 46 48 46 48 46 49 58 49 49 57 64
          0 7 64 64 0 1 65 112 65 120 65 121 1 8 75 109 97 120 45 112 97 121
          108 111 97 100 64 25 3 232 0 9 65 112 64 0 1 65 112 67 101 105 100
          71 105 112 110 58 49 46 48 0 10 65 112 64 0 0 11 71 108 111 99 97
          108 46 42 66 97 98 0 1 71 108 111 99 97 108 46 42 66 97 98 70 99 97
          110 99 101 108 0 12 71 108 111 99 97 108 46 42 66 97 98 0 0 13 66
          110 49 65 105 0 1 66 110 49 65 105 65 115 0 14 66 110 49 65 97 0 1
          66 110 49 65 97 65 115 1)))
; A value that never saw an account has an empty tenth slot, and the empty
; value is well formed.
(assert-event (equal (fn-cfg-accounts (fn-cfg-apply (at-v0) 1 *at-stamp*
                                                    *at-old-deltas*))
                     nil))
(assert-event (fn-cfg-valuep (fn-cfg-empty-value)))
; The two new kinds round-trip through the record codec.
(defmacro at-rec2 ()
  '(fn-cfg-record-make 2 2 2 (list (fn-acct-plan-delta (at-plan1))) *at-stamp*))
(assert-event (equal (fn-cfg-decode-exact (fn-cfg-encode (at-rec2)))
                     (fn-record-parse-ok (at-rec2) nil)))

; -----------------------------------------------------------------------------
; The invite and the plan

(assert-event (null (fn-cfg-delta-reason (at-v0) 1 *at-stamp* 0 0 (at-invite))))
(assert-event (fn-cfg-account-pendingp (fn-cfg-accounts (at-v1)) (at-digest)))
(assert-event (equal (fn-cfg-delta-reason (at-v1) 1 *at-stamp* 0 0 (at-invite))
                     :account-digest-reused))

; KEYSTONE fn-acct-redeem-plan-is-admitted-and-redeems: reachable witness.
(assert-event (equal (car (at-plan1)) :redeem))
(assert-event (null (fn-cfg-delta-reason (at-v1) 2 *at-stamp* 5 77
                                         (fn-acct-plan-delta (at-plan1)))))
(assert-event (equal (at-row (at-v2) (at-digest))
                     (fn-cfg-row-make (at-digest) "robin"
                                      (fn-acct-verifier-text
                                       (fn-authsec-enrol *at-salt* *at-password*))
                                      1)))
; Removal of (equal (car plan) :redeem): a refused plan carries no delta the
; configuration admits.
(defmacro at-plan-taken ()
  '(fn-acct-redeem-plan (at-v1) *at-stamp* *at-code* *at-login*
                        *at-password* *at-salt* t))
(assert-event (equal (at-plan-taken) '(:refused :account-login-taken)))
(must-fail (assert-event (null (fn-cfg-delta-reason
                                (at-v1) 2 *at-stamp* 0 0
                                (fn-acct-plan-delta (at-plan-taken))))))

; KEYSTONE fn-acct-redeem-plan-after-its-redeem-is-already-redeemed:
; reachable witness (the crash after publication; a later stamp, a new salt
; and a snapshot that now holds the login).
(assert-event (equal (fn-acct-redeem-plan (at-v2) *at-stamp-late* *at-code*
                                          *at-login* *at-password* *at-salt-2* t)
                     '(:already-redeemed)))
; Removal of (equal (car plan) :redeem): an expired plan stages nothing, so
; the next plan (in time) is a first redeem, not a resume.
(defmacro at-plan-expired ()
  '(fn-acct-redeem-plan (at-v1) *at-stamp-late* *at-code* *at-login*
                        *at-password* *at-salt* nil))
(assert-event (equal (at-plan-expired) '(:refused :account-expired)))
(must-fail (assert-event
            (equal (fn-acct-redeem-plan
                    (fn-cfg-apply-delta (at-v1) 2 *at-stamp-late*
                                        (fn-acct-plan-delta (at-plan-expired)))
                    *at-stamp* *at-code* *at-login* *at-password* *at-salt* nil)
                   '(:already-redeemed))))
; A clock without a wall reading refuses (fail closed).
(assert-event (equal (fn-acct-redeem-plan (at-v1) *at-stamp-no-wall* *at-code*
                                          *at-login* *at-password* *at-salt* nil)
                     '(:refused :account-expired)))

; KEYSTONE fn-acct-redeem-plan-refuses-another-login: reachable witness.
(assert-event (fn-cfg-account-redeemedp (fn-cfg-accounts (at-v2)) (at-digest)))
(assert-event (equal (fn-acct-redeem-plan (at-v2) *at-stamp* *at-code*
                                          *at-login-2* *at-password* *at-salt* nil)
                     '(:refused :account-redeemed)))
; Removal of the redeemed hypothesis: while pending, another login redeems.
(must-fail (assert-event
            (equal (fn-acct-redeem-plan (at-v1) *at-stamp* *at-code*
                                        *at-login-2* *at-password* *at-salt* nil)
                   '(:refused :account-redeemed))))
; Removal of the other-login hypothesis: the same login with its password
; resumes.
(must-fail (assert-event
            (equal (fn-acct-redeem-plan (at-v2) *at-stamp* *at-code*
                                        *at-login* *at-password* *at-salt* nil)
                   '(:refused :account-redeemed))))
; The same login with a wrong password is refused, not resumed.
(assert-event (equal (fn-acct-redeem-plan (at-v2) *at-stamp* *at-code* *at-login*
                                          (fn-record-string-octets "guess")
                                          *at-salt* nil)
                     '(:refused :account-redeemed)))

; KEYSTONE fn-acct-redeem-plan-of-an-unknown-code-stages-nothing: witness.
(assert-event (not (consp (at-row (at-v0) (at-digest)))))
(assert-event (equal (fn-acct-redeem-plan (at-v0) *at-stamp* *at-code* *at-login*
                                          *at-password* *at-salt* nil)
                     '(:refused :account-unknown)))
; Removal: with the row, the plan redeems.
(must-fail (assert-event
            (not (equal (car (at-plan1)) :redeem))))

; KEYSTONE fn-acct-redeemed-refuses-another-redeem: reachable witness.
(defmacro at-other-redeem ()
  '(fn-cfg-account-redeem (at-digest) "mallory"
                          (fn-acct-verifier-text
                           (fn-authsec-enrol *at-salt* *at-password*))))
(assert-event (equal (fn-cfg-delta-reason (at-v2) 3 *at-stamp* 0 0
                                          (at-other-redeem))
                     :account-redeemed))
; Removal of the rows-differ hypothesis: the identical redeem is admitted
; (the delta-level resume).
(must-fail (assert-event (fn-cfg-delta-reason (at-v2) 3 *at-stamp* 0 0
                                              (fn-acct-plan-delta (at-plan1)))))
; Removal of the redeemed hypothesis: while pending, that redeem is admitted.
(must-fail (assert-event (fn-cfg-delta-reason (at-v1) 3 *at-stamp* 0 0
                                              (at-other-redeem))))
; Removal of the kind hypothesis: another kind naming the digest is admitted.
(must-fail (assert-event (fn-cfg-delta-reason (at-v2) 3 *at-stamp* 0 0
                                              (fn-cfg-set-limit (at-digest) 1))))
; A login held by a redeemed row refuses a second code's redeem.
(defmacro at-v3 () '(fn-cfg-apply-delta (at-v2) 3 *at-stamp* (at-invite-2)))
(assert-event (equal (fn-acct-redeem-plan (at-v3) *at-stamp* *at-code-2*
                                          *at-login* *at-password* *at-salt* nil)
                     '(:refused :account-login-taken)))

; fn-acct-redeemed-row-stays (and -by-a-delta): witness and removal.
(assert-event (null (fn-cfg-admissible-reason (at-v2) 3 *at-stamp* 0 0
                                              (list (at-invite-2)))))
(assert-event (equal (at-row (fn-cfg-apply (at-v2) 3 *at-stamp*
                                           (list (at-invite-2)))
                             (at-digest))
                     (at-row (at-v2) (at-digest))))
; Removal of admissibility: a re-issued invite of the digest overwrites.
(assert-event (fn-cfg-admissible-reason (at-v2) 3 *at-stamp* 0 0
                                        (list (at-invite))))
(must-fail (assert-event
            (equal (at-row (fn-cfg-apply (at-v2) 3 *at-stamp* (list (at-invite)))
                           (at-digest))
                   (at-row (at-v2) (at-digest)))))
; Removal of redeemed: a pending row changes under an admitted redeem.
(must-fail (assert-event
            (equal (at-row (at-v2) (at-digest)) (at-row (at-v1) (at-digest)))))

; KEYSTONE fn-acct-redeemed-row-stays-across-replay: witness over the fold
; the owner replays at open, from the initial configuration.
(defmacro at-r1 () '(fn-cfg-record-make 1 1 1 (list (at-invite)) *at-stamp*))
(defmacro at-r3 () '(fn-cfg-record-make 3 3 3 (list (at-invite-2)) *at-stamp*))
(defmacro at-r3-bad () '(fn-cfg-record-make 3 3 3 (list (at-invite)) *at-stamp*))
(defmacro at-cfg2 ()
  '(fn-config-replay-loop (fn-cfg-initial) 0 1000 (list (at-r1) (at-rec2))))
(assert-event (not (equal (at-cfg2) :fault)))
(assert-event (fn-cfg-account-redeemedp (fn-cfg-accounts (fn-cfg-value (at-cfg2)))
                                        (at-digest)))
(assert-event (not (equal (fn-config-replay-loop (at-cfg2) 0 1000 (list (at-r3)))
                          :fault)))
(assert-event (equal (at-row (fn-cfg-value (fn-config-replay-loop
                                            (at-cfg2) 0 1000 (list (at-r3))))
                             (at-digest))
                     (at-row (fn-cfg-value (at-cfg2)) (at-digest))))
; Removal of the :fault hypothesis: a record re-issuing the digest is not
; acceptable, and the replay faults rather than overwrite.
(assert-event (equal (fn-config-replay-loop (at-cfg2) 0 1000 (list (at-r3-bad)))
                     :fault))
