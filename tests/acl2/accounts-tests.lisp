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
; PRF-374: the witnesses reach the plan the host builds (fn-native-admin-plan).
(include-book "../../books/native-admin")
(include-book "must-fail-checked")

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

; The representation: a digest is 64 hex characters, a verifier's text 224,
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
(must-fail-checked (assert-event (null (fn-cfg-delta-reason
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
(must-fail-checked (assert-event
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
(must-fail-checked (assert-event
            (equal (fn-acct-redeem-plan (at-v1) *at-stamp* *at-code*
                                        *at-login-2* *at-password* *at-salt* nil)
                   '(:refused :account-redeemed))))
; Removal of the other-login hypothesis: the same login with its password
; resumes.
(must-fail-checked (assert-event
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
(must-fail-checked (assert-event
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
(must-fail-checked (assert-event (fn-cfg-delta-reason (at-v2) 3 *at-stamp* 0 0
                                              (fn-acct-plan-delta (at-plan1)))))
; Removal of the redeemed hypothesis: while pending, that redeem is admitted.
(must-fail-checked (assert-event (fn-cfg-delta-reason (at-v1) 3 *at-stamp* 0 0
                                              (at-other-redeem))))
; Removal of the kind hypothesis: another kind naming the digest is admitted.
(must-fail-checked (assert-event (fn-cfg-delta-reason (at-v2) 3 *at-stamp* 0 0
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
(must-fail-checked (assert-event
            (equal (at-row (fn-cfg-apply (at-v2) 3 *at-stamp* (list (at-invite)))
                           (at-digest))
                   (at-row (at-v2) (at-digest)))))
; Removal of redeemed: a pending row changes under an admitted redeem.
(must-fail-checked (assert-event
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

; -----------------------------------------------------------------------------
; PKT-439: the owner's bounded plan, the word, the invite (friends-accounts-2)

(defmacro at-bplan (v used bound)
  `(fn-acct-redeem-bounded-plan ,v *at-stamp* *at-code* *at-login*
                                *at-password* *at-salt* nil ,used ,bound))

; KEYSTONE fn-acct-redeem-bounded-plan-refuses-exactly-past-the-operator-bound
; (natp used) (natp bound) (plan :redeem) => bounded = (if (< used bound) plan
; refused).  Witness on both sides of the bound, from a real pending row.
(assert-event (equal (car (at-plan1)) :redeem))
(assert-event (equal (at-bplan (at-v1) 3 4) (at-plan1)))
(assert-event (equal (at-bplan (at-v1) 4 4) '(:refused :account-credential-bound)))
; (natp used) removed: USED = 5/2 against BOUND 2; every other hypothesis
; holds; nfix reads 0, so the plan redeems where the statement says refused.
(assert-event (and (not (natp 5/2)) (natp 2) (equal (car (at-plan1)) :redeem)
                   (not (equal (at-bplan (at-v1) 5/2 2)
                               (if (< 5/2 2) (at-plan1)
                                 '(:refused :account-credential-bound))))))
; (natp bound) removed: BOUND = 1/2 against USED 0.
(assert-event (and (natp 0) (not (natp 1/2)) (equal (car (at-plan1)) :redeem)
                   (not (equal (at-bplan (at-v1) 0 1/2)
                               (if (< 0 1/2) (at-plan1)
                                 '(:refused :account-credential-bound))))))
; (plan :redeem) removed: the resume on the redeemed row is never refused by
; the bound, so the statement's refusal is false there.
(assert-event (and (natp 5) (natp 1)
                   (equal (car (fn-acct-redeem-plan (at-v2) *at-stamp* *at-code*
                                                    *at-login* *at-password*
                                                    *at-salt* nil))
                          :already-redeemed)
                   (not (equal (at-bplan (at-v2) 5 1)
                               '(:refused :account-credential-bound)))))

; KEYSTONE fn-acct-redeem-word-is-bound-only-after-a-durable-redeem.
(assert-event (equal (fn-acct-redeem-word (at-plan1) :accepted) :bound))
(assert-event (equal (fn-acct-redeem-word '(:already-redeemed) :refused) :bound))
; Hypothesis removed: a :redeem plan whose publication was refused is not
; :bound, and the conclusion fails for it.
(assert-event (and (not (equal (fn-acct-redeem-word (at-plan1) :refused) :bound))
                   (not (or (equal (car (at-plan1)) :already-redeemed)
                            (and (equal (car (at-plan1)) :redeem)
                                 (equal :refused :accepted))))))

; KEYSTONE fn-acct-redeem-word-of-an-unknown-code-is-refused.
(assert-event (not (consp (at-row (at-v0) (at-digest)))))
(assert-event (equal (fn-acct-redeem-word (at-bplan (at-v0) 0 5) :accepted)
                     :refused))
; Hypothesis removed: the code's pending row exists, and the word is :bound.
(assert-event (and (consp (at-row (at-v1) (at-digest)))
                   (equal (fn-acct-redeem-word (at-bplan (at-v1) 0 5) :accepted)
                          :bound)))

; KEYSTONE fn-acct-redeem-bounded-plan-after-its-redeem-is-bound (the crash
; cut between the publication and the reply).
(defmacro at-bv2 ()
  '(fn-cfg-apply-delta (at-v1) 2 *at-stamp*
                       (fn-acct-plan-delta (at-bplan (at-v1) 0 5))))
(assert-event (equal (car (at-bplan (at-v1) 0 5)) :redeem))
(assert-event (equal (fn-acct-redeem-bounded-plan (at-bv2) *at-stamp-late*
                                                  *at-code* *at-login*
                                                  *at-password* *at-salt-2* t
                                                  9 9)
                     '(:already-redeemed)))
(assert-event (equal (fn-acct-redeem-word
                      (fn-acct-redeem-bounded-plan (at-bv2) *at-stamp-late*
                                                   *at-code* *at-login*
                                                   *at-password* *at-salt-2* t
                                                   9 9)
                      :refused)
                     :bound))
; Hypothesis removed: a plan refused at the bound stages nothing, so the
; retry is not a resume.
(assert-event
 (and (not (equal (car (at-bplan (at-v1) 5 5)) :redeem))
      (not (equal (fn-acct-redeem-bounded-plan
                   (fn-cfg-apply-delta (at-v1) 2 *at-stamp*
                                       (fn-acct-plan-delta (at-bplan (at-v1) 5 5)))
                   *at-stamp* *at-code* *at-login* *at-password* *at-salt* nil
                   0 5)
                  '(:already-redeemed)))))

; The invite: the code's text, its pending row, and the row's liveness.
(defconst *at-entropy* '(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 250))
(assert-event (equal (fn-acct-code-text *at-entropy*)
                     "000102030405060708090a0b0c0d0efa"))
(assert-event (null (fn-acct-code-text (cdr *at-entropy*))))
(defconst *at-reading* (fn-acct-live-invite-reading *at-stamp*))
(defconst *at-reading-no-wall* (fn-acct-live-invite-reading *at-stamp-no-wall*))
(defmacro at-inv-delta ()
  '(fn-acct-invite-delta (fn-acct-code-digest-text
                          (fn-record-string-octets
                           (fn-acct-code-text *at-entropy*)))
                         60 *at-reading*))
(assert-event (null (fn-cfg-delta-reason (at-v0) 1 *at-stamp* 0 0 (at-inv-delta))))
(assert-event (equal (fn-acct-invite-expiry 60 *at-reading*) 1700060002))
(assert-event (< (fn-clock-reading-latest-milliseconds *at-reading*)
                 (fn-acct-invite-expiry 60 *at-reading*)))
; Hypothesis of fn-acct-invite-delta-is-live-at-its-stamp removed: no wall
; clock, no expiry, and the comparison fails.  The conclusion's `<' reads a
; non-number as 0 in the logic; `fix' says so, since evaluating (< 0 nil)
; is a guard violation, which refused the whole book.
(assert-event (and (null (fn-acct-invite-expiry 60 *at-reading-no-wall*))
                   (null (fn-acct-invite-delta "x" 60 *at-reading-no-wall*))
                   (not (< (fix (fn-clock-reading-latest-milliseconds
                                 *at-reading-no-wall*))
                           (fix (fn-acct-invite-expiry 60 *at-reading-no-wall*))))))
; A bare observation is not a reading: no unit, no expiry (the call shape
; bug M1 had).
(assert-event (null (fn-acct-invite-expiry 60 *at-stamp*)))

; PRF-374 (bug M1): the running and the stopped path, through the plan the
; host builds (host/native-admin-host.lisp fn-acct-host-invite-argv) and the
; readings each path passes (fn-acct-live-invite-reading of the owner's
; milliseconds clock; fn-acct-offline-invite-reading of the record stamp,
; milliseconds too since PRF-378).  The instant is 2026-09-28 in DTN milliseconds.
(defconst *at-now-ms* 812345678901)
(defmacro at-inv-plan ()
  '(fn-native-admin-plan
   (list (fn-record-string-octets "account") (fn-record-string-octets "invite")
         (fn-record-string-octets (at-digest)) (fn-record-string-octets "3600"))))
(defconst *at-live-reading*
  (fn-acct-live-invite-reading (fn-clock-observation 7 *at-now-ms* 250 t)))
(defconst *at-offline-reading*
  (fn-acct-offline-invite-reading (fn-clock-observation 3 *at-now-ms* 250 t)))
; Positive witness of fn-acct-admin-deltas-expire-at-now-plus-expires-on-both-paths:
; every hypothesis holds of the reached plan, and both conclusions.
(assert-event
 (and (equal (fn-native-admin-result-status (at-inv-plan)) :accepted)
      (equal (fn-native-admin-result-kind (at-inv-plan)) :account-invite)
      (equal (fn-native-admin-result-capacity (at-inv-plan)) 3600)
      (equal (fn-acct-admin-deltas (at-inv-plan) *at-live-reading*)
             (list (fn-cfg-account-invite (at-digest) "operator"
                                          "812349279151")))
      (equal (fn-acct-admin-deltas (at-inv-plan) *at-offline-reading*)
             (list (fn-cfg-account-invite (at-digest) "operator"
                                          "812349279151")))))
; Positive witness of fn-acct-invite-expiry-agrees-across-the-running-and-stopped-paths
; (no hypotheses): at the reached observation both paths give the same
; expiry, now + one hour in milliseconds.
(assert-event
 (let ((obs (fn-clock-observation 7 *at-now-ms* 250 t)))
   (and (equal (fn-acct-invite-expiry 3600 (fn-acct-offline-invite-reading obs))
               (+ *at-now-ms* 250 3600000))
        (equal (fn-acct-invite-expiry 3600 (fn-acct-offline-invite-reading obs))
               (fn-acct-invite-expiry 3600 (fn-acct-live-invite-reading obs))))))
; Mutation witness (labelled): a reading that names the stamp :seconds (the
; pre-PRF-378 record stamp) disagrees with the running path by the factor
; the keystone refutes.
(assert-event
 (let ((obs (fn-clock-observation 7 *at-now-ms* 250 t)))
   (not (equal (fn-acct-invite-expiry 3600 (fn-clock-reading :seconds obs))
               (fn-acct-invite-expiry 3600 (fn-acct-live-invite-reading obs))))))
; The redeem side: the owner's clock one minute after issue (milliseconds,
; the redeem plan's stamp) finds the stopped path's row live, and an hour
; and a second later expired.  Bug M1's row (seconds + 1000 x expires) is
; already expired at the issuing instant.
(defmacro at-offline-row ()
  '(car (fn-cfg-delta-rows
        (car (fn-acct-admin-deltas (at-inv-plan) *at-offline-reading*)))))
(assert-event
 (and (fn-cfg-account-livep (at-offline-row)
                            (fn-clock-observation 9 (+ *at-now-ms* 60000) 250 t))
      (not (fn-cfg-account-livep (at-offline-row)
                                 (fn-clock-observation 9 (+ *at-now-ms* 3601000)
                                                       0 t)))))
; Mutation witness (labelled): the pre-fix arithmetic, the record stamp's
; seconds read as milliseconds, is expired at issue.
(assert-event
 (not (fn-cfg-account-livep
       (fn-cfg-row-make (at-digest) "operator"
                        (fn-acct-decimal-text
                         (+ (floor *at-now-ms* 1000) (* 1000 3600)))
                        0)
       (fn-clock-observation 9 *at-now-ms* 250 t))))
; Hypothesis-removal witnesses.  The status and kind hypotheses: a refused
; plan and another verb's plan stage nothing on either path, so the
; conclusion fails while every other hypothesis holds.
(defconst *at-other-plan*
  (fn-native-admin-plan
   (list (fn-record-string-octets "account") (fn-record-string-octets "list"))))
(assert-event
 (and (not (equal (fn-native-admin-result-kind *at-other-plan*) :account-invite))
      (null (fn-acct-admin-deltas *at-other-plan* *at-live-reading*))
      (null (fn-acct-admin-deltas *at-other-plan* *at-offline-reading*))))
; The capacity hypothesis.  The planner refuses `--expires 0' by itself
; (the reached plan is (:refused :account)), so the witness is a
; CONSTRUCTED plan (not reachable through fn-native-admin-plan): accepted,
; an invite, capacity 0; every other hypothesis holds and the conclusion
; fails on both paths (nothing is staged).
(defmacro at-zero-plan ()
  '(fn-native-admin-result :accepted nil :account-invite
                           (fn-native-admin-result-name (at-inv-plan)) 0 nil nil))
(assert-event
 (and (equal (fn-native-admin-result-status (at-zero-plan)) :accepted)
      (equal (fn-native-admin-result-kind (at-zero-plan)) :account-invite)
      (not (posp (fn-native-admin-result-capacity (at-zero-plan))))
      (equal (fn-native-admin-result-status
              (fn-native-admin-plan
               (list (fn-record-string-octets "account")
                     (fn-record-string-octets "invite")
                     (fn-record-string-octets (at-digest))
                     (fn-record-string-octets "0"))))
             :refused)
      (null (fn-acct-admin-deltas (at-zero-plan) *at-live-reading*))
      (null (fn-acct-admin-deltas (at-zero-plan) *at-offline-reading*))))
; The wall and error hypotheses (natp wall, natp err): a reading whose
; wall or error bound is not a natural stages nothing on the running path
; (the plan's hypotheses hold).
(assert-event
 (and (equal (fn-native-admin-result-status (at-inv-plan)) :accepted)
      (null (fn-acct-admin-deltas (at-inv-plan)
                                  (fn-acct-live-invite-reading
                                   (fn-clock-observation 7 -5 0 t))))
      (null (fn-acct-admin-deltas (at-inv-plan)
                                  (fn-acct-live-invite-reading
                                   (fn-clock-observation 7 5 -1 t))))))

; `account list' (books/account-list.lisp, tests/acl2/account-list-tests.lisp)
; names logins and principals, never a digest.

; -----------------------------------------------------------------------------
; public-node-2: `account delete LOGIN' (code 27) and the once-only keystone
; restated over the tombstone.

(defmacro at-del () '(fn-cfg-account-delete "robin"))
(defmacro at-v-del () '(fn-cfg-apply-delta (at-v2) 3 *at-stamp* (at-del)))
(defmacro at-tomb () '(fn-cfg-account-deleted-row (at-row (at-v2) (at-digest))))

; The redeemed row, then its tombstone: same digest and login, no verifier.
(assert-event (fn-cfg-account-redeemedp (fn-cfg-accounts (at-v2)) (at-digest)))
(assert-event (equal (fn-cfg-row-b (at-row (at-v2) (at-digest))) "robin"))
(assert-event (null (fn-cfg-delta-reason (at-v2) 3 *at-stamp* 0 0 (at-del))))
(assert-event (equal (at-row (at-v-del) (at-digest))
                     (fn-cfg-row-make (at-digest) "robin" "" 7)))

; KEYSTONE fn-acct-bound-row-succeeds-by-a-delta: reachable, non-degenerate
; witness (the successor is the tombstone, not the row itself).
(assert-event (fn-acct-boundp (fn-cfg-accounts (at-v2)) (at-digest)))
(assert-event (fn-acct-row-successorp (at-row (at-v2) (at-digest))
                                      (at-row (at-v-del) (at-digest))))
(assert-event (not (equal (at-row (at-v-del) (at-digest))
                          (at-row (at-v2) (at-digest)))))
; A tombstone's successor is itself only: a second delete is admitted (the
; resume) and changes nothing.
(assert-event (fn-acct-boundp (fn-cfg-accounts (at-v-del)) (at-digest)))
(assert-event (null (fn-cfg-delta-reason (at-v-del) 4 *at-stamp* 0 0 (at-del))))
(assert-event (equal (at-row (fn-cfg-apply-delta (at-v-del) 4 *at-stamp* (at-del))
                             (at-digest))
                     (at-row (at-v-del) (at-digest))))
; Removal of boundp: a pending row's admitted redeem is no successor.
(assert-event (not (fn-acct-boundp (fn-cfg-accounts (at-v1)) (at-digest))))
(assert-event (null (fn-cfg-delta-reason (at-v1) 2 *at-stamp* 0 0
                                         (fn-acct-plan-delta (at-plan1)))))
(must-fail-checked (assert-event
                    (fn-acct-row-successorp (at-row (at-v1) (at-digest))
                                            (at-row (at-v2) (at-digest)))))
; Removal of admission: an invite of the digest is refused, and applied
; anyway it overwrites the bound row with a pending one.
(assert-event (fn-cfg-delta-reason (at-v2) 3 *at-stamp* 0 0 (at-invite)))
(must-fail-checked (assert-event
                    (fn-acct-row-successorp
                     (at-row (at-v2) (at-digest))
                     (at-row (fn-cfg-apply-delta (at-v2) 3 *at-stamp* (at-invite))
                             (at-digest)))))

; KEYSTONE fn-acct-bound-row-succeeds-across-replay: the fold the owner
; replays at open, from the initial configuration, through the deletion.
(defmacro at-r4-del () '(fn-cfg-record-make 3 3 3 (list (at-del)) *at-stamp*))
(assert-event (not (equal (fn-config-replay-loop (at-cfg2) 0 1000 (list (at-r4-del)))
                          :fault)))
(assert-event (equal (at-row (fn-cfg-value (fn-config-replay-loop
                                            (at-cfg2) 0 1000 (list (at-r4-del))))
                             (at-digest))
                     (at-tomb)))
(assert-event (fn-acct-row-successorp
               (at-row (fn-cfg-value (at-cfg2)) (at-digest))
               (at-row (fn-cfg-value (fn-config-replay-loop
                                      (at-cfg2) 0 1000 (list (at-r4-del))))
                       (at-digest))))
; Removal of the :fault hypothesis: as before, a re-issue faults.
(assert-event (equal (fn-config-replay-loop (at-cfg2) 0 1000 (list (at-r3-bad)))
                     :fault))
; The replaced statement (the row's equality) is what `account delete'
; falsifies, by design.
(must-fail-checked (assert-event
                    (equal (at-row (fn-cfg-value (fn-config-replay-loop
                                                  (at-cfg2) 0 1000 (list (at-r4-del))))
                                   (at-digest))
                           (at-row (fn-cfg-value (at-cfg2)) (at-digest)))))

; A deleted account's code is never redeemed again, by anyone: its row is
; a tombstone, so the redeem is refused :account-row.
(assert-event (equal (fn-acct-redeem-plan (at-v-del) *at-stamp* *at-code*
                                          *at-login* *at-password* *at-salt* nil)
                     '(:refused :account-row)))

; KEYSTONE fn-acct-delete-keeps-the-login-taken: witness and removal.
(assert-event (fn-cfg-account-login-takenp (fn-cfg-accounts (at-v2)) "robin"))
(assert-event (fn-cfg-account-login-takenp
               (fn-cfg-rows-deleting-account (fn-cfg-accounts (at-v2)) "robin")
               "robin"))
; A second code's redeem under the deleted login is refused.
(defmacro at-v-del-2 () '(fn-cfg-apply-delta (at-v-del) 4 *at-stamp* (at-invite-2)))
(assert-event (equal (fn-acct-redeem-plan (at-v-del-2) *at-stamp* *at-code-2*
                                          *at-login* *at-password* *at-salt* nil)
                     '(:refused :account-login-taken)))
; Removal of the hypothesis: a login no row holds is not taken afterwards.
(assert-event (not (fn-cfg-account-login-takenp (fn-cfg-accounts (at-v2)) "mallory")))
(must-fail-checked (assert-event
                    (fn-cfg-account-login-takenp
                     (fn-cfg-rows-deleting-account (fn-cfg-accounts (at-v2)) "robin")
                     "mallory")))

; KEYSTONE fn-acct-delete-is-admitted-exactly-when-held-and-unobligated.
; All three conjuncts hold: admitted (above).  Each fails alone:
;   the login is not well formed,
(assert-event (equal (fn-cfg-delta-reason (at-v2) 3 *at-stamp* 0 0
                                          (fn-cfg-account-delete "no spaces"))
                     :account-login))
;   no account holds it,
(assert-event (equal (fn-cfg-delta-reason (at-v2) 3 *at-stamp* 0 0
                                          (fn-cfg-account-delete "mallory"))
                     :account-unknown))
;   an obligation names it: a consumer bound to robin, a signing binding,
;   a moderator role.
(defmacro at-v-bound (d) `(fn-cfg-apply-delta (at-v2) 3 *at-stamp* ,d))
(assert-event (equal (fn-cfg-delta-reason
                      (at-v-bound (fn-cfg-consumer-bind "robin-inbox" "robin"))
                      4 *at-stamp* 0 0 (at-del))
                     :account-obligations))
(assert-event (equal (fn-cfg-delta-reason
                      (at-v-bound (fn-cfg-login-binding
                                   "robin"
                                   "0000000000000000000000000000000000000000000000000000000000000000"))
                      4 *at-stamp* 0 0 (at-del))
                     :account-obligations))
(assert-event (equal (fn-cfg-delta-reason
                      (fn-cfg-value-make-full
                       (fn-cfg-groups (at-v2)) (fn-cfg-capacity (at-v2))
                       (fn-cfg-quotas (at-v2)) (fn-cfg-policies (at-v2))
                       (fn-cfg-listeners (at-v2)) (fn-cfg-peers (at-v2))
                       (fn-cfg-limits (at-v2)) (fn-cfg-authorities (at-v2))
                       (fn-cfg-invitations (at-v2))
                       (append (fn-cfg-accounts (at-v2))
                               (fn-cfg-moderator-rows "local.mod" '("robin")))
                       (fn-cfg-descriptions (at-v2)))
                      4 *at-stamp* 0 0 (at-del))
                     :account-obligations))
; An access rule is no obligation.
(assert-event (null (fn-cfg-delta-reason
                     (at-v-bound (fn-cfg-account-access "robin" "local.*" "local.*"))
                     4 *at-stamp* 0 0 (at-del))))
; Each conjunct dropped from the right-hand side: the iff fails.
(defmacro at-delete-iff-without (rhs)
  `(defthm at-delete-iff-weakened
     (iff (fn-cfg-delta-reason v gen stamp reserved ceiling
                               (fn-cfg-account-delete login))
          (not ,rhs))
     :hints (("Goal" :in-theory (e/d (fn-cfg-delta-reason
                                      fn-cfg-account-delete-reason)
                                     (fn-cfg-account-loginp
                                      fn-cfg-account-heldp
                                      fn-cfg-account-obligation))
              :expand ((fn-cfg-account-delete login))))))
(must-fail-checked
 (at-delete-iff-without
  (and (fn-cfg-account-heldp (fn-cfg-accounts v) login)
       (not (fn-cfg-account-obligation (fn-cfg-accounts v) login)))))
(must-fail-checked
 (at-delete-iff-without
  (and (fn-cfg-account-loginp login)
       (not (fn-cfg-account-obligation (fn-cfg-accounts v) login)))))
(must-fail-checked
 (at-delete-iff-without
  (and (fn-cfg-account-loginp login)
       (fn-cfg-account-heldp (fn-cfg-accounts v) login))))


; -----------------------------------------------------------------------------
; PRF-379: a stopped node's `account invite' with an unreadable wall clock.

(defconst *at-wall-stamp* (fn-clock-observation 3 *at-now-ms* 0 t))
(defconst *at-blind-stamp* (fn-clock-observation 3 0 0 nil))
; KEYSTONE fn-acct-offline-invite-refusal-is-no-clock-exactly-without-a-wall:
; positive witnesses on the reached plan, one per value of the wall claim.
(assert-event
 (and (equal (fn-native-admin-result-status (at-inv-plan)) :accepted)
      (equal (fn-native-admin-result-kind (at-inv-plan)) :account-invite)
      (posp (fn-native-admin-result-capacity (at-inv-plan)))
      (fn-clock-observationp *at-blind-stamp*)
      (fn-clock-observationp *at-wall-stamp*)
      (equal (fn-acct-offline-invite-refusal (at-inv-plan) *at-blind-stamp*)
             :no-clock)
      (null (fn-acct-offline-invite-refusal (at-inv-plan) *at-wall-stamp*))))
; Hypothesis removal.  Status and kind: another verb's plan, at a stamp with
; a wall, is refused (nothing to stage), so the conclusion's nil fails.
(assert-event
 (and (not (equal (fn-native-admin-result-kind *at-other-plan*) :account-invite))
      (fn-clock-observationp *at-wall-stamp*)
      (equal (fn-acct-offline-invite-refusal *at-other-plan* *at-wall-stamp*)
             :no-clock)))
; Capacity: the constructed zero-capacity plan (every other hypothesis holds).
(assert-event
 (and (equal (fn-native-admin-result-status (at-zero-plan)) :accepted)
      (equal (fn-native-admin-result-kind (at-zero-plan)) :account-invite)
      (not (posp (fn-native-admin-result-capacity (at-zero-plan))))
      (equal (fn-acct-offline-invite-refusal (at-zero-plan) *at-wall-stamp*)
             :no-clock)))
; Observation: a stamp claiming a wall whose reading is not a natural.
(assert-event
 (let ((bad (fn-clock-observation 3 -5 0 t)))
   (and (not (fn-clock-observationp bad))
        (fn-clock-has-wall bad)
        (equal (fn-acct-offline-invite-refusal (at-inv-plan) bad) :no-clock))))

; -----------------------------------------------------------------------------
; PRF-378: expiry at admission and replay, in milliseconds.  The reached
; path: the stopped node's invite at *at-now-ms* (one hour), its record
; replayed, then a redeem record the owner stamps a minute later (live) and
; one an hour and a second later (expired).

(defmacro at-inv-deltas ()
  '(fn-acct-admin-deltas (at-inv-plan) (fn-acct-offline-invite-reading
                                        *at-wall-stamp*)))
(defmacro at-cfg1m ()
  '(fn-config-replay-loop (fn-cfg-initial) 0 1000
                          (list (fn-cfg-record-make 1 1 1 (at-inv-deltas)
                                                    *at-wall-stamp*))))
(defconst *at-soon* (fn-clock-observation 9 (+ *at-now-ms* 60000) 250 t))
(defconst *at-past* (fn-clock-observation 9 (+ *at-now-ms* 3600000) 0 t))
(defmacro at-redeem-plan-m ()
  '(fn-acct-redeem-plan (fn-cfg-value (at-cfg1m)) *at-soon* *at-code*
                        *at-login* *at-password* *at-salt* nil))
(defmacro at-redeem-at (stamp)
  `(fn-cfg-record-make 2 2 2 (list (fn-acct-plan-delta (at-redeem-plan-m)))
                       ,stamp))
(defmacro at-row-m ()
  '(fn-cfg-account-row (fn-cfg-accounts (fn-cfg-value (at-cfg1m))) (at-digest)))
(defmacro at-keystone-hyps (cfg r)
  `(let* ((d (car (fn-cfg-record-change ,r)))
          (stamp (fn-cfg-record-stamp ,r))
          (row (fn-cfg-account-row (fn-cfg-accounts (fn-cfg-value ,cfg))
                                   (fn-cfg-delta-a d))))
     (list (fn-cfg-deltap d)
           (equal (fn-cfg-delta-kind d) :account-redeem)
           (fn-cfg-account-digestp (fn-cfg-delta-a d))
           (fn-cfg-account-loginp (fn-cfg-delta-b d))
           (fn-cfg-account-delta-rowp d 1)
           (consp row)
           (equal (fn-cfg-row-n row) 0)
           (or (not (fn-clock-has-wall stamp))
               (<= (fn-cfg-account-expiry (fn-cfg-row-c row))
                   (+ (fn-clock-wall stamp) (fn-clock-wall-error stamp)))))))
(defmacro at-keystone-concl (cfg r)
  `(list (equal (fn-cfg-admissible-reason
                 (fn-cfg-value ,cfg) (fn-cfg-record-generation ,r)
                 (fn-cfg-record-stamp ,r) 0 1000 (fn-cfg-record-change ,r))
                :account-expired)
         (not (fn-cfg-record-acceptablep ,cfg ,r 0 1000))
         (equal (fn-config-replay-loop ,cfg 0 1000 (list ,r)) :fault)))

; The invitation's expiry is the stamp's milliseconds plus one hour.
(assert-event (not (equal (at-cfg1m) :fault)))
(assert-event (equal (fn-cfg-account-expiry (fn-cfg-row-c (at-row-m)))
                     (+ *at-now-ms* 3600000)))
(assert-event (equal (car (at-redeem-plan-m)) :redeem))
; KEYSTONE fn-cfg-record-redeeming-an-expired-code-is-refused-and-faults-replay:
; the reached positive witness (every hypothesis, every conclusion).
(assert-event (equal (at-keystone-hyps (at-cfg1m) (at-redeem-at *at-past*))
                     '(t t t t t t t t)))
(assert-event (equal (at-keystone-concl (at-cfg1m) (at-redeem-at *at-past*))
                     '(t t t)))
; Removal of the time hypothesis: the same redeem a minute after issue is
; admitted and replays (every other hypothesis holds).
(assert-event (equal (at-keystone-hyps (at-cfg1m) (at-redeem-at *at-soon*))
                     '(t t t t t t t nil)))
(assert-event (equal (at-keystone-concl (at-cfg1m) (at-redeem-at *at-soon*))
                     '(nil nil nil)))
; Mutation witness (labelled): read as the pre-PRF-378 seconds stamp (the
; same instant floored to seconds), the expired redeem is admitted -- the
; vacuous check this lane removed.
(assert-event
 (equal (at-keystone-concl
         (at-cfg1m)
         (at-redeem-at (fn-clock-observation 9 (floor (+ *at-now-ms* 3600000) 1000)
                                             0 t)))
        '(nil nil nil)))
; Without a wall claim the redeem is refused (the disjunct's other arm).
(assert-event (equal (at-keystone-hyps (at-cfg1m) (at-redeem-at *at-blind-stamp*))
                     '(t t t t t t t t)))
(assert-event (equal (at-keystone-concl (at-cfg1m) (at-redeem-at *at-blind-stamp*))
                     '(t t t)))
; Removal of the pending hypothesis: over the redeemed configuration the
; identical redeem, stamped with no wall claim (the time hypothesis's other
; arm, since a redeemed row holds a verifier, not an expiry), is the resume
; and is admitted.
(defmacro at-resume-late ()
  '(fn-cfg-record-make 3 3 3 (list (fn-acct-plan-delta (at-plan1)))
                       *at-blind-stamp*))
(assert-event (equal (at-keystone-hyps (at-cfg2) (at-resume-late))
                     '(t t t t t t nil t)))
(assert-event (equal (at-keystone-concl (at-cfg2) (at-resume-late))
                     '(nil nil nil)))
; Removal of the row hypothesis: a redeem of a digest no row holds is
; refused as unknown, not expired.
(defmacro at-unknown-late ()
  '(fn-cfg-record-make 2 2 2
                       (list (fn-cfg-account-redeem
                              (at-digest-2) "robin"
                              (fn-acct-verifier-text
                               (fn-authsec-enrol *at-salt* *at-password*))))
                       *at-past*))
(assert-event (equal (at-keystone-hyps (at-cfg1m) (at-unknown-late))
                     '(t t t t t nil nil t)))
(assert-event (equal (fn-cfg-admissible-reason
                      (fn-cfg-value (at-cfg1m)) 2 *at-past* 0 1000
                      (fn-cfg-record-change (at-unknown-late)))
                     :account-unknown))
; Removal of the login hypothesis: an empty login is refused as a login.
(defmacro at-nologin-late ()
  '(fn-cfg-record-make 2 2 2
                       (list (fn-cfg-account-redeem
                              (at-digest) ""
                              (fn-acct-verifier-text
                               (fn-authsec-enrol *at-salt* *at-password*))))
                       *at-past*))
(assert-event (equal (at-keystone-hyps (at-cfg1m) (at-nologin-late))
                     '(t t t nil t t t t)))
(assert-event (equal (fn-cfg-admissible-reason
                      (fn-cfg-value (at-cfg1m)) 2 *at-past* 0 1000
                      (fn-cfg-record-change (at-nologin-late)))
                     :account-login))
; Removal of the kind hypothesis: the invite record itself, replayed late,
; is not refused as expired.
(defmacro at-reinvite-late ()
  '(fn-cfg-record-make 2 2 2 (at-inv-deltas) *at-past*))
(assert-event (not (equal (fn-cfg-admissible-reason
                           (fn-cfg-value (at-cfg1m)) 2 *at-past* 0 1000
                           (fn-cfg-record-change (at-reinvite-late)))
                          :account-expired)))
; Removal of the row-shape hypothesis: a redeem whose row carries the
; pending mark is refused as a row, not expired.
(defmacro at-badrow-late ()
  '(fn-cfg-record-make 2 2 2
                       (list (fn-cfg-delta-make
                              :account-redeem (at-digest) "robin" 0
                              (list (fn-cfg-row-make
                                     (at-digest) "robin"
                                     (fn-acct-verifier-text
                                      (fn-authsec-enrol *at-salt* *at-password*))
                                     0))))
                       *at-past*))
(assert-event (equal (at-keystone-hyps (at-cfg1m) (at-badrow-late))
                     '(t t t t nil t t t)))
(assert-event (equal (fn-cfg-admissible-reason
                      (fn-cfg-value (at-cfg1m)) 2 *at-past* 0 1000
                      (fn-cfg-record-change (at-badrow-late)))
                     :account-row))
; Removal of the digest hypothesis (CONSTRUCTED configuration, not
; reachable: a pending row keyed by a non-digest, applied without its
; admission): refused as a digest, not expired.
(defmacro at-cfg-zz ()
  '(fn-cfg-make 1 (fn-cfg-apply-delta (at-v0) 1 *at-wall-stamp*
                                      (fn-cfg-account-invite "zz" "operator"
                                                             "2000000000"))))
(defmacro at-zz-late ()
  '(fn-cfg-record-make 2 2 2
                       (list (fn-cfg-account-redeem
                              "zz" "robin"
                              (fn-acct-verifier-text
                               (fn-authsec-enrol *at-salt* *at-password*))))
                       *at-past*))
(assert-event (equal (at-keystone-hyps (at-cfg-zz) (at-zz-late))
                     '(t t nil t t t t t)))
(assert-event (equal (fn-cfg-admissible-reason
                      (fn-cfg-value (at-cfg-zz)) 2 *at-past* 0 1000
                      (fn-cfg-record-change (at-zz-late)))
                     :account-digest))
