; Teeth for fn-own-stored-octets-carry-the-account-lock and
; fn-own-stored-octets-keep-the-injected-octets
; (books/owner-served-invariants.lisp; SEC-006, PRF-210): the octets the
; owner stages for a served submission by an account carry exactly one
; Cancel-Lock, the account's under the current key epoch, in front of the
; injected octets, which the account's key opens and another account's does
; not; and their D25 projection is the injected octets.  A witness
; asserting the whole antecedent and the conclusion, then per hypothesis one
; removal at which the other hypotheses hold and the conclusion fails.  The
; stored octets are parsed by the served path's article parser, so the
; witness also checks the step no theorem covers (the written line parses
; back as the one lock entry).  Reachability through a served read
; (fn-own-finish-read recording the author) is the native case
; tests/test_native_own_cancel.py.
(in-package "ACL2")
(include-book "../../books/owner-served-invariants")
(include-book "must-fail-checked")

(defun oclt-octets (s) (fn-record-string-octets s))
(defun oclt-join (lines)
  (if (consp lines)
      (append (oclt-octets (car lines)) (list 13 10) (oclt-join (cdr lines)))
    nil))

(defconst *oclt-e1* (fn-ns-create-entry (oclt-octets "fn.test")
                                        (make-list 32 :initial-element 7)))
(defconst *oclt-secret* (list *oclt-e1*))
(defconst *oclt-alice* (make-list 32 :initial-element 1))
(defconst *oclt-bob* (make-list 32 :initial-element 2))
(defconst *oclt-msgid* (oclt-octets "<t1@fn.test>"))
(defconst *oclt-injected*
  (oclt-join (list "Path: fn.test!not-for-mail" "Injection-Info: fn.test"
                   "From: alice <alice@example.invalid>"
                   "Newsgroups: local.general" "Subject: mine"
                   "Message-ID: <t1@fn.test>" "" "hello")))
(defun oclt-sub (octets account)
  (fn-own-sub-make-author 4 2 0 (fn-inj-make-decision :injected nil *oclt-msgid*
                                                      (list "local.general") octets)
                          (if account (oclt-octets "alice") nil) account))
(defconst *oclt-sub* (oclt-sub *oclt-injected* *oclt-alice*))

(defun oclt-hyps (sub secret)
  (let* ((d (fn-own-sub-decision sub))
         (x (fn-inj-decision-octets d)))
    (and (not (fn-peer-submissionp d))
         (fn-cl-lock-wanted-p secret (fn-own-sub-account sub) (fn-ctl-received-fields x))
         t)))
(defun oclt-conclusion (cfg sub secret)
  (let* ((d (fn-own-sub-decision sub))
         (account (fn-own-sub-account sub))
         (x (fn-ipp-injected-octets d secret (fn-own-sub-login sub) cfg))
         (fields (fn-ctl-received-fields x)))
    (equal (fn-own-sub-stored-octets cfg sub secret)
           (append (fn-cll-line *fn-cll-lock-head*
                                (fn-cl-lock (fn-ns-current secret) account
                                            (fn-inj-decision-msgid d)))
                   (if (consp (fn-cl-key-values secret account fields))
                       (fn-cll-key-line (fn-cl-key-values secret account fields))
                     nil)
                   x))))

; Witness.
(defconst *oclt-stored* (fn-own-sub-stored-octets nil *oclt-sub* *oclt-secret*))
; PKT-597: under the login the injected octets carry the posting-account
; parameter in their one Injection-Info line (books/injection-info-params.lisp);
; the lock goes in front of those.
(defconst *oclt-with-params*
  (fn-ipp-injected-octets (fn-own-sub-decision *oclt-sub*) *oclt-secret*
                          (fn-own-sub-login *oclt-sub*) nil))
(assert-event
 (equal (len *oclt-with-params*)
        (+ (len *oclt-injected*) (len *fn-ipp-account-open*) 64 1)))
(assert-event (oclt-hyps *oclt-sub* *oclt-secret*))
(assert-event (oclt-conclusion nil *oclt-sub* *oclt-secret*))
; Exactly one lock, alice's, parsed back from the stored octets; her key
; opens it, bob's does not; the article is otherwise the injected one.
(assert-event
 (equal (fn-ctl-locks-octets *oclt-stored*)
        (list (fn-cl-lock *oclt-e1* *oclt-alice* *oclt-msgid*))))
(assert-event
 (fn-ctl-some-key-opens-p (list (fn-cl-key *oclt-e1* *oclt-alice* *oclt-msgid*))
                          (fn-ctl-locks-octets *oclt-stored*)))
(assert-event
 (not (fn-ctl-some-key-opens-p (list (fn-cl-key *oclt-e1* *oclt-bob* *oclt-msgid*))
                               (fn-ctl-locks-octets *oclt-stored*))))
(assert-event (equal (len *oclt-stored*)
                     (+ (len *oclt-with-params*) (len *fn-cll-lock-head*)
                        *fn-cll-value-length* 2)))
; fn-own-stored-octets-keep-the-injected-octets: the projection is the
; injected octets (witness: a local submission whose octets open with "P").
(assert-event
 (and (not (fn-peer-submissionp (fn-own-sub-decision *oclt-sub*)))
      (not (equal (car *oclt-with-params*) 67))
      (equal (fn-cll-skip *oclt-stored*) *oclt-with-params*)))

; Removal: a transit submission (the relayed arm; no lock).
(defconst *oclt-transit*
  (fn-own-sub-make-author 4 2 0 (fn-peer-make-submission "p" :ihave *oclt-msgid*
                                                         *oclt-injected*)
                          (oclt-octets "alice") *oclt-alice*))
(assert-event (fn-peer-submissionp (fn-own-sub-decision *oclt-transit*)))
(assert-event (not (oclt-conclusion nil *oclt-transit* *oclt-secret*)))
(must-fail-checked (assert-event (oclt-conclusion nil *oclt-transit* *oclt-secret*)))

; Removal: no key ring installed (nil, the owner before the host's
; install): the stored octets are the injected ones.
(assert-event (not (fn-ns-ringp nil)))
(assert-event (equal (fn-own-sub-stored-octets nil *oclt-sub* nil) *oclt-injected*))
(assert-event (not (oclt-conclusion nil *oclt-sub* nil)))
(must-fail-checked (assert-event (oclt-conclusion nil *oclt-sub* nil)))

; Removal: no author (an unauthenticated POST; the four-element submission).
(defconst *oclt-anon* (oclt-sub *oclt-injected* nil))
(assert-event (equal *oclt-anon* (fn-own-sub-make 4 2 0 (fn-own-sub-decision *oclt-anon*))))
(assert-event (equal (fn-own-sub-stored-octets nil *oclt-anon* *oclt-secret*)
                     *oclt-injected*))
(assert-event (not (oclt-conclusion nil *oclt-anon* *oclt-secret*)))
(must-fail-checked (assert-event (oclt-conclusion nil *oclt-anon* *oclt-secret*)))

; Removal: the poster wrote their own Cancel-Lock (tin): kept, none added.
(defconst *oclt-tin*
  (oclt-join (list "Path: fn.test!not-for-mail" "Injection-Info: fn.test"
                   "From: tin <tin@example.invalid>" "Newsgroups: local.general"
                   "Subject: mine" "Message-ID: <t1@fn.test>"
                   "Cancel-Lock: sha256:OWNLOCKOWNLOCKOWNLOCKOWNLOCKOWNLOCKOWNLOCK123="
                   "" "hello")))
(defconst *oclt-tin-sub* (oclt-sub *oclt-tin* *oclt-alice*))
; (no lock is added; the Injection-Info line carries the login's
; posting-account parameter, PKT-597)
(assert-event (equal (fn-own-sub-stored-octets nil *oclt-tin-sub* *oclt-secret*)
                     (fn-ipp-injected-octets (fn-own-sub-decision *oclt-tin-sub*)
                                             *oclt-secret*
                                             (fn-own-sub-login *oclt-tin-sub*) nil)))
(assert-event (not (oclt-conclusion nil *oclt-tin-sub* *oclt-secret*)))
(must-fail-checked (assert-event (oclt-conclusion nil *oclt-tin-sub* *oclt-secret*)))

; The submission's author survives the writer's take (the mark set, the
; login and account kept), and a submission without one keeps its
; four-element shape.
(assert-event
 (let ((sub (fn-own-sub-make-author 4 2 7 nil (oclt-octets "alice") *oclt-alice*)))
   (and (equal (fn-own-sub-login sub) (oclt-octets "alice"))
        (equal (fn-own-sub-account sub) *oclt-alice*)
        (fn-own-sub-shapep sub))))
(assert-event (equal (len (fn-own-sub-make-author 4 2 7 nil nil *oclt-alice*)) 4))
