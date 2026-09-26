; Teeth for fn-own-stored-octets-carry-the-login-lock
; (books/owner-served-invariants.lisp; SEC-006, PRF-210): the octets the
; owner stages for a served submission under a login carry exactly one
; Cancel-Lock, the login's, which the login's key opens and another
; login's does not.  A witness asserting the whole antecedent and the
; conclusion, then per hypothesis one removal at which the other
; hypotheses hold and the conclusion fails.  The stored octets are parsed
; by the served path's article parser, so the witness also checks the step
; no theorem covers (the written line parses back as the one lock entry).
; Reachability through a served read (fn-own-finish-read recording the
; login) is the native case tests/test_native_own_cancel.py.
(in-package "ACL2")
(include-book "../../books/owner-served-invariants")
(include-book "std/testing/must-fail" :dir :system)

(defun oclt-octets (s) (fn-record-string-octets s))
(defun oclt-join (lines)
  (if (consp lines)
      (append (oclt-octets (car lines)) (list 13 10) (oclt-join (cdr lines)))
    nil))

(defconst *oclt-secret* (make-list 32 :initial-element 7))
(defconst *oclt-alice* (oclt-octets "alice"))
(defconst *oclt-bob* (oclt-octets "bob"))
(defconst *oclt-msgid* (oclt-octets "<t1@fn.test>"))
(defconst *oclt-injected*
  (oclt-join (list "Path: fn.test!not-for-mail" "Injection-Info: fn.test"
                   "From: alice <alice@example.invalid>"
                   "Newsgroups: local.general" "Subject: mine"
                   "Message-ID: <t1@fn.test>" "" "hello")))
(defun oclt-sub (octets login)
  (fn-own-sub-make-login 4 2 0 (fn-inj-make-decision :injected nil *oclt-msgid*
                                                     (list "local.general") octets)
                         login))
(defconst *oclt-sub* (oclt-sub *oclt-injected* *oclt-alice*))

(defun oclt-hyps (sub secret)
  (let* ((d (fn-own-sub-decision sub))
         (login (fn-own-sub-login sub))
         (x (fn-inj-decision-octets d)))
    (and (not (fn-peer-submissionp d))
         (fn-ns-secretp secret)
         (fn-cbor-octet-listp login) (consp login)
         (not (consp (fn-ctl-fields-named *fn-ctl-cancel-lock-name*
                                          (fn-ctl-received-fields x))))
         (fn-cll-info-end x 0 :start)
         t)))
(defun oclt-conclusion (cfg sub secret)
  (let* ((d (fn-own-sub-decision sub))
         (login (fn-own-sub-login sub))
         (x (fn-inj-decision-octets d))
         (k (fn-cll-info-end x 0 :start)))
    (equal (fn-own-sub-stored-octets cfg sub secret)
           (append (fn-cll-take k x)
                   (fn-cll-line *fn-cll-lock-head*
                                (fn-cl-lock secret (fn-inj-decision-msgid d) login))
                   (fn-cl-key-lines secret login (fn-ctl-received-fields x))
                   (fn-cll-drop k x)))))

; Witness.
(defconst *oclt-stored* (fn-own-sub-stored-octets nil *oclt-sub* *oclt-secret*))
(assert-event (oclt-hyps *oclt-sub* *oclt-secret*))
(assert-event (oclt-conclusion nil *oclt-sub* *oclt-secret*))
; Exactly one lock, alice's, parsed back from the stored octets; her key
; opens it, bob's does not; the article is otherwise the injected one.
(assert-event
 (equal (fn-ctl-locks-octets *oclt-stored*)
        (list (fn-cl-lock *oclt-secret* *oclt-msgid* *oclt-alice*))))
(assert-event
 (fn-ctl-some-key-opens-p (list (fn-cl-key *oclt-secret* *oclt-msgid* *oclt-alice*))
                          (fn-ctl-locks-octets *oclt-stored*)))
(assert-event
 (not (fn-ctl-some-key-opens-p (list (fn-cl-key *oclt-secret* *oclt-msgid* *oclt-bob*))
                               (fn-ctl-locks-octets *oclt-stored*))))
(assert-event (equal (len *oclt-stored*)
                     (+ (len *oclt-injected*) (len *fn-cll-lock-head*)
                        *fn-cll-value-length* 2)))

; Removal: a transit submission (the relayed arm; no lock).
(defconst *oclt-transit*
  (fn-own-sub-make-login 4 2 0 (fn-peer-make-submission "p" :ihave *oclt-msgid*
                                                        *oclt-injected*)
                         *oclt-alice*))
(assert-event (fn-peer-submissionp (fn-own-sub-decision *oclt-transit*)))
(assert-event (not (oclt-conclusion nil *oclt-transit* *oclt-secret*)))
(must-fail (assert-event (oclt-conclusion nil *oclt-transit* *oclt-secret*)))

; Removal: no node secret installed (nil, the owner before the host's
; install): the stored octets are the injected ones.
(assert-event (not (fn-ns-secretp nil)))
(assert-event (equal (fn-own-sub-stored-octets nil *oclt-sub* nil) *oclt-injected*))
(assert-event (not (oclt-conclusion nil *oclt-sub* nil)))
(must-fail (assert-event (oclt-conclusion nil *oclt-sub* nil)))

; Removal: no login (an unauthenticated POST; the four-element submission).
(defconst *oclt-anon* (oclt-sub *oclt-injected* nil))
(assert-event (equal *oclt-anon* (fn-own-sub-make 4 2 0 (fn-own-sub-decision *oclt-anon*))))
(assert-event (equal (fn-own-sub-stored-octets nil *oclt-anon* *oclt-secret*)
                     *oclt-injected*))
(assert-event (not (oclt-conclusion nil *oclt-anon* *oclt-secret*)))
(must-fail (assert-event (oclt-conclusion nil *oclt-anon* *oclt-secret*)))

; Removal: the poster wrote their own Cancel-Lock (tin): kept, none added.
(defconst *oclt-tin*
  (oclt-join (list "Path: fn.test!not-for-mail" "Injection-Info: fn.test"
                   "From: tin <tin@example.invalid>" "Newsgroups: local.general"
                   "Subject: mine" "Message-ID: <t1@fn.test>"
                   "Cancel-Lock: sha256:OWNLOCKOWNLOCKOWNLOCKOWNLOCKOWNLOCKOWNLOCK123="
                   "" "hello")))
(defconst *oclt-tin-sub* (oclt-sub *oclt-tin* *oclt-alice*))
(assert-event (equal (fn-own-sub-stored-octets nil *oclt-tin-sub* *oclt-secret*)
                     *oclt-tin*))
(assert-event (not (oclt-conclusion nil *oclt-tin-sub* *oclt-secret*)))
(must-fail (assert-event (oclt-conclusion nil *oclt-tin-sub* *oclt-secret*)))

; Removal: no Injection-Info line of the node (k is nil): nothing inserted.
(defconst *oclt-foreign*
  (oclt-join (list "Path: elsewhere!not-for-mail" "From: x <x@example.invalid>"
                   "Newsgroups: local.general" "Subject: mine"
                   "Message-ID: <t1@fn.test>" "" "hello")))
(defconst *oclt-foreign-sub* (oclt-sub *oclt-foreign* *oclt-alice*))
(assert-event (null (fn-cll-info-end *oclt-foreign* 0 :start)))
(assert-event (equal (fn-own-sub-stored-octets nil *oclt-foreign-sub* *oclt-secret*)
                     *oclt-foreign*))
(assert-event (not (oclt-conclusion nil *oclt-foreign-sub* *oclt-secret*)))
(must-fail (assert-event (oclt-conclusion nil *oclt-foreign-sub* *oclt-secret*)))

; The submission's login survives the writer's take (the mark set, the
; login kept), and a submission without one keeps its four-element shape.
(assert-event
 (equal (fn-own-sub-login (fn-own-sub-make-login 4 2 7 nil *oclt-alice*)) *oclt-alice*))
(assert-event (equal (len (fn-own-sub-make-login 4 2 7 nil nil)) 4))
