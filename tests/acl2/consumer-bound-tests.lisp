; Teeth for books/consumer-bound.lisp (PRF-234, CNS-006): a local consumer
; bound to an account.  Every answer below is a host-called decision
; (host/owner-host.lisp fn-owner-consumer-local-bound-poll / -bound-ack call
; fn-cbind-poll / fn-cbind-ack; fn-owner-consumer-local-poll / -ack call
; fn-cbind-plain-poll / fn-cbind-plain-ack) over a committed Store with two
; groups, fn.public and fn.private.x, one article in each, and four
; consumers:
;
;   "1"  query fn.private.x  bound to bob    (bob reads fn.*,!fn.private.*)
;   "2"  query fn.public     bound to bob
;   "3"  query fn.private.x  unbound         (the operator's)
;   "4"  query fn.private.x  bound to alice  (alice has no rule)
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/consumer-bound")

; --- the Store -------------------------------------------------------------
(defun cbt-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))
(defun cbt-commit (s event)
  (fn-sn-finish
   (fn-sn-io
    (fn-sn-io
     (fn-sn-io (fn-sn-prepare-consumer (cbt-reserve s) event)
               :record-file :ok)
     :record-link :ok)
    :record-directory :ok)))
(defun cbt-article (s record)
  (fn-sn-finish
   (fn-sn-io
    (fn-sn-io
     (fn-sn-io (fn-sn-prepare (cbt-reserve s) record) :record-file :ok)
     :record-link :ok)
    :record-directory :ok)))
(defun cbt-register (s id group)
  (let ((d (fn-col-register (fn-own-start s 2) 256 id group)))
    (if (eq (car d) :write) (cbt-commit s (cadr d)) s)))

(defconst *cbt-public* '(102 110 46 112 117 98 108 105 99))           ; fn.public
(defconst *cbt-private* '(102 110 46 112 114 105 118 97 116 101 46 120)) ; fn.private.x
(defconst *cbt-c1* '(49))
(defconst *cbt-c2* '(50))
(defconst *cbt-c3* '(51))
(defconst *cbt-c4* '(52))

(defconst *cbt-boot*
  (cbt-commit (fn-sn-initial '("fn.public" "fn.private.x") 16)
              (fn-cpe-make 0 0 0 '(:bootstrap (1) (2)))))
(defconst *cbt-registered*
  (cbt-register
   (cbt-register
    (cbt-register (cbt-register *cbt-boot* *cbt-c1* *cbt-private*)
                  *cbt-c2* *cbt-public*)
    *cbt-c3* *cbt-private*)
   *cbt-c4* *cbt-private*))
(defconst *cbt-secret-record*
  (fn-record-make 5 5 5 "<secret@fn.test>" '(83)
                  '("fn.private.x") "secret-pin" "secret-content"
                  "secret-release" 1 841000000))
(defconst *cbt-public-record*
  (fn-record-make 6 6 6 "<public@fn.test>" '(80)
                  '("fn.public") "public-pin" "public-content"
                  "public-release" 1 841000001))
(defconst *cbt-store*
  (cbt-article (cbt-article *cbt-registered* *cbt-secret-record*)
               *cbt-public-record*))
(defconst *cbt-o* (fn-own-start *cbt-store* 2))
; Every registration and both articles committed: frontier 7.
(assert-event (equal (fn-cp-nth 3 (fn-sn-consumer *cbt-store*)) 7))

; --- the configuration: bob's rule and three bindings ------------------------
(defconst *cbt-deltas*
  (list (fn-cfg-account-access "bob" "fn.*,!fn.private.*" "fn.*")
        (fn-cfg-consumer-bind "1" "bob")
        (fn-cfg-consumer-bind "2" "bob")
        (fn-cfg-consumer-bind "4" "alice")))
(assert-event (equal (fn-cfg-kind-code :consumer-bind) 24))
(assert-event (equal (fn-cfg-code-kind 24) :consumer-bind))
(assert-event (fn-cfg-delta-listp *cbt-deltas*))
(assert-event (null (fn-cfg-consumer-bind-reason (fn-cfg-consumer-bind "1" "bob"))))
(assert-event (null (fn-cfg-consumer-bind-reason (fn-cfg-consumer-bind "1" ""))))
(assert-event (equal (fn-cfg-consumer-bind-reason (fn-cfg-consumer-bind "" "bob"))
                     :consumer-name))
(assert-event (equal (fn-cfg-consumer-bind-reason (fn-cfg-consumer-bind "1" "a b"))
                     :consumer-login))
;; The configuration values below are spelled by their accounts rows
;; (`cbt-with-accounts') and each is asserted equal to the value the
;; configuration's own fold (`fn-cfg-apply-delta') produces from the deltas.
(defun cbt-with-accounts (rows)
  (let ((v (fn-cfg-value (fn-cfg-initial))))
    (fn-cfg-value-make-full (fn-cfg-groups v) (fn-cfg-capacity v)
                            (fn-cfg-quotas v) (fn-cfg-policies v)
                            (fn-cfg-listeners v) (fn-cfg-peers v)
                            (fn-cfg-limits v) (fn-cfg-authorities v)
                            (fn-cfg-invitations v) rows
                            (fn-cfg-descriptions v))))
(defun cbt-apply (v gen ds)
  (if (consp ds)
      (cbt-apply (fn-cfg-apply-delta v gen 0 (car ds)) (1+ gen) (cdr ds))
    v))
(defconst *cbt-rows*
  (list (fn-cfg-row-make "bob" "fn.*,!fn.private.*" "fn.*" 3)
        (fn-cfg-row-make "1" "bob" "" 6)
        (fn-cfg-row-make "2" "bob" "" 6)
        (fn-cfg-row-make "4" "alice" "" 6)))
(defconst *cbt-v* (cbt-with-accounts *cbt-rows*))
(assert-event
 (equal (cbt-apply (fn-cfg-value (fn-cfg-initial)) 1 *cbt-deltas*) *cbt-v*))
; A rebind replaces the row; the unbind removes it.
(assert-event
 (equal (fn-cfg-accounts
         (fn-cfg-apply-delta *cbt-v* 9 0 (fn-cfg-consumer-bind "1" "alice")))
        (list (fn-cfg-row-make "bob" "fn.*,!fn.private.*" "fn.*" 3)
              (fn-cfg-row-make "2" "bob" "" 6)
              (fn-cfg-row-make "4" "alice" "" 6)
              (fn-cfg-row-make "1" "alice" "" 6))))
(assert-event
 (equal (fn-cfg-accounts
         (fn-cfg-apply-delta *cbt-v* 9 0 (fn-cfg-consumer-bind "1" "")))
        (list (fn-cfg-row-make "bob" "fn.*,!fn.private.*" "fn.*" 3)
              (fn-cfg-row-make "2" "bob" "" 6)
              (fn-cfg-row-make "4" "alice" "" 6))))

(defconst *cbt-oc* (fn-ocfg-make *cbt-o* (fn-cfg-make 4 *cbt-v*) nil nil))
; The operator's view: no binding row, no rule.
(defconst *cbt-oc-none*
  (fn-ocfg-make *cbt-o* (fn-cfg-make 0 (fn-cfg-value (fn-cfg-initial))) nil nil))

; --- credentials (books/nntp-auth-teeth-tests' verifier literal) -------------
(defconst *cbt-secret* (fn-nntp-string-octets "correct-horse"))
(defconst *cbt-wrong* (fn-nntp-string-octets "wrong-horse"))
(defconst *cbt-salt* (make-list 16 :initial-element 3))
(defconst *cbt-verifier*
  (fn-authsec-verifier
   *cbt-salt*
   '(60 237 250 71 154 204 168 180 72 224 241 93 232 185 72 59
     73 5 240 237 54 116 175 93 127 219 39 238 113 83 63 194)))
(assert-event (equal *cbt-verifier* (fn-authsec-enrol *cbt-salt* *cbt-secret*)))
(defconst *cbt-acfg*
  (fn-auth-make-config
   t nil t
   (list (fn-auth-make-cred (fn-nntp-string-octets "alice")
                            (make-list 32 :initial-element 7) *cbt-verifier* t)
         (fn-auth-make-cred (fn-nntp-string-octets "bob")
                            (make-list 32 :initial-element 8) *cbt-verifier* t))))
(assert-event (fn-auth-configp *cbt-acfg*))

; --- what each consumer is served -------------------------------------------
(defun cbt-poll (oc id secret) (fn-cbind-poll oc *cbt-acfg* id secret))
(defun cbt-msgid (poll)
  (fn-record-msgid (fn-col-poll-article (caddr poll))))

; The operator's consumer poll selects the private article for "1".
(defconst *cbt-d1* (fn-col-poll *cbt-o* *cbt-c1*))
(assert-event (equal (car *cbt-d1*) :poll))
(assert-event (equal (cbt-msgid *cbt-d1*) "<secret@fn.test>"))

; "2" (bob, fn.public): served its article, exactly the consumer poll.
(defun cbt-r2 () (cbt-poll *cbt-oc* *cbt-c2* *cbt-secret*))
(defconst *cbt-d2* (fn-col-poll *cbt-o* *cbt-c2*))
(assert-event (equal (car (cbt-r2)) :poll))
(assert-event (equal (cbt-r2) (fn-col-poll-report *cbt-o* *cbt-c2*)))
(assert-event (equal (cbt-msgid *cbt-d2*) "<public@fn.test>"))
(assert-event (equal (caddr (cbt-r2)) (fn-col-poll-report-octets (caddr *cbt-d2*))))
; "1" (bob, fn.private.x): refused :access, whatever the store holds.
(assert-event (equal (cbt-poll *cbt-oc* *cbt-c1* *cbt-secret*) '(:refused :access)))
; "4" (alice, fn.private.x): served the private article.
(defun cbt-r4 () (cbt-poll *cbt-oc* *cbt-c4* *cbt-secret*))
(assert-event (equal (cbt-r4) (fn-col-poll-report *cbt-o* *cbt-c4*)))
(assert-event (equal (cbt-msgid (fn-col-poll *cbt-o* *cbt-c4*)) "<secret@fn.test>"))
; A wrong password, an unbound consumer, an unregistered bound consumer.
(assert-event (equal (cbt-poll *cbt-oc* *cbt-c2* *cbt-wrong*) '(:refused :credential)))
(assert-event (equal (cbt-poll *cbt-oc* *cbt-c3* *cbt-secret*) '(:refused :unbound)))
(defconst *cbt-v-nine*
  (cbt-with-accounts (append *cbt-rows* (list (fn-cfg-row-make "9" "bob" "" 6)))))
(assert-event (equal (fn-cfg-apply-delta *cbt-v* 5 0 (fn-cfg-consumer-bind "9" "bob"))
                     *cbt-v-nine*))
(assert-event
 (equal (cbt-poll (fn-ocfg-make *cbt-o* (fn-cfg-make 5 *cbt-v-nine*) nil nil)
                  '(57) *cbt-secret*)
        '(:refused :unknown-consumer)))
; A redeemed account's credential (the second producer) authenticates too:
; the row fn-auth-account-creds reads, with the same verifier.
(defconst *cbt-digest* (coerce (make-list 64 :initial-element #\a) (quote string)))
(defconst *cbt-v-carol*
  (cbt-with-accounts
   (list (fn-cfg-row-make "bob" "fn.*,!fn.private.*" "fn.*" 3)
         (fn-cfg-row-make "1" "bob" "" 6)
         (fn-cfg-row-make "4" "alice" "" 6)
         (fn-cfg-row-make "2" "carol" "" 6)
         (fn-cfg-row-make *cbt-digest* "carol"
                          (fn-acct-verifier-text *cbt-verifier*) 1))))
(assert-event
 (equal (fn-cfg-apply-delta
         (fn-cfg-apply-delta *cbt-v* 5 0 (fn-cfg-consumer-bind "2" "carol"))
         6 0
         (fn-cfg-account-redeem *cbt-digest* "carol"
                                (fn-acct-verifier-text *cbt-verifier*)))
        *cbt-v-carol*))
(defconst *cbt-oc-carol* (fn-ocfg-make *cbt-o* (fn-cfg-make 6 *cbt-v-carol*) nil nil))
(assert-event (equal (fn-cbind-poll *cbt-oc-carol* (fn-auth-open-config) *cbt-c2* *cbt-secret*)
                     (cbt-r2)))

; The plain forms.  Unbound "3": today's answer (the private article: the
; operator reads everything).  Bound "2": refused :bound.
(assert-event (equal (fn-cbind-plain-poll *cbt-oc* *cbt-c3*)
                     (fn-col-poll-report *cbt-o* *cbt-c3*)))
(assert-event (equal (cbt-msgid (fn-col-poll *cbt-o* *cbt-c3*)) "<secret@fn.test>"))
(assert-event (equal (fn-cbind-plain-poll *cbt-oc* *cbt-c2*) '(:refused :bound)))
; With no binding in the configuration, every plain answer is today's.
(assert-event (equal (fn-cbind-plain-poll *cbt-oc-none* *cbt-c2*)
                     (fn-col-poll-report *cbt-o* *cbt-c2*)))

; --- acks --------------------------------------------------------------------
(defun cbt-cursor2 () (cadr (cbt-r2)))
(defun cbt-a2 () (fn-cbind-ack *cbt-oc* *cbt-acfg* (cbt-cursor2) *cbt-secret*))
(assert-event (equal (car (cbt-a2)) :write))
(assert-event (equal (cbt-a2) (fn-col-ack *cbt-o* (cbt-cursor2))))
(assert-event (equal (fn-cbind-ack *cbt-oc* *cbt-acfg* (cbt-cursor2) *cbt-wrong*)
                     '(:refused :credential)))
(assert-event (equal (fn-cbind-plain-ack *cbt-oc* (cbt-cursor2)) '(:refused :bound)))
(assert-event (equal (fn-cbind-plain-ack *cbt-oc-none* (cbt-cursor2))
                     (fn-col-ack *cbt-o* (cbt-cursor2))))
; "1"'s own scope cursor (what an earlier poll under an older rule handed
; it): refused :access now.
(defconst *cbt-cursor1* (cadr *cbt-d1*))
(assert-event (equal (fn-cbind-ack *cbt-oc* *cbt-acfg* *cbt-cursor1* *cbt-secret*)
                     '(:refused :access)))

; --- a rule change: the refusal kept the position ----------------------------
; bob's rule widened to "*": "1" is served from where it stopped, the first
; private article (nothing was skipped while it was refused).
(defconst *cbt-v-wide*
  (cbt-with-accounts
   (list (fn-cfg-row-make "1" "bob" "" 6)
         (fn-cfg-row-make "2" "bob" "" 6)
         (fn-cfg-row-make "4" "alice" "" 6)
         (fn-cfg-row-make "bob" "*" "*" 3))))
(assert-event
 (equal (fn-cfg-apply-delta *cbt-v* 5 0 (fn-cfg-account-access "bob" "*" "*"))
        *cbt-v-wide*))
(defconst *cbt-oc-wide* (fn-ocfg-make *cbt-o* (fn-cfg-make 5 *cbt-v-wide*) nil nil))
(assert-event (equal (cbt-poll *cbt-oc-wide* *cbt-c1* *cbt-secret*)
                     (fn-col-poll-report *cbt-o* *cbt-c1*)))
(assert-event (equal (car (cbt-poll *cbt-oc-wide* *cbt-c1* *cbt-secret*)) :poll))

; --- KEYSTONE 1 teeth --------------------------------------------------------
; The literal conclusion of fn-cbind-poll-delivers-only-readable-events.
(defun cbt-k1 (oc acfg consumer secret)
  (let ((r (fn-cbind-poll oc acfg consumer secret))
        (d (fn-col-poll (fn-ocfg-owner oc) consumer))
        (login (fn-cbind-config-login oc consumer)))
    (and login
         (fn-cbind-authenticp oc acfg login secret)
         (equal r (fn-col-poll-report (fn-ocfg-owner oc) consumer))
         (equal (car d) :poll)
         (implies (caddr d)
                  (fn-cbind-event-readablep
                   (fn-cbind-read-pattern oc login) (caddr d)))
         t)))
; Reachable positive witness: the hypothesis holds, a nonempty page, and
; the complete conclusion.
(assert-event (equal (car (cbt-poll *cbt-oc* *cbt-c2* *cbt-secret*)) :poll))
(assert-event (caddr (fn-col-poll *cbt-o* *cbt-c2*)))
(assert-event (cbt-k1 *cbt-oc* *cbt-acfg* *cbt-c2* *cbt-secret*))
; Without the hypothesis (a page): "1" under bob is refused, and the
; conclusion fails -- its selected event is not readable under bob's rule.
(assert-event (not (equal (car (cbt-poll *cbt-oc* *cbt-c1* *cbt-secret*)) :poll)))
(assert-event (not (fn-cbind-event-readablep
                    (fn-cbind-read-pattern *cbt-oc* "bob") (caddr *cbt-d1*))))
(must-fail (assert-event (cbt-k1 *cbt-oc* *cbt-acfg* *cbt-c1* *cbt-secret*)))
; ... and a wrong password: the credential conjunct fails.
(must-fail (assert-event (cbt-k1 *cbt-oc* *cbt-acfg* *cbt-c2* *cbt-wrong*)))

; --- KEYSTONE 2 and 3 witnesses (no hypotheses) ------------------------------
; Each disjunct is reached: the consumer's own answer, and a refusal.
(assert-event (equal (cbt-poll *cbt-oc* *cbt-c2* *cbt-secret*)
                     (fn-col-poll-report *cbt-o* *cbt-c2*)))
(assert-event (not (equal (cbt-poll *cbt-oc* *cbt-c1* *cbt-secret*)
                          (fn-col-poll-report *cbt-o* *cbt-c1*))))
(assert-event (equal (car (cbt-poll *cbt-oc* *cbt-c1* *cbt-secret*)) :refused))
(assert-event (not (equal (fn-cbind-ack *cbt-oc* *cbt-acfg* *cbt-cursor1* *cbt-secret*)
                          (fn-col-ack *cbt-o* *cbt-cursor1*))))
; KEYSTONE 3's second conjunct: without "not refused", "1"'s ack has its
; binding and credential but not a readable query.
(assert-event (fn-cbind-config-login *cbt-oc* *cbt-c1*))
(assert-event (fn-cbind-authenticp *cbt-oc* *cbt-acfg* "bob" *cbt-secret*))
(assert-event (not (fn-cbind-group-readablep (fn-cbind-read-pattern *cbt-oc* "bob")
                                             "fn.private.x")))

; --- KEYSTONE 4 teeth ----------------------------------------------------------
; Positive: unbound "3" is today's poll; bound "2" is refused.
(assert-event (not (fn-cbind-config-login *cbt-oc* *cbt-c3*)))
(assert-event (fn-cbind-config-login *cbt-oc* *cbt-c2*))
; Without "unbound": bound "2"'s plain poll is not the consumer poll.
(must-fail (assert-event (equal (fn-cbind-plain-poll *cbt-oc* *cbt-c2*)
                                (fn-col-poll-report *cbt-o* *cbt-c2*))))
; Without "bound": unbound "3"'s plain poll is not refused :bound.
(must-fail (assert-event (equal (fn-cbind-plain-poll *cbt-oc* *cbt-c3*)
                                '(:refused :bound))))
; The plain ack's "decodable" hypothesis, CORRUPTED state: a binding row
; named "" (admission refuses it, :consumer-name) binds the consumer an
; undecodable cursor names (nil), and the plain ack of those bytes is
; fn-col-ack's refusal, not :bound.
(defconst *cbt-oc-corrupt*
  (fn-ocfg-make *cbt-o*
                (fn-cfg-make 1 (fn-cfg-value-make-full
                                nil nil nil nil nil nil nil nil nil
                                (list (fn-cfg-row-make "" "bob" "" 6)) nil))
                nil nil))
(assert-event (not (equal (fn-cp-nth 0 (fn-cp-cursor-decode '(1 2 3))) :ok)))
(assert-event (fn-cbind-config-login *cbt-oc-corrupt*
                                     (fn-cp-nth 3 (fn-cp-nth 1 (fn-cp-cursor-decode '(1 2 3))))))
(must-fail (assert-event (equal (fn-cbind-plain-ack *cbt-oc-corrupt* '(1 2 3))
                                '(:refused :bound))))

