; Witnesses and teeth for books/public-exposure.lisp (PRF-161).
;
; Each keystone gets a reachable witness that makes its whole antecedent and
; its conclusion true, and, per hypothesis, a ground instance that keeps
; every other hypothesis true, makes that one false, and falsifies the
; conclusion.  The anonymous keystone reuses the RFC 4643 fixtures of
; tests/acl2/nntp-auth-teeth-tests.lisp: *aut-s-req* is exactly the session
; fn-exp-open pins for the operator configuration *aut-required* under the
; :none policy.
(in-package "ACL2")
(include-book "../../books/public-exposure")
(include-book "nntp-auth-teeth-tests")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; Fixtures

; The limits: total 3, 2 per address, 2 steps a second, idle 600 s, first
; command 60 s, 2 failed logins a minute, 1 post a minute; anonymous :none.
(defconst *pxt-lim* (fn-exp-lim-make 3 2 2 600 60 2 1 :none))
(defconst *pxt-lim-open* (fn-exp-lim-make 3 2 2 600 60 2 1 :open))
(defconst *pxt-lim-no-steps* (fn-exp-lim-make 3 2 0 600 60 2 1 :none))
(defconst *pxt-lim-closed* (fn-exp-lim-make 0 2 2 600 60 2 1 :none))

(defconst *pxt-a* '(:inet 127 0 0 2))
(defconst *pxt-b* '(:inet 127 0 0 3))

; An owner with no connection, room for eight, next id 5, and the empty
; configuration: fn-own-open runs over it.
(defconst *pxt-owner*
  (fn-own-make nil nil nil 5 8 nil nil nil nil nil nil nil nil))
(defconst *pxt-oc* (fn-ocfg-make *pxt-owner* (fn-cfg-initial) nil nil))

(defmacro pxt-open (oc xs lim address now)
  `(fn-exp-open ,oc ,xs ,lim *aut-required* nil ,address ,now))

; -----------------------------------------------------------------------------
; The rows: absent rows take the listener's defaults; a row wins.

(assert-event (not (fn-exp-address-publicp :inet '(127 0 0 1))))
(assert-event (not (fn-exp-address-publicp :inet6 *fn-ncfg-listener-ipv6-loopback*)))
(assert-event (fn-exp-address-publicp :inet '(192 0 2 7)))
(assert-event (not (fn-exp-address-publicp :inet nil)))

(defconst *pxt-v-empty* (fn-cfg-value (fn-cfg-initial)))
; One of the run's 32 is the operator's (fn-exp-socket-cap).
(assert-event (equal (fn-exp-limits *pxt-v-empty* 32 nil nil)
                     (fn-exp-lim-make 31 31 0 0 0 0 0 :open)))
(assert-event (equal (fn-exp-limits *pxt-v-empty* 32 t nil)
                     (fn-exp-lim-make 31 8 64 600 60 10 60 :none)))
(assert-event (equal (fn-exp-lim-total (fn-exp-limits *pxt-v-empty* 1 nil nil)) 1))
; `[auth] required' is never weakened by a row.
(defconst *pxt-v-open*
  (fn-cfg-apply-delta *pxt-v-empty* 1 0 (fn-cfg-set-policy "anonymous" "open")))
(assert-event (equal (fn-exp-lim-anonymous (fn-exp-limits *pxt-v-open* 32 t nil)) :open))
(assert-event (equal (fn-exp-lim-anonymous (fn-exp-limits *pxt-v-open* 32 t t)) :none))
; A row wins over the default, and the total never passes max_connections.
(defconst *pxt-v-rows*
  (fn-cfg-apply-delta
   (fn-cfg-apply-delta *pxt-v-empty* 1 0 (fn-cfg-set-limit "exposure-per-address" 3))
   2 0 (fn-cfg-set-limit "exposure-connections" 500)))
(assert-event (equal (fn-exp-lim-per-address (fn-exp-limits *pxt-v-rows* 32 t nil)) 3))
(assert-event (equal (fn-exp-lim-total (fn-exp-limits *pxt-v-rows* 32 t nil)) 31))

; -----------------------------------------------------------------------------
; KEYSTONE fn-exp-open-admits-within-the-limits-in-force
;   H1 (fn-exp-open-id r)

(defconst *pxt-r1* (pxt-open *pxt-oc* (fn-exp-initial) *pxt-lim* *pxt-a* 5000))
(defconst *pxt-xs1* (fn-exp-open-state *pxt-r1*))
(defconst *pxt-oc1* (fn-exp-open-ocfg *pxt-r1*))
; Witness: the first connection from A opens as id 5, with a 200/201
; greeting from the served machine, and A now holds one of its two.
(assert-event (equal (fn-exp-open-id *pxt-r1*) 5))
(assert-event (consp (fn-exp-open-effects *pxt-r1*)))
(assert-event (< 0 (fn-exp-lim-total *pxt-lim*)))
(assert-event (equal (fn-exp-count-address *pxt-a* (fn-exp-conns *pxt-xs1*)) 1))
(assert-event (equal (len (fn-own-conns (fn-ocfg-owner *pxt-oc1*))) 1))
; The second from A opens; the third from A is refused 400 by address,
; while B still opens: the refusal is the address's, not the node's.
(defconst *pxt-r2* (pxt-open *pxt-oc1* *pxt-xs1* *pxt-lim* *pxt-a* 5001))
(assert-event (equal (fn-exp-open-id *pxt-r2*) 6))
(defconst *pxt-r3* (pxt-open (fn-exp-open-ocfg *pxt-r2*) (fn-exp-open-state *pxt-r2*)
                             *pxt-lim* *pxt-a* 5002))
(assert-event (null (fn-exp-open-id *pxt-r3*)))
(assert-event (equal (fn-exp-open-refusal *pxt-r3*)
                     (fn-exp-line *fn-exp-address-line*)))
(defconst *pxt-r4* (pxt-open (fn-exp-open-ocfg *pxt-r2*) (fn-exp-open-state *pxt-r2*)
                             *pxt-lim* *pxt-b* 5002))
(assert-event (equal (fn-exp-open-id *pxt-r4*) 7))
; Then the node is full at 3: B's second is refused busy.
(defconst *pxt-r5* (pxt-open (fn-exp-open-ocfg *pxt-r4*) (fn-exp-open-state *pxt-r4*)
                             *pxt-lim* *pxt-b* 5003))
(assert-event (null (fn-exp-open-id *pxt-r5*)))
(assert-event (equal (fn-exp-open-refusal *pxt-r5*) (fn-exp-line *fn-exp-busy-line*)))
; H1 dropped: under a total of 0 the open is refused, every retained
; premise (there are none) holds, and the first conclusion is false.
(defconst *pxt-r0* (pxt-open *pxt-oc* (fn-exp-initial) *pxt-lim-closed* *pxt-a* 5000))
(assert-event (null (fn-exp-open-id *pxt-r0*)))
(must-fail
 (assert-event (< (len (fn-own-conns (fn-ocfg-owner *pxt-oc*)))
                  (fn-exp-lim-total *pxt-lim-closed*))))
; A lowered limit (reconfiguration) closes nothing and admits nothing more
; from A: fn-exp-open-never-exceeds-a-limit-in-force.
(defconst *pxt-lim-lower* (fn-exp-lim-make 3 1 2 600 60 2 1 :none))
(defconst *pxt-r6* (pxt-open (fn-exp-open-ocfg *pxt-r2*) (fn-exp-open-state *pxt-r2*)
                             *pxt-lim-lower* *pxt-a* 5004))
(assert-event (null (fn-exp-open-id *pxt-r6*)))
(assert-event (equal (fn-exp-count-address *pxt-a* (fn-exp-conns (fn-exp-open-state *pxt-r6*))) 2))

; -----------------------------------------------------------------------------
; KEYSTONE fn-exp-charge-bounds-steps-per-quantum
;   H1 e (the connection is registered)
;   H2 (posp (fn-exp-lim-steps lim))
;   H3 (equal (car r) :proceed)

(defconst *pxt-c1* (fn-exp-charge *pxt-xs1* *pxt-lim* 5 5100))
(defconst *pxt-c2* (fn-exp-charge (cdr *pxt-c1*) *pxt-lim* 5 5200))
(defconst *pxt-c3* (fn-exp-charge (cdr *pxt-c2*) *pxt-lim* 5 5300))
; Witness: two steps proceed in quantum 5 and leave A's count at the budget.
(assert-event (equal (car *pxt-c1*) :proceed))
(assert-event (equal (car *pxt-c2*) :proceed))
(assert-event (equal (fn-exp-count-in *pxt-a* 5 (fn-exp-rates (cdr *pxt-c2*))) 2))
; The third waits 700 ms for quantum 6 (H3's teeth below), and then goes.
(assert-event (equal (car *pxt-c3*) '(:defer 700)))
(assert-event (equal (car (fn-exp-charge (cdr *pxt-c3*) *pxt-lim* 5 6000)) :proceed))
; H3 dropped: the deferred charge keeps H1 and H2; its "before" count is 2,
; not below the budget of 2.
(assert-event (fn-exp-find 5 (fn-exp-conns (cdr *pxt-c2*))))
(must-fail
 (assert-event (< (fn-exp-count-in *pxt-a* 5 (fn-exp-rates (cdr *pxt-c2*)))
                  (fn-exp-lim-steps *pxt-lim*))))
; H2 dropped: with no budget every step proceeds, even over a count of 2.
(assert-event (equal (car (fn-exp-charge (cdr *pxt-c2*) *pxt-lim-no-steps* 5 5300))
                     :proceed))
(must-fail
 (assert-event (< (fn-exp-count-in *pxt-a* 5 (fn-exp-rates (cdr *pxt-c2*)))
                  (fn-exp-lim-steps *pxt-lim-no-steps*))))
; H1 dropped: an unknown connection proceeds, and the address its (absent)
; entry names, nil, may carry any count: a state with 5 steps for nil.
(defconst *pxt-xs-nil*
  (fn-exp-make nil (list (list nil 5 5)) nil nil (list 0 0 0 0 0 0 0 0 0)))
(assert-event (equal (car (fn-exp-charge *pxt-xs-nil* *pxt-lim* 99 5300)) :proceed))
(must-fail
 (assert-event (< (fn-exp-count-in nil 5 (fn-exp-rates *pxt-xs-nil*))
                  (fn-exp-lim-steps *pxt-lim*))))

; The per-principal post rate: after one submission in this minute the
; principal's connection waits for the next minute.
(defconst *pxt-o1* (fn-exp-observe *pxt-xs1* *pxt-lim* 5 5400
                                   (fn-exp-line "240 article received OK") 40
                                   *aut-principal* t))
(assert-event (equal (car *pxt-o1*) :continue))
(assert-event (equal (car (fn-exp-charge (cdr *pxt-o1*) *pxt-lim* 5 5500))
                     '(:defer 54500)))

; -----------------------------------------------------------------------------
; KEYSTONE fn-exp-anonymous-none-gates-every-restricted-command
;   H0 (equal (fn-exp-lim-anonymous lim) :none)
;   H1 sessionp   H2 not handshaking   H3 config is the pinned one
;   H4 no subject H5 command input     H6 arguments at most
;   H7 restricted keyword

(defconst *pxt-pinned* (fn-exp-pinned-acfg *aut-required* *pxt-lim*))
(assert-event (equal *pxt-pinned* *aut-required*))
(assert-event (equal (fn-auth-session-config *aut-s-req*) *pxt-pinned*))
; Under :none an operator configuration that requires nothing is pinned as
; one that requires a login, with its credentials kept.
(defconst *pxt-pinned-open* (fn-exp-pinned-acfg *aut-open* *pxt-lim*))
(assert-event (fn-auth-config-requiredp *pxt-pinned-open*))
(defconst *pxt-s-pinned-open* (aut-session *pxt-pinned-open* nil))
; Witness: GROUP and POST are 480 and nothing is submitted.
(assert-event (equal (aut-reply *pxt-s-pinned-open* "GROUP fn.letters")
                     (aut-single *aut-480*)))
(assert-event (equal (aut-reply *pxt-s-pinned-open* "POST") (aut-single *aut-480*)))
(assert-event (null (fn-post-result-submission (aut-step *pxt-s-pinned-open* "POST"))))
(assert-event (fn-auth-restricted-keywordp (fn-nntp-string-octets "POST")))
; H0 dropped: under :open the operator's open configuration is pinned as it
; is, the session config is the pinned one, and GROUP runs.
(defconst *pxt-pinned-under-open* (fn-exp-pinned-acfg *aut-open* *pxt-lim-open*))
(assert-event (equal *pxt-pinned-under-open* *aut-open*))
(must-fail
 (assert-event (equal (aut-reply *aut-s-open* "GROUP fn.letters")
                      (aut-single *aut-480*))))
; H3 dropped: under :none, a session carrying the operator's open
; configuration (not the pinned one) answers GROUP.
(assert-event (not (equal (fn-auth-session-config *aut-s-open*)
                          (fn-exp-pinned-acfg *aut-open* *pxt-lim*))))
; H1, H2, H4 to H7 dropped: each ground value of the underlying keystone's
; teeth (tests/acl2/nntp-auth-teeth-tests.lisp) keeps the pinned config
; *aut-required* = (fn-exp-pinned-acfg *aut-required* *pxt-lim*):
(assert-event (equal (fn-auth-session-config *aut-forged*) *pxt-pinned*))
(must-fail (assert-event (equal (aut-reply *aut-forged* "GROUP fn.letters")
                                (aut-single *aut-480*))))
(assert-event (equal (fn-auth-session-config *aut-s-handshaking*) *pxt-pinned*))
(must-fail (assert-event (equal (aut-reply *aut-s-handshaking* "GROUP fn.letters")
                                (aut-single *aut-480*))))
(assert-event (equal (fn-auth-session-config (aut-authed)) *pxt-pinned*))
(assert-event (not (equal (aut-reply (aut-authed) "ARTICLE 1") (aut-single *aut-480*))))
(assert-event
 (not (equal (fn-post-result-effects
              (fn-auth-step *aut-s-req* *aut-archive* *aut-config* *aut-obs* *aut-obs*
                            (list :command *aut-over-long-line*)))
             (aut-single *aut-480*))))
(assert-event
 (not (equal (fn-post-result-effects
              (fn-auth-step *aut-s-req* *aut-archive* *aut-config* *aut-obs* *aut-obs*
                            (list :command *aut-over-long-argument-line*)))
             (aut-single *aut-480*))))
(assert-event (not (fn-auth-restricted-keywordp (fn-nntp-string-octets "DATE"))))
(assert-event (not (equal (aut-reply *aut-s-req* "DATE") (aut-single *aut-480*))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-exp-limits-never-drop-a-connection (and the two closes)

(assert-event (member-equal 5 (fn-exp-ids (fn-exp-conns *pxt-xs1*))))
(assert-event (member-equal 5 (fn-exp-ids (fn-exp-conns (cdr *pxt-c3*)))))
; A limit of zero everywhere still drops nothing.
(defconst *pxt-lim-zero* (fn-exp-lim-make 0 0 0 0 0 0 0 :none))
(assert-event (member-equal 5 (fn-exp-ids (fn-exp-conns
                                           (cdr (fn-exp-charge *pxt-xs1* *pxt-lim-zero* 5 9000))))))
(assert-event (equal (car (fn-exp-idle *pxt-xs1* *pxt-lim-zero* 5 999999999)) :keep))
; Only release removes, and only the connection named.
(assert-event (not (member-equal 5 (fn-exp-ids (fn-exp-conns (fn-exp-release *pxt-xs1* 5))))))

; fn-exp-idle-closes-only-silence.  Witness: never answered, 60 s after
; open: closed.  59 s: kept.  Answered 70 s after open (the first-command
; timer no longer applies): kept until 600 s of silence.
(assert-event (equal (car (fn-exp-idle *pxt-xs1* *pxt-lim* 5 65000)) :close))
(assert-event (equal (car (fn-exp-idle *pxt-xs1* *pxt-lim* 5 64999)) :keep))
(defconst *pxt-answered*
  (cdr (fn-exp-observe *pxt-xs1* *pxt-lim* 5 5100 (fn-exp-line "111 20260926000000")
                       6 nil nil)))
(assert-event (equal (car (fn-exp-idle *pxt-answered* *pxt-lim* 5 70000)) :keep))
(assert-event (equal (car (fn-exp-idle *pxt-answered* *pxt-lim* 5 605100)) :close))
; Slowloris: 511 octets consumed with no reply is not progress; 512 is.
(defconst *pxt-trickle*
  (cdr (fn-exp-observe *pxt-xs1* *pxt-lim* 5 50000 nil 511 nil nil)))
(assert-event (equal (car (fn-exp-idle *pxt-trickle* *pxt-lim* 5 65000)) :close))
(defconst *pxt-significant*
  (cdr (fn-exp-observe *pxt-trickle* *pxt-lim* 5 50000 nil 1 nil nil)))
(assert-event (equal (car (fn-exp-idle *pxt-significant* *pxt-lim* 5 65000)) :keep))

; fn-exp-observe-closes-only-on-a-failed-login.  Witness: the second 481
; in the minute closes with the 400; the first does not.
(defconst *pxt-481* (fn-exp-line "481 authentication failed"))
(defconst *pxt-f1* (fn-exp-observe *pxt-xs1* *pxt-lim* 5 5100 *pxt-481* 30 nil nil))
(assert-event (equal (car *pxt-f1*) :continue))
(defconst *pxt-f2* (fn-exp-observe (cdr *pxt-f1*) *pxt-lim* 5 5200 *pxt-481* 30 nil nil))
(assert-event (equal (car *pxt-f2*) (list :close (fn-exp-line *fn-exp-auth-close-line*))))
(assert-event (equal (fn-exp-481-count *pxt-481* t) 1))
; And the address is refused at the next accept for the rest of the minute.
(defconst *pxt-r7* (pxt-open *pxt-oc1* (cdr *pxt-f2*) *pxt-lim* *pxt-a* 5300))
(assert-event (equal (fn-exp-open-refusal *pxt-r7*) (fn-exp-line *fn-exp-auth-line*)))
(assert-event (equal (fn-exp-open-id (pxt-open *pxt-oc1* (cdr *pxt-f2*) *pxt-lim* *pxt-a* 60000))
                     6))

; The health lines say pressure is held after a refusal in this minute.
(assert-event
 (equal (take 23 (fn-exp-health-lines (fn-exp-open-state *pxt-r5*) *pxt-lim* 3 5003))
        (fn-record-string-octets "exposure pressure held ")))
(assert-event
 (equal (take 24 (fn-exp-health-lines (fn-exp-initial) *pxt-lim* 0 5003))
        (fn-record-string-octets "exposure pressure clear ")))
