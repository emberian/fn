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
  (fn-own-make nil nil nil 5 8 nil nil nil nil nil nil nil nil nil nil))
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
;; The arena and its lifts (in-arena-aut-reply, -aut-step, -fn-auth-step) are
;; nntp-auth-teeth-tests': *aut-arena* holds *aut-payload* at handle 0.
(assert-event (equal (in-arena-aut-reply *aut-arena* *pxt-s-pinned-open* "GROUP fn.letters")
                     (aut-single *aut-480*)))
(assert-event (equal (in-arena-aut-reply *aut-arena* *pxt-s-pinned-open* "POST") (aut-single *aut-480*)))
(assert-event (null (fn-post-result-submission (in-arena-aut-step *aut-arena* *pxt-s-pinned-open* "POST"))))
(assert-event (fn-auth-restricted-keywordp (fn-nntp-string-octets "POST")))
; H0 dropped: under :open the operator's open configuration is pinned as it
; is, the session config is the pinned one, and GROUP runs.
(defconst *pxt-pinned-under-open* (fn-exp-pinned-acfg *aut-open* *pxt-lim-open*))
(assert-event (equal *pxt-pinned-under-open* *aut-open*))
(must-fail
 (assert-event (equal (in-arena-aut-reply *aut-arena* *aut-s-open* "GROUP fn.letters")
                      (aut-single *aut-480*))))
; H3 dropped: under :none, a session carrying the operator's open
; configuration (not the pinned one) answers GROUP.
(assert-event (not (equal (fn-auth-session-config *aut-s-open*)
                          (fn-exp-pinned-acfg *aut-open* *pxt-lim*))))
; H1, H2, H4 to H7 dropped: each ground value of the underlying keystone's
; teeth (tests/acl2/nntp-auth-teeth-tests.lisp) keeps the pinned config
; *aut-required* = (fn-exp-pinned-acfg *aut-required* *pxt-lim*):
(assert-event (equal (fn-auth-session-config *aut-forged*) *pxt-pinned*))
(must-fail (assert-event (equal (in-arena-aut-reply *aut-arena* *aut-forged* "GROUP fn.letters")
                                (aut-single *aut-480*))))
(assert-event (equal (fn-auth-session-config *aut-s-handshaking*) *pxt-pinned*))
(must-fail (assert-event (equal (in-arena-aut-reply *aut-arena* *aut-s-handshaking* "GROUP fn.letters")
                                (aut-single *aut-480*))))
(assert-event (equal (fn-auth-session-config (aut-authed)) *pxt-pinned*))
(assert-event (not (equal (in-arena-aut-reply *aut-arena* (aut-authed) "ARTICLE 1") (aut-single *aut-480*))))
(assert-event
 (not (equal (fn-post-result-effects
              (in-arena-fn-auth-step *aut-arena* *aut-s-req* *aut-archive* *aut-config* *aut-obs* *aut-obs* (list :command *aut-over-long-line*)))
             (aut-single *aut-480*))))
(assert-event
 (not (equal (fn-post-result-effects
              (in-arena-fn-auth-step *aut-arena* *aut-s-req* *aut-archive* *aut-config* *aut-obs* *aut-obs* (list :command *aut-over-long-argument-line*)))
             (aut-single *aut-480*))))
(assert-event (not (fn-auth-restricted-keywordp (fn-nntp-string-octets "DATE"))))
(assert-event (not (equal (in-arena-aut-reply *aut-arena* *aut-s-req* "DATE") (aut-single *aut-480*))))

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

; =============================================================================
; PRF-211 (NNT-043): the connection capacity and the trusted range.

; The trusted-range grammar: ranges, a bare address, IPv6, `none'; and
; refusals (a prefix past the family's width, two slashes, an empty word,
; an empty element, a word longer than a configuration label).
(assert-event (equal (fn-exp-trusted-of-word "192.168.1.0/24, fd00::/8")
                     '((:inet (192 168 1 0) 24)
                       (:inet6 (253 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) 8))))
(assert-event (equal (fn-exp-trusted-of-word "10.0.0.7") '((:inet (10 0 0 7) 32))))
(assert-event (equal (fn-exp-trusted-of-word "none") nil))
(assert-event (fn-exp-trusted-wordp "none"))
(assert-event (fn-exp-trusted-wordp "192.168.1.0/24"))
(assert-event (not (fn-exp-trusted-wordp "192.168.1.0/33")))
(assert-event (not (fn-exp-trusted-wordp "fd00::/129")))
(assert-event (not (fn-exp-trusted-wordp "1.2.3.4/8/9")))
(assert-event (not (fn-exp-trusted-wordp "")))
(assert-event (not (fn-exp-trusted-wordp "10.0.0.0/8,")))
(assert-event (not (fn-exp-trusted-wordp "localhost/8")))
(assert-event (not (fn-exp-trusted-wordp
                    (coerce (make-list 257 :initial-element #\1) 'string))))
; Matching is by family and the first BITS bits.
(assert-event (fn-exp-trusted-addressp '(:inet 192 168 1 77)
                                       (fn-exp-trusted-of-word "192.168.1.0/24")))
(assert-event (fn-exp-trusted-addressp '(:inet 192 168 1 77)
                                       (fn-exp-trusted-of-word "192.168.0.0/23")))
(assert-event (not (fn-exp-trusted-addressp '(:inet 192 168 2 77)
                                            (fn-exp-trusted-of-word "192.168.0.0/23"))))
(assert-event (fn-exp-trusted-addressp '(:inet 192 168 1 77)
                                       (fn-exp-trusted-of-word "0.0.0.0/0")))
(assert-event (not (fn-exp-trusted-addressp '(:inet6 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1)
                                            (fn-exp-trusted-of-word "0.0.0.0/0"))))

; The configuration rows the host reads.
(defconst *pxt-v-cap40*
  (fn-cfg-apply-delta *pxt-v-empty* 1 0 (fn-cfg-set-limit "exposure-connections" 40)))
(defconst *pxt-v-cap-u32*
  (fn-cfg-apply-delta *pxt-v-empty* 1 0
                      (fn-cfg-set-limit "exposure-connections" *fn-cbor-max-uint*)))
; Past the rows' width: a value no admitted record holds (the delta is
; refused with a reason), built here only to falsify H1.
(defconst *pxt-v-cap-wide*
  (fn-cfg-apply-delta *pxt-v-empty* 1 0
                      (fn-cfg-set-limit "exposure-connections"
                                        *fn-exp-owner-connection-bound*)))
(assert-event (fn-cfg-delta-reason *pxt-v-empty* 1 0 0 nil
                                  (fn-cfg-set-limit "exposure-connections"
                                                    *fn-exp-owner-connection-bound*)))
(assert-event (equal (fn-exp-connections-capacity *pxt-v-empty*) 31))
(assert-event (equal (fn-exp-connections-capacity *pxt-v-cap40*) 40))

; fn-exp-owner-bound-exceeds-every-capacity.  H1 (fn-cfg-limits-withinp).
(assert-event (fn-cfg-limits-withinp (fn-cfg-limits *pxt-v-cap-u32*)))
(assert-event (< (fn-exp-connections-capacity *pxt-v-cap-u32*)
                 *fn-exp-owner-connection-bound*))
(assert-event (not (fn-cfg-limits-withinp (fn-cfg-limits *pxt-v-cap-wide*))))
(must-fail
 (assert-event (< (fn-exp-connections-capacity *pxt-v-cap-wide*)
                  *fn-exp-owner-connection-bound*)))

; fn-exp-limits-total-is-the-capacity.  H1 (< capacity max-conns).
; Witness: 40 under the run's bound, above the 31 every node had.
(assert-event (< 40 *fn-exp-owner-connection-bound*))
(assert-event (equal (fn-exp-lim-total (fn-exp-limits *pxt-v-cap40*
                                                      *fn-exp-owner-connection-bound*
                                                      t nil))
                     40))
; H1 dropped: an owner bounded at the old 32 clips 40 to 31.
(assert-event (not (< 40 32)))
(must-fail
 (assert-event (equal (fn-exp-lim-total (fn-exp-limits *pxt-v-cap40* 32 t nil)) 40)))

; KEYSTONE fn-exp-open-refuses-exactly-at-the-capacity.
;   H1 (fn-cfg-limits-withinp (fn-cfg-limits v))
;   H2 (not (fn-exp-auth-refusesp xs lim address now))
(defconst *pxt-lim-cap40*
  (fn-exp-limits *pxt-v-cap40* *fn-exp-owner-connection-bound* t nil))
; Witness: the 40th held connection refuses the next with the busy 400; 39
; admit; both sides of the equality computed.
(assert-event (fn-cfg-limits-withinp (fn-cfg-limits *pxt-v-cap40*)))
(assert-event (not (fn-exp-auth-refusesp (fn-exp-initial) *pxt-lim-cap40* *pxt-a* 5000)))
(assert-event (equal (fn-exp-admit-decision (fn-exp-initial) *pxt-lim-cap40* 40 *pxt-a* 5000)
                     (list :refuse *fn-exp-busy-line* 1)))
(assert-event (equal (fn-exp-admit-decision (fn-exp-initial) *pxt-lim-cap40* 39 *pxt-a* 5000)
                     (list :admit)))
; Over a real owner bounded as a run bounds it, with capacity 2: two open,
; the third reads the named 400 and nothing opens.
(defconst *pxt-v-cap2*
  (fn-cfg-apply-delta *pxt-v-empty* 1 0 (fn-cfg-set-limit "exposure-connections" 2)))
(defconst *pxt-lim-cap2*
  (fn-exp-limits *pxt-v-cap2* *fn-exp-owner-connection-bound* nil nil))
(defconst *pxt-run-oc*
  (fn-ocfg-make (fn-own-make nil nil nil 5 *fn-exp-owner-connection-bound*
                             nil nil nil nil nil nil nil nil nil nil)
                (fn-cfg-initial) nil nil))
(defconst *pxt-k1* (pxt-open *pxt-run-oc* (fn-exp-initial) *pxt-lim-cap2* *pxt-a* 5000))
(defconst *pxt-k2* (pxt-open (fn-exp-open-ocfg *pxt-k1*) (fn-exp-open-state *pxt-k1*)
                             *pxt-lim-cap2* *pxt-b* 5001))
(defconst *pxt-k3* (pxt-open (fn-exp-open-ocfg *pxt-k2*) (fn-exp-open-state *pxt-k2*)
                             *pxt-lim-cap2* *pxt-a* 5002))
(assert-event (equal (fn-exp-open-id *pxt-k1*) 5))
(assert-event (equal (fn-exp-open-id *pxt-k2*) 6))
(assert-event (null (fn-exp-open-id *pxt-k3*)))
(assert-event (equal (fn-exp-open-refusal *pxt-k3*) (fn-exp-line *fn-exp-busy-line*)))
(assert-event (equal (fn-exp-open-refusal *pxt-k3*)
                     (fn-record-string-octets
                      (concatenate 'string "400 too many connections; try again later"
                                   (coerce (list (code-char 13) (code-char 10)) 'string)))))
; H1 dropped: a row past the width is clipped by the owner's bound, so at
; that many connections the decision is busy while the right side says admit.
(defconst *pxt-lim-wide*
  (fn-exp-limits *pxt-v-cap-wide* *fn-exp-owner-connection-bound* t nil))
(assert-event (not (fn-exp-auth-refusesp (fn-exp-initial) *pxt-lim-wide* *pxt-a* 5000)))
(must-fail
 (assert-event (equal (fn-exp-admit-decision (fn-exp-initial) *pxt-lim-wide*
                                             *fn-cbor-max-uint* *pxt-a* 5000)
                      (list :admit))))
; H2 dropped: ten 481s from A this minute under the public limit; below the
; capacity the right side says admit, the decision refuses by auth.
(defconst *pxt-xs-failed*
  (fn-exp-make nil nil (list (list *pxt-a* 0 10)) nil (list 0 0 0 0 0 0 0 0 0)))
(assert-event (fn-exp-auth-refusesp *pxt-xs-failed* *pxt-lim-cap40* *pxt-a* 5000))
(must-fail
 (assert-event (equal (fn-exp-admit-decision *pxt-xs-failed* *pxt-lim-cap40* 0 *pxt-a* 5000)
                      (list :admit))))

; KEYSTONE fn-exp-trusted-address-is-never-refused-by-address.
;   H1 (fn-exp-trusted-addressp address (fn-exp-lim-trusted lim))
(defconst *pxt-lan* '(:inet 192 168 1 1))
(defconst *pxt-wan* '(:inet 198 51 100 7))
(defconst *pxt-lim-trusted*
  (fn-exp-lim-make-full 5 1 2 600 60 2 1 :none
                        (fn-exp-trusted-of-word "192.168.1.0/24") "192.168.1.0/24"))
(defconst *pxt-v-trusted*
  (fn-cfg-apply-delta *pxt-v-cap40* 2 0 (fn-cfg-set-policy "exposure-trusted" "192.168.1.0/24")))
(assert-event (equal (fn-exp-lim-trusted
                      (fn-exp-limits *pxt-v-trusted* *fn-exp-owner-connection-bound* t nil))
                     (fn-exp-trusted-of-word "192.168.1.0/24")))
; Witness: over a real owner, the router's LAN address opens three with a
; per-address limit of 1.
(defconst *pxt-t1* (pxt-open *pxt-run-oc* (fn-exp-initial) *pxt-lim-trusted* *pxt-lan* 5000))
(defconst *pxt-t2* (pxt-open (fn-exp-open-ocfg *pxt-t1*) (fn-exp-open-state *pxt-t1*)
                             *pxt-lim-trusted* *pxt-lan* 5001))
(defconst *pxt-t3* (pxt-open (fn-exp-open-ocfg *pxt-t2*) (fn-exp-open-state *pxt-t2*)
                             *pxt-lim-trusted* *pxt-lan* 5002))
(assert-event (fn-exp-trusted-addressp *pxt-lan* (fn-exp-lim-trusted *pxt-lim-trusted*)))
(assert-event (equal (fn-exp-open-id *pxt-t3*) 7))
(assert-event (equal (fn-exp-count-address *pxt-lan* (fn-exp-conns (fn-exp-open-state *pxt-t3*)))
                     3))
(assert-event (not (equal (fn-exp-admit-decision (fn-exp-open-state *pxt-t2*) *pxt-lim-trusted*
                                                 2 *pxt-lan* 5002)
                          (list :refuse *fn-exp-address-line* 2))))
; H1 dropped: the WAN address holding its one is refused by address.
(defconst *pxt-xs-wan*
  (fn-exp-open-state (pxt-open *pxt-run-oc* (fn-exp-initial) *pxt-lim-trusted* *pxt-wan* 5000)))
(assert-event (not (fn-exp-trusted-addressp *pxt-wan* (fn-exp-lim-trusted *pxt-lim-trusted*))))
(must-fail
 (assert-event (not (equal (fn-exp-admit-decision *pxt-xs-wan* *pxt-lim-trusted* 1 *pxt-wan* 5001)
                           (list :refuse *fn-exp-address-line* 2)))))

; KEYSTONE fn-exp-untrusted-address-is-refused-exactly-at-its-limit.
;   H1 (not trusted)   H2 (not auth-refuses)   H3 (< nconns total)
; Witness: the WAN address at its limit is refused, below it admitted.
(assert-event (not (fn-exp-auth-refusesp *pxt-xs-wan* *pxt-lim-trusted* *pxt-wan* 5001)))
(assert-event (< 1 (fn-exp-lim-total *pxt-lim-trusted*)))
(assert-event (equal (fn-exp-admit-decision *pxt-xs-wan* *pxt-lim-trusted* 1 *pxt-wan* 5001)
                     (list :refuse *fn-exp-address-line* 2)))
(assert-event (equal (fn-exp-admit-decision (fn-exp-initial) *pxt-lim-trusted* 0 *pxt-wan* 5001)
                     (list :admit)))
; H1 dropped: the trusted address at its limit is admitted, not refused.
(defconst *pxt-xs-lan* (fn-exp-open-state *pxt-t1*))
(assert-event (<= (fn-exp-lim-per-address *pxt-lim-trusted*)
                  (fn-exp-count-address *pxt-lan* (fn-exp-conns *pxt-xs-lan*))))
(must-fail
 (assert-event (equal (fn-exp-admit-decision *pxt-xs-lan* *pxt-lim-trusted* 1 *pxt-lan* 5001)
                      (list :refuse *fn-exp-address-line* 2))))
; H2 dropped: two 481s from the WAN address (the limit is 2) refuse by auth.
(defconst *pxt-xs-wan-failed*
  (fn-exp-make (fn-exp-conns *pxt-xs-wan*) nil (list (list *pxt-wan* 0 2)) nil
               (list 0 0 0 0 0 0 0 0 0)))
(assert-event (fn-exp-auth-refusesp *pxt-xs-wan-failed* *pxt-lim-trusted* *pxt-wan* 5001))
(must-fail
 (assert-event (equal (fn-exp-admit-decision *pxt-xs-wan-failed* *pxt-lim-trusted* 1
                                             *pxt-wan* 5001)
                      (list :refuse *fn-exp-address-line* 2))))
; H3 dropped: at the total the decision is busy, not the address's.
(must-fail
 (assert-event (equal (fn-exp-admit-decision *pxt-xs-wan* *pxt-lim-trusted* 5 *pxt-wan* 5001)
                      (list :refuse *fn-exp-address-line* 2))))

; The capacity line `status' and `health' print.
(assert-event
 (equal (fn-exp-capacity-line (fn-exp-limits *pxt-v-trusted* *fn-exp-owner-connection-bound*
                                             t nil)
                              3)
        (fn-record-string-octets
         (concatenate 'string
                      "exposure capacity connections=3 capacity=40 per-address=8"
                      " trusted=192.168.1.0/24"
                      (coerce (list (code-char 10)) 'string)))))
(assert-event
 (equal (fn-exp-capacity-line *pxt-lim-cap40* 0)
        (fn-record-string-octets
         (concatenate 'string
                      "exposure capacity connections=0 capacity=40 per-address=8 trusted=none"
                      (coerce (list (code-char 10)) 'string)))))
