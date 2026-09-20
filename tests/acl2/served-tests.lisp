; Evidence for the served path (books/served.lisp).
;
; Order follows docs/proof-style.md section 6: the guard-world audit first,
; then the malformed-input regressions, then the scenarios, then the teeth.
;
; The scenario is the reader's own transcript: one committed article in one
; group, and the command stream GROUP / STAT / QUIT.  Two of the cuts are the
; ones packet P1 names.  Cut A falls inside a command (between the `t` and the
; `t` of "fn.letters"); cut B falls inside the reply stream, after the 211 has
; already been earned and inside the next command, which is the case a
; one-event-at-a-time adapter used to handle with a Python loop.

(in-package "ACL2")
(include-book "../../books/served")

; -----------------------------------------------------------------------------
; Guard-world audit
;
; specs/node-functionality.md section 3.1: the served entry point is total in
; the executable sense, not only in the logic.  Guard `t` verified means raw
; Common Lisp evaluation on ANY arguments computes the value without a guard
; violation.  The whole-closure version of this check is packet P2.

(assert-event (equal (symbol-class 'fn-served-step (w state))
                     :common-lisp-compliant))
(assert-event (equal (guard 'fn-served-step nil (w state)) *t*))
(assert-event (equal (symbol-class 'fn-served-run (w state))
                     :common-lisp-compliant))
(assert-event (equal (guard 'fn-served-run nil (w state)) *t*))
(assert-event (equal (symbol-class 'fn-served-open (w state))
                     :common-lisp-compliant))
(assert-event (equal (symbol-class 'fn-served-reply-octets (w state))
                     :common-lisp-compliant))
(assert-event (equal (symbol-class 'fn-served-closingp (w state))
                     :common-lisp-compliant))
(assert-event (equal (symbol-class 'fn-served-post-outcome (w state))
                     :common-lisp-compliant))
(assert-event (equal (guard 'fn-served-post-outcome nil (w state)) *t*))

; -----------------------------------------------------------------------------
; The scenario

(defconst *fn-t-served-groups* '("fn.letters"))
(defconst *fn-t-served-id* "<reader@example.invalid>")
(defconst *fn-t-served-payload*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 114 101 97 100 101 114 64
    101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 62 13 10 13 10
    72 101 108 108 111 13 10))
(defconst *fn-t-served-archive*
  (fn-accept-complete
   (fn-accept-prepare (fn-initial-state *fn-t-served-groups*) 1
                      *fn-t-served-id* *fn-t-served-payload*
                      *fn-t-served-groups*)
   0 1 :durable))

; RFC 3977 section 3.1's 512 octets include the CRLF, so the wire holds 510.
; The posting configuration and the clock observation are pinned into the
; connection at open (books/served.lisp fn-served-open).
(defconst *fn-t-served-agent*
  '(102 110 46 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100))
(defconst *fn-t-served-config*
  (fn-inj-make-config t *fn-t-served-agent*
                      (list '(102 110 46 108 101 116 116 101 114 115)) 32768))
(defconst *fn-t-served-observation*
  (fn-clock-observation 1000000 843004800000 500 t))
(defconst *fn-t-served-open*
  (fn-served-open *fn-t-served-archive* 510 8192
                  *fn-t-served-config* *fn-t-served-observation*
                  *fn-t-served-observation*))
(defconst *fn-t-served-conn* (fn-served-result-conn *fn-t-served-open*))

(defconst *fn-t-served-greeting*
  '(50 48 49 32 102 110 45 110 110 116 112 32 101 120 112 101 114 105 109
    101 110 116 97 108 32 114 101 97 100 101 114 32 114 101 97 100 121 13 10))
(defconst *fn-t-served-command*
  '(71 82 79 85 80 32 102 110 46 108 101 116 116 101 114 115 13 10 83 84 65
    84 13 10 81 85 73 84 13 10))
(defconst *fn-t-served-reply*
  '(50 49 49 32 49 32 49 32 49 32 102 110 46 108 101 116 116 101 114 115 13
    10 50 50 51 32 49 32 60 114 101 97 100 101 114 64 101 120 97 109 112 108
    101 46 105 110 118 97 108 105 100 62 32 114 101 116 114 105 101 118 101
    100 13 10 50 48 53 32 99 108 111 115 105 110 103 32 99 111 110 110 101
    99 116 105 111 110 13 10))
(defconst *fn-t-served-group-command*
  '(71 82 79 85 80 32 102 110 46 108 101 116 116 101 114 115 13 10))
(defconst *fn-t-served-group-reply*
  '(50 49 49 32 49 32 49 32 49 32 102 110 46 108 101 116 116 101 114 115 13
    10))

; Opening is a connection, and the greeting is the only thing owed before the
; client speaks.
(assert-event (fn-served-connp *fn-t-served-conn*))
(assert-event (equal (fn-served-reply-octets
                      (fn-served-result-effects *fn-t-served-open*))
                     *fn-t-served-greeting*))

; A reachable, non-degenerate run: three commands, three replies, a close.
(assert-event (equal (fn-served-reply-octets
                      (fn-served-result-effects
                       (fn-served-step *fn-t-served-conn* *fn-t-served-command*)))
                     *fn-t-served-reply*))
(assert-event (fn-served-closingp
               (fn-served-result-effects
                (fn-served-step *fn-t-served-conn* *fn-t-served-command*))))
(assert-event (fn-served-effectsp
               (fn-served-result-effects
                (fn-served-step *fn-t-served-conn* *fn-t-served-command*))))
(assert-event (fn-served-connp
               (fn-served-result-conn
                (fn-served-step *fn-t-served-conn* *fn-t-served-command*))))

; -----------------------------------------------------------------------------
; The two-chunk witness
;
; Cut A: inside the GROUP command's argument.  The first chunk earns nothing.
(defconst *fn-t-served-cut-a*
  (list
    '(71 82 79 85 80 32 102 110 46 108 101 116)
    '(116 101 114 115 13 10 83 84 65 84 13 10 81 85 73 84 13 10)))

; Cut B: after the GROUP reply and inside the STAT command, so the first
; chunk's reply is a strict, non-empty prefix of the whole reply stream.
(defconst *fn-t-served-cut-b*
  (list
    '(71 82 79 85 80 32 102 110 46 108 101 116 116 101 114 115 13 10 83 84)
    '(65 84 13 10 81 85 73 84 13 10)))

(assert-event (equal (fn-served-reply-octets
                      (fn-served-result-effects
                       (fn-served-step *fn-t-served-conn*
                         '(71 82 79 85 80 32 102 110 46 108 101 116 116 101
                           114 115 13 10 83 84))))
                     *fn-t-served-group-reply*))

(assert-event (fn-served-chunk-listp *fn-t-served-cut-a*))
(assert-event (fn-served-chunk-listp *fn-t-served-cut-b*))
(assert-event (equal (fn-served-concat *fn-t-served-cut-a*) *fn-t-served-command*))
(assert-event (equal (fn-served-concat *fn-t-served-cut-b*) *fn-t-served-command*))

; fn-served-run-is-the-concatenated-step, evaluated on both cuts and on the
; bytewise partition: the whole result, state and effects, not only the bytes.
(assert-event (equal (fn-served-run *fn-t-served-conn* *fn-t-served-cut-a*)
                     (fn-served-step *fn-t-served-conn* *fn-t-served-command*)))
(assert-event (equal (fn-served-run *fn-t-served-conn* *fn-t-served-cut-b*)
                     (fn-served-step *fn-t-served-conn* *fn-t-served-command*)))
(defconst *fn-t-served-bytewise*
  (list '(71)
        '(82)
        '(79)
        '(85)
        '(80)
        '(32)
        '(102)
        '(110)
        '(46)
        '(108)
        '(101)
        '(116)
        '(116)
        '(101)
        '(114)
        '(115)
        '(13)
        '(10)
        '(83)
        '(84)
        '(65)
        '(84)
        '(13)
        '(10)
        '(81)
        '(85)
        '(73)
        '(84)
        '(13)
        '(10)))
(assert-event (equal (fn-served-run *fn-t-served-conn* *fn-t-served-bytewise*)
                     (fn-served-step *fn-t-served-conn* *fn-t-served-command*)))
(assert-event (equal (fn-served-reply-octets
                      (fn-served-result-effects
                       (fn-served-run *fn-t-served-conn* *fn-t-served-bytewise*)))
                     *fn-t-served-reply*))

; -----------------------------------------------------------------------------
; Work per read, on the witness
;
; fn-served-step-nntp-steps-is-bounded, instantiated.  Three dispatcher steps
; for thirty octets: the bound is pessimistic by a factor of ten on this
; transcript, which is the honest distance to quote beside it.  The per-step
; cost of fn-nntp-step is still OPEN (books/served.lisp records the obligation).
(assert-event (equal (fn-served-step-nntp-steps *fn-t-served-conn*
                                                *fn-t-served-command*)
                     3))
(assert-event (<= (fn-served-step-nntp-steps *fn-t-served-conn*
                                             *fn-t-served-command*)
                  (len *fn-t-served-command*)))

; -----------------------------------------------------------------------------
; Teeth
;
; fn-served-step-preserves-connp has two hypotheses.
;
; (1) fn-served-connp conn.  The violating value: a connection whose session
; carries the projection verdict `t` against an archive that is not a state at
; all.  fn-nntp-session-consistentp's second clause fails, and the conclusion
; fails with it: after one GROUP command the resulting connection is still not
; a connection.  The witness is well shaped -- the wire is a real initial wire
; state and the session is a real fn-nntp-sessionp -- so it separates the
; predicate by more than its weakest clause.

(defconst *fn-t-served-forged*
  (fn-served-make-conn (fn-wire-initial-state 510 8192)
                       (fn-post-make-session (fn-nntp-make-session t nil nil t)
                                             nil)
                       nil *fn-t-served-config* *fn-t-served-observation*
                       *fn-t-served-observation*))

(assert-event (fn-wire-statep (fn-served-conn-wire *fn-t-served-forged*)))
(assert-event (fn-post-sessionp (fn-served-conn-session *fn-t-served-forged*)))
(assert-event (fn-served-conn-shapep *fn-t-served-forged*))
(assert-event (not (fn-served-connp *fn-t-served-forged*)))
(assert-event (not (fn-served-connp
                    (fn-served-result-conn
                     (fn-served-step *fn-t-served-forged*
                                     *fn-t-served-group-command*)))))

; (2) fn-wire-octet-listp octets.  NO violating value found, recorded open
; rather than faked.  The reason is structural: fn-wire-drive re-checks
; fn-wire-statep at every turn and fn-wire-feed-byte refuses a value outside
; 0..255 by closing the framing, so a non-octet chunk yields a connection that
; is still a connection and a result that is still partition independent.  The
; hypothesis is nevertheless required, because the lemma this theorem is lifted
; from (fn-wire-drive-preserves-statep, books/wire-invariants.lisp:563) carries
; it.  Two concrete probes, both of which hold rather than fail:
;
;   (fn-served-connp (fn-served-result-conn (fn-served-step conn '(300))))   = T
;   (equal (fn-served-step conn (append '(300) group))
;          (fn-served-run conn (list '(300) group)))                        = T
;
; The obligation: either strengthen fn-wire-drive-preserves-statep to drop the
; octet hypothesis, and then drop it here, or produce a chunk that separates
; it.  Until one of those happens this hypothesis has no tooth.
;
; fn-served-step-effects-are-typed carries fn-served-connp for the same reason
; fn-nntp-step-effects-well-formed does (books/nntp-effects.lisp:846), and the
; teeth for THAT hypothesis are in tests/acl2/nntp-teeth-tests.lisp, where the
; keystone lives.  The forged connection above does not separate it: a session
; with an unusable archive still answers 411 and 503, which are well-formed
; replies.  Measured here so the claim is not taken on trust:
(assert-event (fn-served-effectsp
               (fn-served-result-effects
                (fn-served-step *fn-t-served-forged*
                                *fn-t-served-group-command*))))

; -----------------------------------------------------------------------------
; POST through the served step: 340, the article, a submission, then the
; outcome fed back.  Article mode is wire state inside the connection, so the
; offer and the body are one read, and a cut inside the body is the same read.

(defconst *fn-t-served-post-command* '(80 79 83 84 13 10))
(defconst *fn-t-served-article*
  (append '(70 114 111 109 58 32 112 111 115 116 101 114 64 101 120 97 109
            112 108 101 46 105 110 118 97 108 105 100 13 10
            83 117 98 106 101 99 116 58 32 104 101 108 108 111 13 10
            78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101
            116 116 101 114 115 13 10
            13 10
            72 101 108 108 111 44 32 110 101 119 115 46 13 10)
          '(46 13 10)))
(defconst *fn-t-served-post-read*
  (append *fn-t-served-post-command* *fn-t-served-article*))
(defconst *fn-t-served-offer*
  (fn-served-reply-octets
   (fn-served-result-effects
    (fn-served-step *fn-t-served-conn* *fn-t-served-post-command*))))
(defconst *fn-t-served-post-result*
  (fn-served-step *fn-t-served-conn* *fn-t-served-post-read*))
(defconst *fn-t-served-post-effects*
  (fn-served-result-effects *fn-t-served-post-result*))
(defconst *fn-t-served-post-conn*
  (fn-served-result-conn *fn-t-served-post-result*))

; The offer is a 340; after POST alone the wire is in article mode.
(assert-event (equal (take 4 *fn-t-served-offer*) '(51 52 48 32)))
(assert-event (equal (fn-wire-state-mode
                      (fn-served-conn-wire
                       (fn-served-result-conn
                        (fn-served-step *fn-t-served-conn*
                                        *fn-t-served-post-command*))))
                     :article))
; The whole read replies with the offer alone: an injected article is a
; submission, not a reply.  The wire is back in command mode and the session
; no longer awaits.
(assert-event (equal (fn-served-reply-octets *fn-t-served-post-effects*)
                     *fn-t-served-offer*))
(assert-event (fn-inj-injectedp (fn-served-submission *fn-t-served-post-effects*)))
(assert-event (fn-served-effectsp *fn-t-served-post-effects*))
(assert-event (not (fn-served-closingp *fn-t-served-post-effects*)))
(assert-event (equal (fn-wire-state-mode (fn-served-conn-wire *fn-t-served-post-conn*))
                     :command))
(assert-event (not (fn-post-session-awaiting
                    (fn-served-conn-session *fn-t-served-post-conn*))))
(assert-event (fn-served-connp *fn-t-served-post-conn*))
(assert-event (equal (fn-served-step-nntp-steps *fn-t-served-conn*
                                                *fn-t-served-post-read*)
                     2))

; A cut between the offer and the body, and one inside the body, are the
; same read (fn-served-run-is-the-concatenated-step, with article mode).
(defconst *fn-t-served-post-cut*
  (list *fn-t-served-post-command*
        (take 20 *fn-t-served-article*)
        (nthcdr 20 *fn-t-served-article*)))
(assert-event (fn-served-chunk-listp *fn-t-served-post-cut*))
(assert-event (equal (fn-served-concat *fn-t-served-post-cut*)
                     *fn-t-served-post-read*))
(assert-event (equal (fn-served-run *fn-t-served-conn* *fn-t-served-post-cut*)
                     *fn-t-served-post-result*))

; The outcome, fed back as one more served input: 240 from :durable and from
; nothing else; the two 441s are distinct; the connection is unchanged.
(defconst *fn-t-served-240*
  (fn-served-reply-octets
   (fn-served-result-effects
    (fn-served-post-outcome *fn-t-served-post-conn* :durable))))
(defconst *fn-t-served-441-refused*
  (fn-served-reply-octets
   (fn-served-result-effects
    (fn-served-post-outcome *fn-t-served-post-conn* :refused))))
(defconst *fn-t-served-441-uncertain*
  (fn-served-reply-octets
   (fn-served-result-effects
    (fn-served-post-outcome *fn-t-served-post-conn* :uncertain))))
(assert-event (equal (take 4 *fn-t-served-240*) '(50 52 48 32)))
(assert-event (equal (take 4 *fn-t-served-441-refused*) '(52 52 49 32)))
(assert-event (equal (take 4 *fn-t-served-441-uncertain*) '(52 52 49 32)))
(assert-event (not (equal *fn-t-served-441-refused* *fn-t-served-441-uncertain*)))
(assert-event (equal (fn-served-result-conn
                      (fn-served-post-outcome *fn-t-served-post-conn* :durable))
                     *fn-t-served-post-conn*))
(assert-event (fn-served-effectsp
               (fn-served-result-effects
                (fn-served-post-outcome *fn-t-served-post-conn* :durable))))

; A refusal: the same body without From is a 441 with its reason after the
; offer, and submits nothing.
(defconst *fn-t-served-bad-article*
  (append '(83 117 98 106 101 99 116 58 32 104 101 108 108 111 13 10
            78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101
            116 116 101 114 115 13 10
            13 10
            72 101 108 108 111 46 13 10)
          '(46 13 10)))
(defconst *fn-t-served-refused-effects*
  (fn-served-result-effects
   (fn-served-step *fn-t-served-conn*
                   (append *fn-t-served-post-command* *fn-t-served-bad-article*))))
(assert-event (equal (take (len *fn-t-served-offer*)
                           (fn-served-reply-octets *fn-t-served-refused-effects*))
                     *fn-t-served-offer*))
(assert-event (equal (take 4 (nthcdr (len *fn-t-served-offer*)
                                     (fn-served-reply-octets
                                      *fn-t-served-refused-effects*)))
                     '(52 52 49 32)))
(assert-event (null (fn-served-submission *fn-t-served-refused-effects*)))
(assert-event (fn-served-effectsp *fn-t-served-refused-effects*))

; Posting disallowed: 440, and the wire never enters article mode.
(defconst *fn-t-served-closed-config*
  (fn-inj-make-config nil *fn-t-served-agent*
                      (list '(102 110 46 108 101 116 116 101 114 115)) 32768))
(defconst *fn-t-served-440-result*
  (fn-served-step
   (fn-served-result-conn
    (fn-served-open *fn-t-served-archive* 510 8192
                    *fn-t-served-closed-config* *fn-t-served-observation*
                    *fn-t-served-observation*))
   *fn-t-served-post-command*))
(assert-event (equal (take 4 (fn-served-reply-octets
                              (fn-served-result-effects *fn-t-served-440-result*)))
                     '(52 52 48 32)))
(assert-event (equal (fn-wire-state-mode
                      (fn-served-conn-wire
                       (fn-served-result-conn *fn-t-served-440-result*)))
                     :command))
(assert-event (null (fn-served-submission
                     (fn-served-result-effects *fn-t-served-440-result*))))
