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
                  *fn-t-served-observation* (fn-auth-open-config)))
(defconst *fn-t-served-conn* (fn-served-result-conn *fn-t-served-open*))

; RFC 3977 section 5.1.1: the greeting code is the connection's posting
; permission.  This connection's pinned configuration allows posting
; (*fn-t-served-config*, fn-inj-make-config with allow T), so the greeting is
; 200 and not 201.  The 201 spelling is witnessed below against a
; configuration that refuses posting.
(defconst *fn-t-served-greeting*
  '(50 48 48 32 102 110 45 110 110 116 112 32 101 120 112 101 114 105 109
    101 110 116 97 108 32 115 101 114 118 101 114 32 114 101 97 100 121 13
    10))
(defconst *fn-t-served-greeting-prohibited*
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
; session-depth-ok: the point of this witness is a session at the WRONG level
; -- a bare POST session where a served connection carries an auth session --
; so tools/session_depth.py must not read it as a miss.
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
; The POST-composed reader session is two wrappers down now: the served
; session is fn-auth-step's, an auth session over a peer session over it.
(assert-event (not (fn-post-session-awaiting
                    (fn-auth-post-session
                     (fn-served-conn-session *fn-t-served-post-conn*)))))
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
                    *fn-t-served-observation* (fn-auth-open-config)))
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

; -----------------------------------------------------------------------------
; RFC 3977 section 5.1.1: the greeting states the posting permission
;
; The same configuration bit decides the greeting, the POST capability label
; (section 5.2.2) and what fn-nntp-post-step does with a POST command, so the
; three cannot disagree.  Witnessed both ways.

(defconst *fn-t-served-prohibited-open*
  ; The AUTHINFO policy that requires nothing and offers nothing, which is
  ; what every served theorem written before this book carried
  ; authentication means (books/nntp-auth.lisp fn-auth-open-config).
  (fn-served-open *fn-t-served-archive* 510 8192
                  *fn-t-served-closed-config* *fn-t-served-observation*
                  *fn-t-served-observation* (fn-auth-open-config)))
(assert-event (equal (fn-served-reply-octets
                      (fn-served-result-effects *fn-t-served-prohibited-open*))
                     *fn-t-served-greeting-prohibited*))
(assert-event (not (equal *fn-t-served-greeting*
                          *fn-t-served-greeting-prohibited*)))
(assert-event (equal (take 4 *fn-t-served-greeting*) '(50 48 48 32)))
(assert-event (equal (take 4 *fn-t-served-greeting-prohibited*)
                     '(50 48 49 32)))

; -----------------------------------------------------------------------------
; RFC 3977 section 3.5: a command pipelined behind the POST body
;
; One read carries POST, the article, its terminator and a GROUP command.
; The teeth for fn-served-pipelined-read-is-the-sequential-reply: the
; hypotheses are reachable on a real transcript, the conclusion is
; non-degenerate (`later' earns its own 211, so neither side of the equality
; is the other's prefix by accident), and no octet of the trailing command
; was swallowed into the article body.

(defconst *fn-t-served-pipelined-read*
  (append *fn-t-served-post-read* *fn-t-served-group-command*))
(defconst *fn-t-served-pipelined-result*
  (fn-served-step *fn-t-served-conn* *fn-t-served-pipelined-read*))
(defconst *fn-t-served-pipelined-effects*
  (fn-served-result-effects *fn-t-served-pipelined-result*))

(assert-event (fn-wire-octet-listp *fn-t-served-post-read*))
(assert-event (fn-wire-octet-listp *fn-t-served-group-command*))
(assert-event (fn-served-connp *fn-t-served-conn*))

; The trailing GROUP is framed as a command and answered: the reply stream is
; the offer followed by the 211, and the 211 is the same octets the GROUP
; earns on its own.
(assert-event (equal (fn-served-reply-octets *fn-t-served-pipelined-effects*)
                     (append *fn-t-served-offer* *fn-t-served-group-reply*)))
(assert-event (consp *fn-t-served-group-reply*))
(assert-event (not (equal (fn-served-reply-octets *fn-t-served-pipelined-effects*)
                          *fn-t-served-offer*)))

; The article was still injected: the pipelined command neither removed nor
; replaced the submission.
(assert-event (fn-inj-injectedp
               (fn-served-submission *fn-t-served-pipelined-effects*)))
(assert-event (equal (fn-served-submission *fn-t-served-pipelined-effects*)
                     (fn-served-submission *fn-t-served-post-effects*)))

; The single read equals the two sequential reads, effects and connection:
; the theorem instantiated on this transcript.
(defconst *fn-t-served-pipelined-sequential*
  (fn-served-step *fn-t-served-post-conn* *fn-t-served-group-command*))
(assert-event (equal (fn-served-reply-octets *fn-t-served-pipelined-effects*)
                     (append (fn-served-reply-octets *fn-t-served-post-effects*)
                             (fn-served-reply-octets
                              (fn-served-result-effects
                               *fn-t-served-pipelined-sequential*)))))
(assert-event (equal (fn-served-result-conn *fn-t-served-pipelined-result*)
                     (fn-served-result-conn *fn-t-served-pipelined-sequential*)))
(assert-event (fn-served-connp
               (fn-served-result-conn *fn-t-served-pipelined-result*)))
(assert-event (fn-served-effectsp *fn-t-served-pipelined-effects*))

; The group selection really happened in the same read: the session carries
; the selected group afterwards, so the trailing command was executed and not
; merely echoed.
; The served session is an auth session over a peer session over the
; POST-composed reader session, so the reader session is three accessors
; down, not two.
(assert-event (equal (fn-nntp-session-group
                      (fn-auth-reader-session
                       (fn-served-conn-session
                        (fn-served-result-conn
                         *fn-t-served-pipelined-result*))))
                     "fn.letters"))

; The framing fact the keystone rests on: the byte that completed the article
; left the wire in command mode, so the next octet of the SAME read was
; framed as a command.
(assert-event (equal (fn-wire-state-mode
                      (fn-served-conn-wire *fn-t-served-post-conn*))
                     :command))

; A three-command pipeline in one read, cut at every octet boundary the
; network could choose: partition independence holds across the POST body.
(defconst *fn-t-served-pipelined-cut*
  (list (take 3 *fn-t-served-pipelined-read*)
        (take 40 (nthcdr 3 *fn-t-served-pipelined-read*))
        (nthcdr 43 *fn-t-served-pipelined-read*)))
(assert-event (fn-served-chunk-listp *fn-t-served-pipelined-cut*))
(assert-event (equal (fn-served-concat *fn-t-served-pipelined-cut*)
                     *fn-t-served-pipelined-read*))
(assert-event (equal (fn-served-run *fn-t-served-conn* *fn-t-served-pipelined-cut*)
                     *fn-t-served-pipelined-result*))

; -----------------------------------------------------------------------------
; Teeth for the transit depth (fn-served-transit-outcome)
;
; A served connection's session is three records deep, and
; fn-peer-transit-outcome wants the PEER session -- one accessor in, not
; none.  Until this lane it was handed the whole auth session.  The reply
; octets were right anyway, and that is the whole difficulty: the transit
; reply does not read its session, so nothing on the wire could separate the
; two depths.  So this witness observes the SESSION the outcome is computed
; from, not the octets it comes out as.

(defconst *fn-t-served-transit-sub*
  (fn-peer-make-submission "innA" :ihave *fn-t-served-id* *fn-t-served-payload*))
(defconst *fn-t-served-transit-want* (fn-peer-decision :want nil))
(defconst *fn-t-served-transit-session*
  (fn-auth-session-base (fn-served-conn-session *fn-t-served-conn*)))

; The witness is not degenerate: it is a real transit submission and a real
; connection, and the two candidate sessions are DIFFERENT values of which
; exactly one is a peer session.  That is the separation: the miss was a type
; error, not a synonym.
(assert-event (fn-peer-submissionp *fn-t-served-transit-sub*))
(assert-event (fn-served-connp *fn-t-served-conn*))
(assert-event (fn-peer-sessionp *fn-t-served-transit-session*))
; session-depth-ok: the whole point of this line is that the served session
; is NOT a peer session, which is the separation the fix rests on.
(assert-event (not (fn-peer-sessionp
                    (fn-served-conn-session *fn-t-served-conn*))))
(assert-event (not (equal *fn-t-served-transit-session*
                          (fn-served-conn-session *fn-t-served-conn*))))

; The outcome the served path computes is the one over the PEER session, and
; the session that comes back out of fn-peer-transit-outcome -- which is what
; a state-dependent transit reply would read -- is that same peer session and
; not the auth session above it.
(assert-event
 (equal (fn-served-result-effects
         (fn-served-transit-outcome *fn-t-served-conn* *fn-t-served-transit-sub*
                                    *fn-t-served-transit-want* :durable))
        (fn-post-result-effects
         (fn-peer-transit-outcome *fn-t-served-transit-session*
                                  *fn-t-served-transit-sub*
                                  *fn-t-served-transit-want* :durable))))
(assert-event
 (equal (fn-post-result-session
         (fn-peer-transit-outcome *fn-t-served-transit-session*
                                  *fn-t-served-transit-sub*
                                  *fn-t-served-transit-want* :durable))
        *fn-t-served-transit-session*))
(assert-event
 (not (equal (fn-post-result-session
              (fn-peer-transit-outcome *fn-t-served-transit-session*
                                       *fn-t-served-transit-sub*
                                       *fn-t-served-transit-want* :durable))
             (fn-served-conn-session *fn-t-served-conn*))))

; A NEGATIVE CONTROL that is also the alarm.  Today the transit reply ignores
; its session, which is the only reason the wrong depth was invisible on the
; wire.  When that stops being true this assertion FAILS, and its failure is
; the notice that every fn-peer-transit-outcome call site must be re-read --
; the POST outcome is the cautionary case, where the same accident held until
; a reply became session-shaped and the served path fell silent.
; session-depth-ok: this assertion deliberately calls fn-peer-transit-outcome
; at the WRONG depth, to pin that today it makes no difference to the octets.
(assert-event
 (equal (fn-post-result-effects
         (fn-peer-transit-outcome (fn-served-conn-session *fn-t-served-conn*)
                                  *fn-t-served-transit-sub*
                                  *fn-t-served-transit-want* :durable))
        (fn-post-result-effects
         (fn-peer-transit-outcome *fn-t-served-transit-session*
                                  *fn-t-served-transit-sub*
                                  *fn-t-served-transit-want* :durable))))
(assert-event
 (equal (take 4 (fn-served-reply-octets
                 (fn-served-result-effects
                  (fn-served-transit-outcome *fn-t-served-conn*
                                             *fn-t-served-transit-sub*
                                             *fn-t-served-transit-want* :durable))))
        '(50 51 53 32)))

; -----------------------------------------------------------------------------
; Teeth for the fourth POST outcome, on the served path
;
; The miss this lane exists for emitted NOTHING.  It cannot any more: a
; connection whose session is at the wrong level earns a 403 through
; fn-served-post-outcome, distinct from 240 and from both 441s, and the
; served effect enumeration accepts it.  *fn-t-served-forged* above is a
; connection whose session is a bare POST session -- one wrapper short of a
; served connection, the exact shape of the 2026-09-20 miss.
(defconst *fn-t-served-403*
  (fn-served-reply-octets
   (fn-served-result-effects
    (fn-served-post-outcome *fn-t-served-forged* :durable))))
(assert-event (equal (take 4 *fn-t-served-403*) '(52 48 51 32)))
(assert-event (consp *fn-t-served-403*))
(assert-event (not (equal *fn-t-served-403* *fn-t-served-240*)))
(assert-event (not (equal *fn-t-served-403* *fn-t-served-441-refused*)))
(assert-event (not (equal *fn-t-served-403* *fn-t-served-441-uncertain*)))
(assert-event (fn-served-effectsp
               (fn-served-result-effects
                (fn-served-post-outcome *fn-t-served-forged* :uncertain))))
