; Expected transcripts for POST, RFC 3977 section 6.3.1, through the function
; the serving host calls: fn-nntp-post-step (host/reader-host.lisp,
; fn-reader-chunk).  Every form is a computation on a specific session, wire
; event, configuration and clock observation.
(in-package "ACL2")
(include-book "../../books/nntp-post")

(defconst *fn-tp-groups* '("fn.letters"))
(defconst *fn-tp-seed* '(77 101 115 115 97 103 101 45 73 68 58 32 60 115 101 101 100 64 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 62 13 10 83 117 98 106 101 99 116 58 32 115 101 101 100 13 10 13 10 83 101 101 100 32 98 111 100 121 13 10))
(defconst *fn-tp-archive*
  (fn-accept-complete
   (fn-accept-prepare (fn-initial-state *fn-tp-groups*) 1
                      "<seed@example.invalid>" *fn-tp-seed* *fn-tp-groups* 841000000)
   0 1 :durable))
(defconst *fn-tp-agent* '(102 110 46 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100))
(defconst *fn-tp-cfg*
  (fn-inj-make-config t *fn-tp-agent* (list '(102 110 46 108 101 116 116 101 114 115)) 32768))
(defconst *fn-tp-cfg-closed*
  (fn-inj-make-config nil *fn-tp-agent* (list '(102 110 46 108 101 116 116 101 114 115)) 32768))
(defconst *fn-tp-obs* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *fn-tp-good* '(70 114 111 109 58 32 112 111 115 116 101 114 64 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 13 10 83 117 98 106 101 99 116 58 32 104 101 108 108 111 13 10 78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10 13 10 72 101 108 108 111 44 32 110 101 119 115 46 13 10))
(defconst *fn-tp-bad* '(83 117 98 106 101 99 116 58 32 104 101 108 108 111 13 10 78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10 13 10 72 101 108 108 111 46 13 10))
(defconst *fn-tp-good-lines* (list '(70 114 111 109 58 32 112 111 115 116 101 114 64 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100) '(83 117 98 106 101 99 116 58 32 104 101 108 108 111) '(78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115) '() '(72 101 108 108 111 44 32 110 101 119 115 46)))
(defconst *fn-tp-bad-lines* (list '(83 117 98 106 101 99 116 58 32 104 101 108 108 111) '(78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115) '() '(72 101 108 108 111 46)))
(assert-event (equal (fn-post-body-octets *fn-tp-good-lines*) *fn-tp-good*))
(assert-event (equal (fn-post-body-octets *fn-tp-bad-lines*) *fn-tp-bad*))
(defconst *fn-tp-post-event* (list :command '(80 79 83 84)))
(defconst *fn-tp-post-arg-event* (list :command '(80 79 83 84 32 120)))
(defconst *fn-tp-quit-event* (list :command '(81 85 73 84)))

(defconst *fn-tp-s0* (fn-post-open-session *fn-tp-archive*))
(assert-event (fn-post-sessionp *fn-tp-s0*))
(assert-event (not (fn-post-session-awaiting *fn-tp-s0*)))
(assert-event (fn-post-session-consistentp *fn-tp-s0* *fn-tp-archive*))

; POST with posting configured: 340 and the one framing effect, and the
; session now awaits the article.
(defconst *fn-tp-r1*
  (fn-nntp-post-step *fn-tp-s0* *fn-tp-archive* *fn-tp-cfg* *fn-tp-obs* *fn-tp-obs*
                     *fn-tp-post-event*))
(assert-event
 (equal (fn-post-result-effects *fn-tp-r1*)
        (list (fn-nntp-reply-effect
               (fn-nntp-crlf
                (fn-nntp-string-octets "340 send article to be posted")))
              (fn-nntp-begin-article-effect))))
(assert-event (fn-nntp-effectsp (fn-post-result-effects *fn-tp-r1*)))
(assert-event (equal (fn-post-session-awaiting
                      (fn-post-result-session *fn-tp-r1*))
                     t))
(assert-event (fn-post-session-consistentp
               (fn-post-result-session *fn-tp-r1*) *fn-tp-archive*))
(assert-event (equal (fn-post-result-submission *fn-tp-r1*) nil))

; POST with posting refused by configuration: 440, and no article mode.
(defconst *fn-tp-r440*
  (fn-nntp-post-step *fn-tp-s0* *fn-tp-archive* *fn-tp-cfg-closed* *fn-tp-obs* *fn-tp-obs*
                     *fn-tp-post-event*))
(assert-event
 (equal (fn-post-result-effects *fn-tp-r440*)
        (list (fn-nntp-reply-effect
               (fn-nntp-crlf
                (fn-nntp-string-octets "440 posting not permitted"))))))
(assert-event (not (fn-post-session-awaiting
                    (fn-post-result-session *fn-tp-r440*))))

; POST takes no argument.
(assert-event
 (equal (fn-post-result-effects
         (fn-nntp-post-step *fn-tp-s0* *fn-tp-archive* *fn-tp-cfg* *fn-tp-obs* *fn-tp-obs*
                            *fn-tp-post-arg-event*))
        (list (fn-nntp-reply-effect
               (fn-nntp-crlf (fn-nntp-string-octets "501 syntax error"))))))

; Every command that is not POST is the reader profile, unchanged.
(assert-event
 (equal (fn-post-result-effects
         (fn-nntp-post-step *fn-tp-s0* *fn-tp-archive* *fn-tp-cfg* *fn-tp-obs* *fn-tp-obs*
                            *fn-tp-quit-event*))
        (fn-nntp-result-effects
         (fn-nntp-step (fn-post-session-base *fn-tp-s0*) *fn-tp-archive*
                       (fn-nntp-env *fn-tp-obs* nil
                                    (and (fn-inj-config-allow *fn-tp-cfg*) t))
                       *fn-tp-quit-event*))))

; The terminated body: injected, so a submission and no reply yet.  240 is not
; reachable from this step at all.
(defconst *fn-tp-r2*
  (fn-nntp-post-step (fn-post-result-session *fn-tp-r1*) *fn-tp-archive*
                     *fn-tp-cfg* *fn-tp-obs* *fn-tp-obs* (list :article *fn-tp-good-lines*)))
(assert-event (equal (fn-post-result-effects *fn-tp-r2*) nil))
(assert-event (fn-inj-injectedp (fn-post-result-submission *fn-tp-r2*)))
(assert-event (not (fn-post-session-awaiting
                    (fn-post-result-session *fn-tp-r2*))))
(assert-event (fn-post-session-consistentp
               (fn-post-result-session *fn-tp-r2*) *fn-tp-archive*))
(assert-event (equal (fn-inj-decision-msgid (fn-post-result-submission *fn-tp-r2*))
                     (fn-inj-decision-msgid
                      (fn-inj-decide *fn-tp-good* *fn-tp-cfg* *fn-tp-obs*))))

; A refused body: 441 carrying the injection reason, and nothing submitted.
(defconst *fn-tp-r3*
  (fn-nntp-post-step (fn-post-result-session *fn-tp-r1*) *fn-tp-archive*
                     *fn-tp-cfg* *fn-tp-obs* *fn-tp-obs* (list :article *fn-tp-bad-lines*)))
(assert-event
 (equal (fn-post-result-effects *fn-tp-r3*)
        (list (fn-nntp-reply-effect
               (fn-nntp-crlf
                (fn-nntp-string-octets
                 "441 posting failed; From is required"))))))
(assert-event (equal (fn-post-result-submission *fn-tp-r3*) nil))
(assert-event (fn-nntp-effectsp (fn-post-result-effects *fn-tp-r3*)))

; An unexpected wire event while awaiting the article is a refusal, not a
; silent acceptance.
(assert-event
 (equal (fn-post-result-effects
         (fn-nntp-post-step (fn-post-result-session *fn-tp-r1*) *fn-tp-archive*
                            *fn-tp-cfg* *fn-tp-obs* *fn-tp-obs* (list :reject :too-long)))
        (list (fn-nntp-reply-effect
               (fn-nntp-crlf
                (fn-nntp-string-octets
                 "441 posting failed; the article was not received"))))))

; The three durable observations stay distinct out to the wire.
(assert-event
 (equal (fn-post-result-effects
         (fn-nntp-post-outcome (fn-post-result-session *fn-tp-r2*) :durable))
        (list (fn-nntp-reply-effect
               (fn-nntp-crlf (fn-nntp-string-octets "240 article received OK"))))))
(assert-event
 (equal (fn-post-result-effects
         (fn-nntp-post-outcome (fn-post-result-session *fn-tp-r2*) :refused))
        (list (fn-nntp-reply-effect
               (fn-nntp-crlf
                (fn-nntp-string-octets
                 "441 posting failed; the article was refused"))))))
(assert-event
 (equal (fn-post-result-effects
         (fn-nntp-post-outcome (fn-post-result-session *fn-tp-r2*) :uncertain))
        (list (fn-nntp-reply-effect
               (fn-nntp-crlf
                (fn-nntp-string-octets
                 "441 posting failed; the outcome is uncertain, do not repost"))))))
(assert-event
 (not (equal (fn-post-result-effects
              (fn-nntp-post-outcome (fn-post-result-session *fn-tp-r2*) :refused))
             (fn-post-result-effects
              (fn-nntp-post-outcome (fn-post-result-session *fn-tp-r2*)
                                    :uncertain)))))
(assert-event
 (fn-nntp-effectsp
  (fn-post-result-effects
   (fn-nntp-post-outcome (fn-post-result-session *fn-tp-r2*) :durable))))

; -----------------------------------------------------------------------------
; Teeth for the injection clock
;
; One connection is one session, one pinned archive, one configuration and
; one pinned reader observation.  These four cases exhibit
; fn-post-distinct-injection-clocks-give-distinct-identities and its
; hypothesis on a specific pair of values.

(defconst *fn-tp-obs2* (fn-clock-observation 1000007 843004800007 500 t))
(defconst *fn-tp-good2-lines*
  (list (fn-nntp-string-octets "From: poster@example.invalid")
        (fn-nntp-string-octets "Subject: hello again")
        (fn-nntp-string-octets "Newsgroups: fn.letters")
        nil
        (fn-nntp-string-octets "Hello once more, news.")))
(defconst *fn-tp-r2b*
  (fn-nntp-post-step (fn-post-result-session *fn-tp-r1*) *fn-tp-archive*
                     *fn-tp-cfg* *fn-tp-obs* *fn-tp-obs2*
                     (list :article *fn-tp-good2-lines*)))
(assert-event (fn-inj-injectedp (fn-post-result-submission *fn-tp-r2b*)))

; The keystone's conclusion on this pair: a second post on the connection
; that posted *fn-tp-r2* is a new article, not a duplicate identity.
(assert-event
 (not (equal (fn-inj-decision-msgid (fn-post-result-submission *fn-tp-r2*))
             (fn-inj-decision-msgid (fn-post-result-submission *fn-tp-r2b*)))))

; Without the hypothesis that the injection clocks differ: two DISTINCT
; bodies under ONE injection clock share a generated Message-ID, because the
; generator's inputs are the clock and the configured agent only.  This is
; the defect the seam removes -- one reading pinned per connection made
; every post after the first on it a duplicate of the first.
(assert-event
 (equal (fn-inj-decision-msgid (fn-post-result-submission *fn-tp-r2*))
        (fn-inj-decision-msgid
         (fn-post-result-submission
          (fn-nntp-post-step (fn-post-result-session *fn-tp-r1*)
                             *fn-tp-archive* *fn-tp-cfg* *fn-tp-obs*
                             *fn-tp-obs* (list :article *fn-tp-good2-lines*))))))

; The retry rule the other way (books/injection-invariants.lisp,
; fn-inj-generated-identity-is-the-clock-identity): the same body under the
; same injection clock is the same article, octet for octet.
(assert-event
 (equal (fn-inj-decision-octets (fn-post-result-submission *fn-tp-r2*))
        (fn-inj-decision-octets
         (fn-post-result-submission
          (fn-nntp-post-step (fn-post-result-session *fn-tp-r1*)
                             *fn-tp-archive* *fn-tp-cfg* *fn-tp-obs*
                             *fn-tp-obs* (list :article *fn-tp-good-lines*))))))

; The pinned reader observation does not enter the identity at all: moving
; it and holding the injection clock gives the same identity.
(assert-event
 (equal (fn-inj-decision-msgid (fn-post-result-submission *fn-tp-r2b*))
        (fn-inj-decision-msgid
         (fn-post-result-submission
          (fn-nntp-post-step (fn-post-result-session *fn-tp-r1*)
                             *fn-tp-archive* *fn-tp-cfg* *fn-tp-obs2*
                             *fn-tp-obs2* (list :article *fn-tp-good2-lines*))))))

; -----------------------------------------------------------------------------
; Teeth for the fourth outcome: a malformed session
;
; The served command chain is four records deep (auth over peer over post
; over the reader session) and all three base accessors are `car', so a call
; site that reaches one level short hands this function a well-shaped value
; at the wrong level.  It used to answer that with NO EFFECTS, and on
; 2026-09-20 that is exactly what happened: books/served.lisp reached one
; wrapper short, so a posting client got the 340 offer, sent its article and
; was told nothing at all.  Silence is not accepted, refused or uncertain.
;
; The witnesses are the two ways to miss by one: the READER session, which is
; what a site that walks one level too FAR produces, and a posting session
; wrapped once more, which is the shape a site one level too SHORT hands in
; (the served path handed in an auth session, whose base is a peer session,
; for exactly this reason; peer-inbound is above this book, so the witness
; here is the same miss built from the records this book has).  Both are
; well-shaped records; neither is a posting session; each now earns a 403.

(defconst *fn-tp-too-deep* (fn-nntp-open-session *fn-tp-archive*))
(defconst *fn-tp-too-shallow* (fn-post-make-session *fn-tp-s0* nil))
(defconst *fn-tp-403*
  (list (fn-nntp-reply-effect
         (fn-nntp-crlf
          (fn-nntp-string-octets
           "403 internal fault; the posting session is malformed")))))

; The two witnesses are real records at the wrong level, not junk: this is a
; separating witness by more than the weakest clause of fn-post-sessionp.
(assert-event (fn-nntp-sessionp *fn-tp-too-deep*))
(assert-event (not (fn-post-sessionp *fn-tp-too-deep*)))
(assert-event (fn-post-session-shapep *fn-tp-too-shallow*))
(assert-event (equal (fn-post-session-base *fn-tp-too-shallow*) *fn-tp-s0*))
(assert-event (fn-post-sessionp *fn-tp-s0*))
(assert-event (not (fn-post-sessionp *fn-tp-too-shallow*)))

; Neither is answered with silence any more, and both are answered the same
; way whatever the store reported: the completion is not the defect.
(assert-event
 (equal (fn-post-result-effects (fn-nntp-post-outcome *fn-tp-too-deep* :durable))
        *fn-tp-403*))
(assert-event
 (equal (fn-post-result-effects (fn-nntp-post-outcome *fn-tp-too-shallow* :refused))
        *fn-tp-403*))
(assert-event
 (equal (fn-post-result-effects (fn-nntp-post-outcome *fn-tp-too-deep* :uncertain))
        (fn-post-result-effects (fn-nntp-post-outcome *fn-tp-too-shallow* :durable))))
(assert-event (fn-nntp-effectsp *fn-tp-403*))

; The separation fn-post-outcome-separates-a-malformed-session states, on
; these witnesses: the fourth outcome is not any of the three.
(assert-event
 (not (equal (fn-post-result-effects (fn-nntp-post-outcome *fn-tp-too-deep* :durable))
             (fn-post-result-effects
              (fn-nntp-post-outcome (fn-post-result-session *fn-tp-r2*) :durable)))))
(assert-event
 (not (equal (fn-post-result-effects (fn-nntp-post-outcome *fn-tp-too-deep* :refused))
             (fn-post-result-effects
              (fn-nntp-post-outcome (fn-post-result-session *fn-tp-r2*) :refused)))))
(assert-event
 (not (equal (fn-post-result-effects (fn-nntp-post-outcome *fn-tp-too-deep* :uncertain))
             (fn-post-result-effects
              (fn-nntp-post-outcome (fn-post-result-session *fn-tp-r2*) :uncertain)))))

; The hypothesis of fn-post-outcome-240-only-for-a-durable-observation is
; necessary, and this is the violating value: without fn-post-sessionp the
; three completions are NOT told apart, because the fourth outcome ignores
; the completion.
(assert-event
 (equal (fn-post-result-effects (fn-nntp-post-outcome *fn-tp-too-deep* :refused))
        (fn-post-result-effects (fn-nntp-post-outcome *fn-tp-too-deep* :durable))))

; -----------------------------------------------------------------------------
; Teeth for fn-post-without-a-clock-refuses-with-the-clock-line (D10-a)
;
; The owner has no clock exactly when its host reported a reading that
; contradicted the one it held (books/owner.lisp fn-own-observe), so what
; fn-own-read supplies as the injection reading is not an observation.  The
; witness is reachable -- the session is the one POST left awaiting above --
; and each case below drops one hypothesis and shows the conclusion fail.

(defconst *fn-tp-clockless*
  (fn-nntp-post-step (fn-post-result-session *fn-tp-r1*) *fn-tp-archive*
                     *fn-tp-cfg* *fn-tp-obs* nil
                     (list :article *fn-tp-good-lines*)))
(assert-event
 (equal (fn-post-result-effects *fn-tp-clockless*)
        (list (fn-nntp-reply-effect
               (fn-nntp-crlf
                (fn-nntp-string-octets
                 "441 posting failed; this server has no usable clock reading"))))))
(assert-event (equal (fn-post-result-submission *fn-tp-clockless*) nil))
(assert-event (fn-nntp-effectsp (fn-post-result-effects *fn-tp-clockless*)))
; and it is a DIFFERENT line from every other refusal this step can give,
; which is the whole point: a clock fault is not an article verdict.
(assert-event
 (not (equal (fn-post-result-effects *fn-tp-clockless*)
             (fn-post-result-effects *fn-tp-r3*))))
(assert-event
 (not (equal (fn-post-result-effects *fn-tp-clockless*)
             (fn-post-result-effects
              (fn-nntp-post-outcome (fn-post-result-session *fn-tp-r2*) :refused)))))
(assert-event
 (not (equal (fn-post-result-effects *fn-tp-clockless*)
             (fn-post-result-effects
              (fn-nntp-post-outcome (fn-post-result-session *fn-tp-r2*) :uncertain)))))

; Hypothesis (not (fn-clock-observationp injection)) dropped: with a reading
; the article is injected and there IS a submission.
(assert-event (fn-inj-injectedp (fn-post-result-submission *fn-tp-r2*)))
(assert-event
 (not (equal (fn-post-result-effects *fn-tp-r2*)
             (fn-post-result-effects *fn-tp-clockless*))))

; Hypothesis (fn-post-session-awaiting ps) dropped: the same event on a
; session that is not awaiting an article is not an injection at all.
(assert-event (not (fn-post-session-awaiting *fn-tp-s0*)))
(assert-event
 (not (equal (fn-post-result-effects
              (fn-nntp-post-step *fn-tp-s0* *fn-tp-archive* *fn-tp-cfg*
                                 *fn-tp-obs* nil (list :article *fn-tp-good-lines*)))
             (fn-post-result-effects *fn-tp-clockless*))))

; Hypothesis (fn-post-sessionp ps) dropped: one wrapper too shallow answers
; with no effects at all, which is neither refusal.
(assert-event
 (equal (fn-post-result-effects
         (fn-nntp-post-step *fn-tp-too-shallow* *fn-tp-archive* *fn-tp-cfg*
                            *fn-tp-obs* nil (list :article *fn-tp-good-lines*)))
        nil))

; Hypothesis (fn-inj-config-allow config) dropped: a connection whose pinned
; configuration forbids posting is refused for THAT reason, with no clock.
(assert-event
 (equal (fn-post-result-effects
         (fn-nntp-post-step (fn-post-result-session *fn-tp-r1*) *fn-tp-archive*
                            *fn-tp-cfg-closed* *fn-tp-obs* nil
                            (list :article *fn-tp-good-lines*)))
        (list (fn-nntp-reply-effect
               (fn-nntp-crlf
                (fn-nntp-string-octets
                 "441 posting failed; posting is not permitted"))))))

; Hypothesis (fn-inj-configp config) dropped: a value that is not a
; configuration is refused before the clock is ever read, with the bare line.
(assert-event (fn-inj-configp *fn-tp-cfg*))
(assert-event (not (fn-inj-configp 7)))
(assert-event
 (equal (fn-post-result-effects
         (fn-nntp-post-step (fn-post-result-session *fn-tp-r1*) *fn-tp-archive*
                            7 *fn-tp-obs* nil (list :article *fn-tp-good-lines*)))
        (list (fn-nntp-reply-effect
               (fn-nntp-crlf (fn-nntp-string-octets "441 posting failed"))))))
