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
                      "<seed@example.invalid>" *fn-tp-seed* *fn-tp-groups*)
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
  (fn-nntp-post-step *fn-tp-s0* *fn-tp-archive* *fn-tp-cfg* *fn-tp-obs*
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
  (fn-nntp-post-step *fn-tp-s0* *fn-tp-archive* *fn-tp-cfg-closed* *fn-tp-obs*
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
         (fn-nntp-post-step *fn-tp-s0* *fn-tp-archive* *fn-tp-cfg* *fn-tp-obs*
                            *fn-tp-post-arg-event*))
        (list (fn-nntp-reply-effect
               (fn-nntp-crlf (fn-nntp-string-octets "501 syntax error"))))))

; Every command that is not POST is the reader profile, unchanged.
(assert-event
 (equal (fn-post-result-effects
         (fn-nntp-post-step *fn-tp-s0* *fn-tp-archive* *fn-tp-cfg* *fn-tp-obs*
                            *fn-tp-quit-event*))
        (fn-nntp-result-effects
         (fn-nntp-step (fn-post-session-base *fn-tp-s0*) *fn-tp-archive*
                       *fn-tp-quit-event*))))

; The terminated body: injected, so a submission and no reply yet.  240 is not
; reachable from this step at all.
(defconst *fn-tp-r2*
  (fn-nntp-post-step (fn-post-result-session *fn-tp-r1*) *fn-tp-archive*
                     *fn-tp-cfg* *fn-tp-obs* (list :article *fn-tp-good-lines*)))
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
                     *fn-tp-cfg* *fn-tp-obs* (list :article *fn-tp-bad-lines*)))
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
                            *fn-tp-cfg* *fn-tp-obs* (list :reject :too-long)))
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
