; fn: one admission decision, three wire forms (PRF-207, NNT-042).
;
; A peer offers an article with IHAVE (RFC 3977 section 6.3.2) or streams it
; with CHECK and TAKETHIS after MODE STREAM (RFC 4644 sections 2.3 to 2.5).
; fn answers all three from the same two ACL2 decisions of
; books/peer-inbound.lisp: `fn-peer-decide-offer' before the article (IHAVE's
; first reply, CHECK's only reply) and `fn-peer-decide-transfer' after it
; (IHAVE's second reply, TAKETHIS's only reply; the owner calls it with no
; command formal at all, books/owner.lisp `fn-own-bp-transit-submit-result'
; and the host's `fn-owner-transit-decide').  This book states that the codes
; a peer READS OFF THE SOCKET are the images of one decision under the two
; RFC tables:
;
;   offer     IHAVE 335 / 435 / 436      CHECK    238 / 438 / 431
;   transfer  IHAVE 235 / 437 / 436      TAKETHIS 239 / 439 / 436
;
; 436 after TAKETHIS is fn's local policy (RFC 4644 section 2.5 names 400;
; the reason, innfeed's retry classes, is at `fn-peer-transit-code').  So a
; duplicate is 435 and 438, a deferral 436 and 431, a refusal 437 and 439,
; and no article is admitted under one form that the other would refuse.
;
; The subjects are the functions the host calls.  `fn-peer-command' is run
; for every transit command line: the served path executes
; `fn-pgc-peer-command' (books/peer-guard-carried.lisp, from
; `fn-pgc-peer-arm', itself `fn-peer-step-pinned' by
; `fn-pgc-peer-arm-is-peer-step-pinned'), which equals `fn-peer-command' by
; `fn-pgc-peer-command-is-peer-command'.  `fn-peer-transit-outcome-effects'
; renders the reply after the durable attempt: books/served.lisp
; `fn-served-transit-outcome' (`fn-served-transit-outcome-effects-by-definition'),
; called by books/owner.lisp `fn-own-transit-outcome', which the host runs
; once per transit completion (host/owner-host.lisp).
;
; `fn-peer-wire-code' is the reading a peer makes of fn's reply: the three
; decimal digits that begin the first reply line (RFC 3977 section 3.2).
(in-package "ACL2")
(include-book "peer-inbound")

(defun fn-peer-wire-code (effects)
  (declare (xargs :guard t))
  (let ((e (if (consp effects) (car effects) nil)))
    (if (and (consp e) (equal (car e) :reply) (consp (cdr e)))
        (let ((o (cadr e)))
          (if (and (consp o) (consp (cdr o)) (consp (cddr o)))
              (+ (* 100 (- (nfix (car o)) 48))
                 (* 10 (- (nfix (cadr o)) 48))
                 (- (nfix (caddr o)) 48))
            nil))
      nil)))

; RFC 4644 section 2.4's CHECK codes for RFC 3977 section 6.3.2's IHAVE
; offer codes; every other code (501) is its own image.
(defun fn-peer-check-form (code)
  (declare (xargs :guard t))
  (cond ((equal code 335) 238)
        ((equal code 435) 438)
        ((equal code 436) 431)
        (t code)))

; RFC 4644 section 2.5's TAKETHIS codes for IHAVE's transfer codes; 436 (the
; retry class, local policy on TAKETHIS) is its own image.
(defun fn-peer-takethis-form (code)
  (declare (xargs :guard t))
  (cond ((equal code 235) 239)
        ((equal code 437) 439)
        (t code)))

(local (defthm fn-ptf-coerce-string-append
  (implies (and (stringp x) (stringp y))
           (equal (coerce (string-append x y) 'list)
                  (append (coerce x 'list) (coerce y 'list))))))

(local (defthm fn-ptf-string-octets-aux-append
  (equal (fn-nntp-string-octets-aux (append a b))
         (append (fn-nntp-string-octets-aux a) (fn-nntp-string-octets-aux b)))
  :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux)))))

(local (defthm fn-ptf-string-octets-of-string-append
  (implies (and (stringp x) (stringp y))
           (equal (fn-nntp-string-octets (string-append x y))
                  (append (fn-nntp-string-octets x) (fn-nntp-string-octets y))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-string-octets) (string-append))))))

(local (defthm fn-ptf-check-is-not-ihave
  (implies (fn-nntp-keywordp k "CHECK")
           (not (fn-nntp-keywordp k "IHAVE")))
  :hints (("Goal" :in-theory (enable fn-nntp-keywordp)))))

; -----------------------------------------------------------------------------
; KEYSTONE 1: the offer.  For one connection state and one Message-ID, the
; code IHAVE answers and the code CHECK answers are the IHAVE and CHECK images
; of the same `fn-peer-decide-offer' decision (the node, configuration, peer
; and outstanding-offer count the session carries), so CHECK's code is
; exactly the streaming form of IHAVE's.  The hypothesis is the one that
; makes both arms reach the decision: a well-formed Message-ID argument
; (otherwise both answer 501, which is its own image).
(defthm fn-peer-check-and-ihave-answer-one-offer-decision
  (implies (and (fn-nntp-keywordp ki "IHAVE")
                (fn-nntp-keywordp kc "CHECK")
                (fn-peer-msgid-argp args))
           (let ((d (fn-peer-decide-offer (fn-peer-session-node ps)
                                          (fn-peer-session-cfg ps)
                                          (fn-peer-session-peer ps)
                                          ps (car args) nil
                                          (fn-peer-session-inflight ps)))
                 (ihave (fn-peer-wire-code
                         (fn-post-result-effects (fn-peer-command ps ki args))))
                 (check (fn-peer-wire-code
                         (fn-post-result-effects (fn-peer-command ps kc args)))))
             (and (equal ihave (fn-peer-offer-code :ihave d))
                  (equal check (fn-peer-offer-code :check d))
                  (equal check (fn-peer-check-form ihave)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-peer-command fn-peer-ihave-offer-line
                                   fn-peer-check-code fn-peer-offer-code
                                   fn-peer-single fn-nntp-single
                                   fn-nntp-make-result fn-nntp-result-effects
                                   fn-nntp-reply-effect fn-nntp-crlf
                                   fn-peer-echo-reply fn-nntp-string-octets
                                   fn-nntp-string-octets-aux)
                                  (fn-peer-decide-offer fn-peer-msgid-argp
                                   fn-peer-reason-text string-append
                                   fn-nntp-keywordp)))))

; -----------------------------------------------------------------------------
; KEYSTONE 2: the transfer.  For one decision D (the owner's
; `fn-peer-decide-transfer' on the article, with no command formal) and one
; durable COMPLETION, the reply rendered for a TAKETHIS submission and for an
; IHAVE submission of the same article carry the IHAVE and TAKETHIS images
; of that verdict, the TAKETHIS code is exactly the streaming form of the
; IHAVE code, and one closes the connection exactly when the other does (an
; uncertain outcome).  No hypothesis: every decision and every completion.
(defthm fn-peer-takethis-and-ihave-answer-one-transfer-verdict
  (let ((ihave (fn-peer-transit-outcome-effects
                ps (fn-peer-make-submission peer :ihave msgid octets) d completion))
        (takethis (fn-peer-transit-outcome-effects
                   ps (fn-peer-make-submission peer :takethis msgid octets) d completion)))
    (and (equal (fn-peer-wire-code ihave)
                (fn-peer-transit-code :ihave d completion))
         (equal (fn-peer-wire-code takethis)
                (fn-peer-transit-code :takethis d completion))
         (equal (fn-peer-wire-code takethis)
                (fn-peer-takethis-form (fn-peer-wire-code ihave)))
         (iff (member-equal (fn-nntp-close-effect) takethis)
              (member-equal (fn-nntp-close-effect) ihave))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-peer-transit-outcome-effects
                                   fn-peer-transit-code
                                   fn-peer-transit-refusal-line
                                   fn-peer-single fn-nntp-single
                                   fn-nntp-make-result fn-nntp-result-effects
                                   fn-nntp-reply-effect fn-nntp-crlf
                                   fn-peer-echo-reply fn-nntp-string-octets
                                   fn-nntp-string-octets-aux)
                                  (fn-peer-reason-text string-append
                                   fn-post-store-refusal-text)))))

; The article the transfer arm hands the owner names the form and nothing
; else of it: for a session awaiting (KIND MSGID), the article event yields
; the submission (peer KIND MSGID octets), so an IHAVE transfer and a
; TAKETHIS of the same article reach the owner's one decision with the same
; peer, Message-ID and octets.  -unfolds: the branch is the definition.
(defthm fn-peer-transfer-submission-differs-only-in-form-unfolds
  (implies (and (fn-peer-sessionp ps)
                (fn-peer-session-peer ps)
                (equal (fn-nntp-session-openp (fn-peer-reader-session ps)) t)
                (equal (fn-peer-session-transfer ps) (list kind msgid)))
           (equal (fn-post-result-submission
                   (fn-peer-step-pinned ps archive index verdicts config observation
                                        injection (list :article lines)))
                  (fn-peer-make-submission (fn-peer-session-peer ps) kind msgid
                                           (fn-post-body-octets lines))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-peer-step-pinned fn-peer-step fn-peer-with-transfer)
                                  (fn-peer-sessionp fn-peer-make-submission
                                   fn-post-body-octets)))))

; -----------------------------------------------------------------------------
; KEYSTONE 3: the pipeline is bounded per connection (D27: work, not data).
; A streaming peer may send many CHECKs before their TAKETHISes (RFC 4644
; section 2.4.1).  Each command line is one served event, and no event
; raises the connection's count of outstanding 238s above the larger of what
; it was and the peer record's inbound max-inflight: a CHECK past the bound
; is 431 (retry later), never an unbounded promise.  By induction over the
; events of a connection (which opens at 0, `fn-peer-open-session') the
; count never exceeds max-inflight.  Subject: `fn-peer-step-pinned', the arm
; `fn-pgc-peer-arm' equals.
(defthm fn-peer-command-keeps-outstanding-offers-within-the-peer-bound
  (<= (nfix (fn-peer-session-inflight
             (fn-post-result-session (fn-peer-command ps kc args))))
      (max (nfix (fn-peer-session-inflight ps))
           (nfix (fn-cfg-peer-inbound-max-inflight
                  (fn-cfg-peer-find (fn-peer-session-peer ps)
                                    (fn-cfg-peers
                                     (fn-cfg-value (fn-peer-session-cfg ps))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-peer-command fn-peer-decide-offer
                                   fn-peer-with-transfer)
                                  (fn-nntp-keywordp fn-peer-msgid-argp
                                   fn-peer-echo-reply fn-peer-single
                                   fn-peer-history-hasp fn-peer-stagedp
                                   fn-retain-admissiblep fn-af-message-idp
                                   fn-record-octets-string fn-peer-evidence
                                   fn-cfg-peer-find fn-cfg-peer-inbound
                                   fn-cfg-peer-inbound-max-inflight)))))

(local (defthm fn-peer-step-keeps-outstanding-offers-within-the-peer-bound
  (<= (nfix (fn-peer-session-inflight
             (fn-post-result-session
              (fn-peer-step ps archive config observation injection wire-event))))
      (max (nfix (fn-peer-session-inflight ps))
           (nfix (fn-cfg-peer-inbound-max-inflight
                  (fn-cfg-peer-find (fn-peer-session-peer ps)
                                    (fn-cfg-peers
                                     (fn-cfg-value (fn-peer-session-cfg ps))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-peer-step fn-peer-delegate fn-peer-with-base
                                   fn-peer-with-transfer)
                                  (fn-peer-command fn-nntp-post-step
                                   fn-peer-sessionp fn-nntp-tokenize
                                   fn-nntp-command-inputp fn-peer-single
                                   fn-peer-make-submission fn-post-body-octets))
           :use ((:instance fn-peer-command-keeps-outstanding-offers-within-the-peer-bound
                            (kc (car (fn-nntp-tokenize (car (cdr wire-event)))))
                            (args (cdr (fn-nntp-tokenize (car (cdr wire-event)))))))))))

(defthm fn-peer-step-pinned-keeps-outstanding-offers-within-the-peer-bound
  (<= (nfix (fn-peer-session-inflight
             (fn-post-result-session
              (fn-peer-step-pinned ps archive index verdicts config observation
                                   injection wire-event))))
      (max (nfix (fn-peer-session-inflight ps))
           (nfix (fn-cfg-peer-inbound-max-inflight
                  (fn-cfg-peer-find (fn-peer-session-peer ps)
                                    (fn-cfg-peers
                                     (fn-cfg-value (fn-peer-session-cfg ps))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-peer-step-pinned fn-peer-delegate-pinned
                                   fn-peer-with-base)
                                  (fn-peer-command fn-peer-step fn-nntp-post-step-pinned
                                   fn-peer-sessionp fn-nntp-tokenize
                                   fn-nntp-command-inputp))
           :use ((:instance fn-peer-command-keeps-outstanding-offers-within-the-peer-bound
                            (kc (car (fn-nntp-tokenize (car (cdr wire-event)))))
                            (args (cdr (fn-nntp-tokenize (car (cdr wire-event))))))
                 (:instance fn-peer-step-keeps-outstanding-offers-within-the-peer-bound)))))
