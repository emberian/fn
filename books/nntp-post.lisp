; fn: POST (RFC 3977 section 6.3.1) as one composed transition.
;
; books/nntp.lisp answers a POST command line with 340 and one
; :begin-article effect.  That is deliberately all it does: the dispatcher
; has no configuration argument and no clock, so it cannot decide whether
; this server accepts postings, what the supplied octets become, or whether
; the result is 240 or 441.  This book is the function the serving host
; calls, `fn-nntp-post-step`, and it decides all three.  It is a strict
; wrapper: every command that is not POST is passed to `fn-nntp-step` and its
; result is returned unchanged, so the reader profile keeps exactly the
; behaviour its own keystones describe.
;
;   command "POST", posting allowed      340 and :begin-article; awaiting
;   command "POST", posting disallowed   440, not awaiting
;   awaiting, (:article body)            injection; a refusal is 441 with its
;                                        reason, an acceptance emits a
;                                        submission and no reply yet
;   awaiting, anything else              441, not awaiting
;
; Two clock readings, and they are not the same reading.  `observation` is
; the one the connection pinned when it was accepted: it is the reader
; environment (DATE, NEWGROUPS) and stays fixed for the life of the
; connection, so a reader's view of the server's calendar does not move under
; it.  `injection` is the reading the host supplied with THIS event, and it
; is the only one fn-inj-decide sees, because RFC 5537 section 3.4 makes
; Injection-Date the time of injection and books/injection.lisp derives a
; generated Message-ID from that same reading.  One reading per connection
; would make every submission after the first on a connection a retry of the
; first (same clock, same generated identity), which is why these are two
; arguments.
;
; A submission is not an acknowledgement.  `fn-nntp-post-step` never answers
; 240: the host must carry the submitted octets through the same durable
; acceptance path the command-line `post` uses (tools/run_store.py, through
; fn-node-prepare and fn-node-complete) and then call `fn-nntp-post-outcome`
; with what it observed.  The three observations stay distinct out to the
; wire: :durable is 240, each Store refusal kind is its own 441 line
; (fn-post-store-refusal-line) and :uncertain is another.

(in-package "ACL2")
(include-book "nntp-effects")
(include-book "injection")

(local (in-theory (enable fn-nntp-syntax-vocabulary
                          fn-nntp-session-vocabulary
                          fn-nntp-projection-vocabulary
                          fn-nntp-responses-vocabulary
                          fn-nntp-vocabulary)))
; books/injection.lisp withdraws its total list primitives at export; the two
; record blocks below are stated over them, so they are open here.
(local (in-theory (enable fn-inj-nth fn-inj-car fn-inj-cdr)))

; -----------------------------------------------------------------------------
; The session, extended opaquely
;
; The reader session record is untouched.  A posting session is the reader
; session plus one carried bit: whether a 340 has been issued and the wire is
; therefore in article mode.  Nothing below opens either record.

(defun fn-post-session-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 2)))
(defun fn-post-session-base (x)
  (declare (xargs :guard t))
  (fn-inj-nth 0 x))
(defun fn-post-session-awaiting (x)
  (declare (xargs :guard t))
  (fn-inj-nth 1 x))
(defun fn-post-make-session (base awaiting)
  (declare (xargs :guard t))
  (list base awaiting))

(defthm fn-post-session-shapep-of-fn-post-make-session
  (fn-post-session-shapep (fn-post-make-session base awaiting)))
(defthm fn-post-session-base-of-fn-post-make-session
  (equal (fn-post-session-base (fn-post-make-session base awaiting)) base))
(defthm fn-post-session-awaiting-of-fn-post-make-session
  (equal (fn-post-session-awaiting (fn-post-make-session base awaiting))
         awaiting))

(in-theory (disable (:d fn-post-session-shapep) (:d fn-post-make-session)
                    (:d fn-post-session-base) (:d fn-post-session-awaiting)))

(defun fn-post-sessionp (x)
  (declare (xargs :guard t))
  (and (fn-post-session-shapep x)
       (fn-nntp-sessionp (fn-post-session-base x))
       (booleanp (fn-post-session-awaiting x))))

(defun fn-post-open-session (archive)
  (declare (xargs :guard t))
  (fn-post-make-session (fn-nntp-open-session archive) nil))

; A proof-side relation only: books/nntp-invariants.lisp leaves
; fn-nntp-session-consistentp without guards because no served path runs it.
(defun fn-post-session-consistentp (x archive)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-post-sessionp x)
       (fn-nntp-session-consistentp (fn-post-session-base x) archive)))

; -----------------------------------------------------------------------------
; The result record

(defun fn-post-result-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 3)))
(defun fn-post-result-session (x)
  (declare (xargs :guard t))
  (fn-inj-nth 0 x))
(defun fn-post-result-effects (x)
  (declare (xargs :guard t))
  (fn-inj-nth 1 x))
(defun fn-post-result-submission (x)
  (declare (xargs :guard t))
  (fn-inj-nth 2 x))
(defun fn-post-make-result (session effects submission)
  (declare (xargs :guard t))
  (list session effects submission))

(defthm fn-post-result-shapep-of-fn-post-make-result
  (fn-post-result-shapep (fn-post-make-result session effects submission)))
(defthm fn-post-result-session-of-fn-post-make-result
  (equal (fn-post-result-session
          (fn-post-make-result session effects submission))
         session))
(defthm fn-post-result-effects-of-fn-post-make-result
  (equal (fn-post-result-effects
          (fn-post-make-result session effects submission))
         effects))
(defthm fn-post-result-submission-of-fn-post-make-result
  (equal (fn-post-result-submission
          (fn-post-make-result session effects submission))
         submission))

(in-theory (disable (:d fn-post-result-shapep) (:d fn-post-make-result)
                    (:d fn-post-result-session) (:d fn-post-result-effects)
                    (:d fn-post-result-submission)))

; -----------------------------------------------------------------------------
; Reading the dispatcher's offer, and the refusal lines
;
; The marker is read structurally.  Nothing here inspects reply text: the
; 340 octets are the dispatcher's and are passed through unchanged.

(defun fn-post-offeredp (effects)
  (declare (xargs :guard t))
  (if (consp effects)
      (or (equal (car effects) (fn-nntp-begin-article-effect))
          (fn-post-offeredp (cdr effects)))
    nil))

; One 441 line per injection reason.  RFC 5537 section 3.5 asks an injecting
; agent to tell the posting agent why; these are that text, and each is a
; distinct constant so a client can distinguish them.
(defun fn-post-refusal-line (reason)
  (declare (xargs :guard t))
  (cond
   ((equal reason :unparsable) "441 posting failed; the article is not valid syntax")
   ((equal reason :injection-info) "441 posting failed; Injection-Info must not be supplied")
   ((equal reason :xref) "441 posting failed; Xref must not be supplied")
   ((equal reason :injection-date-present) "441 posting failed; Injection-Date must not be supplied")
   ((equal reason :path-present) "441 posting failed; Path must not be supplied")
   ((equal reason :newsgroups-missing) "441 posting failed; Newsgroups is required")
   ((equal reason :newsgroups-duplicate) "441 posting failed; Newsgroups appears more than once")
   ((equal reason :newsgroups-invalid) "441 posting failed; Newsgroups is not a valid newsgroup list")
   ((equal reason :message-id-duplicate) "441 posting failed; Message-ID appears more than once")
   ((equal reason :message-id-invalid) "441 posting failed; Message-ID is not a valid identifier")
   ((equal reason :from-missing) "441 posting failed; From is required")
   ((equal reason :from-duplicate) "441 posting failed; From appears more than once")
   ((equal reason :from-invalid) "441 posting failed; From is not a valid mailbox list")
   ((equal reason :subject-missing) "441 posting failed; Subject is required")
   ((equal reason :subject-duplicate) "441 posting failed; Subject appears more than once")
   ((equal reason :date-duplicate) "441 posting failed; Date appears more than once")
   ((equal reason :no-groups) "441 posting failed; no newsgroup was named")
   ((equal reason :unknown-group) "441 posting failed; a named newsgroup is not carried here")
   ((equal reason :oversize) "441 posting failed; the article exceeds the configured size")
   ((equal reason :clock-unusable) "441 posting failed; this server has no usable clock reading")
   ((equal reason :clock-out-of-range) "441 posting failed; this server clock is outside the modelled range")
   ((equal reason :posting-disallowed) "441 posting failed; posting is not permitted")
   (t "441 posting failed")))

; books/wire.lisp delivers an (:article lines) event, where each line is its
; octets without CRLF and dot-stuffing has already been undone.  Reassembling
; the exact source the posting agent sent is a decision about octets, so it is
; made here and not in the host.
(defun fn-post-body-octets (lines)
  (declare (xargs :guard t))
  (if (consp lines)
      (fn-inj-append (car lines)
                     (fn-inj-append '(13 10) (fn-post-body-octets (cdr lines))))
    nil))

(defun fn-post-single (ps text)
  (declare (xargs :guard t))
  (fn-nntp-result-effects (fn-nntp-single (fn-post-session-base ps) text)))

; -----------------------------------------------------------------------------
; The composed step
;
; This is the function the serving host calls, once per wire event, at
; host/reader-host.lisp `fn-reader-chunk`.

(defun fn-nntp-post-step (ps archive config observation injection wire-event)
  (declare (xargs :guard t))
  (if (not (fn-post-sessionp ps))
      (fn-post-make-result ps nil nil)
    (if (fn-post-session-awaiting ps)
        (if (and (consp wire-event)
                 (equal (car wire-event) :article)
                 (consp (cdr wire-event))
                 (null (cdr (cdr wire-event))))
            (let ((decision (fn-inj-decide
                             (fn-post-body-octets (car (cdr wire-event)))
                             config injection)))
              (if (fn-inj-injectedp decision)
                  ; No reply yet.  The host owes a durable acceptance attempt
                  ; and then fn-nntp-post-outcome.
                  (fn-post-make-result
                   (fn-post-make-session (fn-post-session-base ps) nil)
                   nil decision)
                (fn-post-make-result
                 (fn-post-make-session (fn-post-session-base ps) nil)
                 (fn-post-single
                  ps (fn-post-refusal-line (fn-inj-decision-reason decision)))
                 nil)))
          (fn-post-make-result
           (fn-post-make-session (fn-post-session-base ps) nil)
           (fn-post-single ps "441 posting failed; the article was not received")
           nil))
      ; The reader environment is built here, where the dispatcher is called:
      ; the connection's pinned clock observation and the persisted
      ; group-creation facts.  The served tree persists no creation facts yet
      ; (planning/lanes/HANDOFF-w3-reader-profile.md, proposal 3), so the fact
      ; list is empty and NEWGROUPS reports no group rather than an invented
      ; creation date.
      (let ((r (fn-nntp-step (fn-post-session-base ps) archive
                             (fn-nntp-env observation nil (and (fn-inj-config-allow config) t)) wire-event)))
        (if (fn-post-offeredp (fn-nntp-result-effects r))
            (if (fn-inj-config-allow config)
                (fn-post-make-result
                 (fn-post-make-session (fn-nntp-result-session r) t)
                 (fn-nntp-result-effects r) nil)
              (fn-post-make-result
               (fn-post-make-session (fn-nntp-result-session r) nil)
               (fn-post-single ps "440 posting not permitted")
               nil))
          (fn-post-make-result
           (fn-post-make-session (fn-nntp-result-session r) nil)
           (fn-nntp-result-effects r) nil))))))

; The host's durable observation, reported distinctly.  240 is reachable from
; :durable and from nothing else.
;
; A session that is not an fn-post-sessionp is a FOURTH outcome and is
; answered as one.  It used to be answered with no effects at all, and that
; is how the served path came to emit neither 240 nor 441 for a whole day
; (books/served.lisp reached one wrapper short of the POST session; a client
; got the 340 offer, sent its article and was never told whether it was
; stored).  "No effects" is not accepted, not refused and not uncertain: it
; is silence that reads as success, which is exactly what AGENTS.md's three
; outcomes rule forbids.  403 is RFC 3977 section 3.2.1's internal fault, it
; is distinct from 240 and from both 441s
; (fn-post-outcome-separates-a-malformed-session below), and it makes the
; next missed wrapper a visible failure on the wire and in the test book
; instead of a silent one.
;
; A Store refusal names the kind the Store decided (P2: "441 refused names
; its reason").  The owner renders the word it was handed only when the
; completion is a refusal (books/owner.lisp fn-own-outcome-rendering), so a
; kind here is never reached after a consumed completion.  :duplicate and
; :conflict are fn-pb-existing-action's two answers (books/poster-bytes.lisp,
; the decision the host calls since D25);
; :malformed is fn-owner-prepare's :invalid; :unaffordable is a refusal of
; the persisted profile (fn-store-publication-admissibility) or of the
; transaction capacity; :storage-failed is a Store write that failed before
; publication and whose reservation ACL2 consumed as a known abort, so
; nothing was stored.  :refused remains the kind for a refusal the Store did
; not name.  RFC 3977 section 6.3.1 allows 441 for all of them; the
; distinct text is the stronger fn guarantee.  The exact words are a local
; policy choice pending ember's decision on the wire vocabulary.
(defun fn-post-store-refusalp (completion)
  (declare (xargs :guard t))
  (and (member-equal completion
                     '(:refused :duplicate :conflict :malformed :unaffordable
                       :storage-failed
                       ;; A signed POST refused at its FN-Authorship carrier
                       ;; (books/peer-authored-accept.lisp fn-pa-served-word):
                       ;; the plan's reason, or the signature observation.
                       :article :carrier :carrier-shape :local-enrollment
                       :signature))
       t))

(defun fn-post-store-refusal-line (kind)
  (declare (xargs :guard t))
  (cond
   ((equal kind :duplicate)
    "441 posting failed; this article is already stored here")
   ((equal kind :conflict)
    "441 posting failed; a different article with this Message-ID is stored here")
   ((equal kind :malformed)
    "441 posting failed; the store refused the article as malformed")
   ((equal kind :unaffordable)
    "441 posting failed; the store has no capacity for this article")
   ((equal kind :storage-failed)
    "441 posting failed; the store could not write the article, nothing was stored")
   ((equal kind :article)
    "441 posting failed; the article carrying FN-Authorship does not parse")
   ((equal kind :carrier)
    "441 posting failed; the FN-Authorship carrier is malformed")
   ((equal kind :carrier-shape)
    "441 posting failed; the FN-Authorship carrier has the wrong shape")
   ((equal kind :local-enrollment)
    "441 posting failed; the signer has no current enrollment here (local-enrollment)")
   ((equal kind :signature)
    "441 posting failed; the author signature does not verify")
   (t "441 posting failed; the article was refused")))

(defconst *fn-post-malformed-session-line*
  "403 internal fault; the posting session is malformed")

(defun fn-nntp-post-outcome (ps completion)
  (declare (xargs :guard t))
  (if (not (fn-post-sessionp ps))
      (fn-post-make-result ps (fn-post-single ps *fn-post-malformed-session-line*)
                           nil)
    (fn-post-make-result
     ps
     (fn-post-single
      ps
      (cond ((equal completion :durable) "240 article received OK")
            ((equal completion :clock-unusable)
             (fn-post-refusal-line :clock-unusable))
            ((fn-post-store-refusalp completion)
             (fn-post-store-refusal-line completion))
            (t "441 posting failed; the outcome is uncertain, do not repost")))
     nil)))

(verify-guards fn-post-session-shapep)
(verify-guards fn-post-make-session)
(verify-guards fn-post-sessionp)
(verify-guards fn-post-open-session)
(verify-guards fn-post-result-shapep)
(verify-guards fn-post-make-result)
(verify-guards fn-post-offeredp)
(verify-guards fn-post-refusal-line)
(verify-guards fn-post-store-refusalp)
(verify-guards fn-post-store-refusal-line)
(verify-guards fn-post-body-octets)
(verify-guards fn-post-single)
(verify-guards fn-nntp-post-step)
(verify-guards fn-nntp-post-outcome)

; -----------------------------------------------------------------------------
; What the composed step preserves

(defthm fn-post-open-session-is-consistent
  (fn-post-session-consistentp (fn-post-open-session archive) archive)
  :hints (("Goal"
           :use ((:instance fn-nntp-consistent-session-is-session
                            (session (fn-nntp-open-session archive))))
           :in-theory (disable fn-nntp-open-session
                               fn-nntp-consistent-session-is-session
                               fn-nntp-session-consistentp
                               fn-nntp-sessionp))))

(defthm fn-post-step-preserves-consistent-session
  (implies (fn-post-session-consistentp ps archive)
           (fn-post-session-consistentp
            (fn-post-result-session
             (fn-nntp-post-step ps archive config observation injection wire-event))
            archive))
  :hints (("Goal"
           :use ((:instance fn-nntp-step-preserves-consistent-session
                            (session (fn-post-session-base ps))
                            (env (fn-nntp-env observation nil (and (fn-inj-config-allow config) t))))
                 (:instance fn-nntp-consistent-session-is-session
                            (session (fn-nntp-result-session
                                      (fn-nntp-step (fn-post-session-base ps)
                                                    archive
                                                    (fn-nntp-env observation nil (and (fn-inj-config-allow config) t))
                                                    wire-event))))
                 (:instance fn-nntp-consistent-session-is-session
                            (session (fn-post-session-base ps))))
           :in-theory (disable fn-nntp-step-preserves-consistent-session
                               fn-nntp-consistent-session-is-session
                               fn-nntp-step fn-nntp-session-consistentp
                               fn-nntp-sessionp fn-nntp-projectionp
                               fn-inj-decide fn-inj-injectedp
                               fn-inj-decision-reason fn-post-refusal-line
                               fn-post-offeredp))))

(defthm fn-post-step-effects-well-formed
  (implies (fn-post-session-consistentp ps archive)
           (fn-nntp-effectsp
            (fn-post-result-effects
             (fn-nntp-post-step ps archive config observation injection wire-event))))
  :hints (("Goal"
           :use ((:instance fn-nntp-step-effects-well-formed
                            (session (fn-post-session-base ps))
                            (env (fn-nntp-env observation nil (and (fn-inj-config-allow config) t)))))
           :in-theory (e/d (fn-post-single fn-nntp-effectsp
                            fn-post-refusal-line)
                           (fn-nntp-step-effects-well-formed
                            fn-nntp-step fn-nntp-session-consistentp
                            fn-nntp-sessionp fn-nntp-projectionp
                            fn-nntp-replyp fn-inj-decide fn-inj-injectedp
                            fn-inj-decision-reason
                            fn-post-offeredp)))))

(defthm fn-post-outcome-effects-well-formed
  (fn-nntp-effectsp (fn-post-result-effects (fn-nntp-post-outcome ps completion)))
  :hints (("Goal" :in-theory (e/d (fn-post-single fn-nntp-effectsp)
                                  (fn-nntp-replyp fn-post-sessionp
                                   fn-nntp-response-textp
                                   fn-nntp-initial-status-linep)))))

; -----------------------------------------------------------------------------
; What the composed step decides
;
; Each of these is about `fn-nntp-post-step`, the function the host calls at
; host/reader-host.lisp `fn-reader-chunk`.

; These three dispatch on the step's arms and need nothing of the session
; but whether it is one, so `fn-post-sessionp' stays closed as it already
; does in the clock and disallowed-posting theorems below.  Opened, it
; carried the reader session recognizer into the dispatch and the splitter
; took 161, 76 and 60 cases at Goal: 3.4 s, 1.8 s and 1.0 s (t1-seam
; certify-20260923T000250Z-1473169).
(defthm fn-post-submission-is-an-injected-article
  (implies (fn-post-result-submission
            (fn-nntp-post-step ps archive config observation injection wire-event))
           (fn-inj-injectedp
            (fn-post-result-submission
             (fn-nntp-post-step ps archive config observation injection wire-event))))
  :hints (("Goal" :in-theory (disable fn-inj-decide fn-inj-injectedp
                                      fn-nntp-step fn-post-offeredp
                                      fn-post-refusal-line
                                      fn-post-sessionp))))

(defthm fn-post-refused-body-submits-nothing
  (implies (not (fn-inj-injectedp
                 (fn-inj-decide (fn-post-body-octets body) config
                                injection)))
           (equal (fn-post-result-submission
                   (fn-nntp-post-step ps archive config observation injection
                                      (list :article body)))
                  nil))
  :hints (("Goal" :in-theory (disable fn-inj-decide fn-inj-injectedp
                                      fn-nntp-step fn-post-offeredp
                                      fn-post-refusal-line
                                      fn-post-sessionp))))

; A clock fault is not an article verdict (decision D10-a, specs/nntp.md).
; The reading `fn-own-read` supplies with the event is the owner's current
; clock observation, and after a reading that contradicts the one it held
; the owner has NO clock (books/owner.lisp `fn-own-observe`), so what
; arrives here is not an observation at all.  The article is then refused
; with the CLOCK line -- a distinct constant -- and no submission is
; emitted, so a client can tell a server whose host withdrew its clock from
; a server that judged the article.  Before D10-a the owner kept the
; contradicted reading instead, every POST after the first in that window
; minted the identity of the first, and the duplicate was reported as
; `441 posting failed; the article was refused'.
(local
 (defthm fn-inj-decide-without-a-clock-refuses-clock-unusable
   (implies (and (fn-inj-configp config)
                 (fn-inj-config-allow config)
                 (not (fn-clock-observationp observation)))
            (equal (fn-inj-decide source config observation)
                   (fn-inj-refuse :clock-unusable)))
   :hints (("Goal" :in-theory (enable fn-inj-decide)))))

(defthm fn-post-without-a-clock-refuses-with-the-clock-line
  (implies (and (fn-post-sessionp ps)
                (fn-post-session-awaiting ps)
                (fn-inj-configp config)
                (fn-inj-config-allow config)
                (not (fn-clock-observationp injection)))
           (and (equal (fn-post-result-submission
                        (fn-nntp-post-step ps archive config observation
                                           injection (list :article body)))
                       nil)
                (equal (fn-post-result-effects
                        (fn-nntp-post-step ps archive config observation
                                           injection (list :article body)))
                       (fn-post-single
                        ps
                        "441 posting failed; this server has no usable clock reading"))))
  :hints (("Goal" :in-theory (disable fn-nntp-step fn-post-offeredp
                                      fn-inj-decide fn-post-single
                                      fn-post-sessionp))))

(defthm fn-post-disallowed-posting-does-not-await
  (implies (and (fn-post-sessionp ps)
                (not (fn-inj-config-allow config)))
           (not (fn-post-session-awaiting
                 (fn-post-result-session
                  (fn-nntp-post-step ps archive config observation injection
                                     wire-event)))))
  :hints (("Goal" :in-theory (disable fn-nntp-step fn-post-offeredp
                                      fn-inj-decide fn-inj-injectedp
                                      fn-post-refusal-line fn-post-sessionp))))

; The fourth outcome is distinct from all three of the others, whatever
; completion the store reported: a caller that reaches the wrong depth cannot
; be mistaken for one that posted, one that was refused or one that is
; uncertain.  This is the teeth of the 403 above; it is what the old
; no-effects answer could not say.
(defthm fn-post-outcome-separates-a-malformed-session
  (implies (and (not (fn-post-sessionp bad))
                (fn-post-sessionp good))
           (not (equal (fn-post-result-effects (fn-nntp-post-outcome bad completion))
                       (fn-post-result-effects (fn-nntp-post-outcome good other)))))
  :hints (("Goal" :in-theory (e/d (fn-post-single fn-nntp-single)
                                  (fn-nntp-replyp fn-post-sessionp
                                   fn-nntp-response-textp
                                   fn-nntp-initial-status-linep))))
  :rule-classes nil)

(defthm fn-post-outcome-240-only-for-a-durable-observation
  (implies (and (fn-post-sessionp ps)
                (not (equal completion :durable)))
           (not (equal (fn-post-result-effects
                        (fn-nntp-post-outcome ps completion))
                       (fn-post-result-effects
                        (fn-nntp-post-outcome ps :durable)))))
  :hints (("Goal" :in-theory (e/d (fn-post-single fn-nntp-single)
                                  (fn-nntp-replyp fn-post-sessionp
                                   fn-nntp-response-textp
                                   fn-nntp-initial-status-linep))))
  :rule-classes nil)

; A Store refusal is never the uncertain line, and two Store refusal kinds
; never share a line: a client can tell "not stored, and here is why" from
; "do not repost", and one reason from another.
(defthm fn-post-outcome-store-refusal-is-not-uncertain
  (implies (and (fn-post-sessionp ps)
                (fn-post-store-refusalp completion))
           (not (equal (fn-post-result-effects
                        (fn-nntp-post-outcome ps completion))
                       (fn-post-result-effects
                        (fn-nntp-post-outcome ps :uncertain)))))
  :hints (("Goal" :in-theory (e/d (fn-post-single fn-nntp-single
                                   fn-post-store-refusalp)
                                  (fn-nntp-replyp fn-post-sessionp
                                   fn-nntp-response-textp
                                   fn-nntp-initial-status-linep))))
  :rule-classes nil)

; Only OTHER need be a refusal kind: any non-refusal completion renders the
; 240, the clock line or the uncertain line, none of which is a Store
; refusal line, so a hypothesis on KIND would have no violating value.
(defthm fn-post-outcome-store-refusal-kinds-are-distinct
  (implies (and (fn-post-sessionp ps)
                (fn-post-store-refusalp other)
                (not (equal kind other)))
           (not (equal (fn-post-result-effects
                        (fn-nntp-post-outcome ps kind))
                       (fn-post-result-effects
                        (fn-nntp-post-outcome ps other)))))
  :hints (("Goal" :in-theory (e/d (fn-post-single fn-nntp-single
                                   fn-post-store-refusalp)
                                  (fn-nntp-replyp fn-post-sessionp
                                   fn-nntp-response-textp
                                   fn-nntp-initial-status-linep))))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Two submissions on one connection
;
; books/injection-invariants.lisp is included LOCALLY: its rules are proof
; vocabulary for the two forms below and are not inherited by an includer of
; this book.

(local (include-book "injection-invariants"))

; A definitional restatement, cited by :use and never a registry event: the
; submission this step emits for an article body is the injection decision
; over that body, this connection's configuration and the injection clock
; supplied with the event.
(defthm fn-post-submission-is-the-decision-by-definition
  (implies (fn-post-result-submission
            (fn-nntp-post-step ps archive config observation injection
                               (list :article body)))
           (equal (fn-post-result-submission
                   (fn-nntp-post-step ps archive config observation injection
                                      (list :article body)))
                  (fn-inj-decide (fn-post-body-octets body) config injection)))
  :hints (("Goal" :in-theory (disable fn-inj-decide fn-inj-injectedp
                                      fn-nntp-step fn-post-offeredp
                                      fn-post-refusal-line
                                      fn-post-sessionp)))
  :rule-classes nil)

; The keystone the owner's POST seam rests on.  One connection is one
; session, one pinned archive, one configuration and one pinned reader
; observation; the two submissions below differ only in their body and in
; the injection clock the host supplied with each.  Neither supplies a
; Message-ID, so each identity is generated, and two clock readings that
; differ in either number generate two different identities
; (fn-inj-generated-identity-separates-different-clock-readings).  A second
; POST on a connection is therefore a new article, not a duplicate of the
; first.  With ONE reading per connection this conclusion is false and the
; host refuses the second post as a duplicate identity: the hypothesis that
; the clocks differ is what the per-submission seam buys.
(defthm fn-post-distinct-injection-clocks-give-distinct-identities
  (implies (and (fn-clock-observationp ca) (fn-clock-observationp cb)
                (fn-post-result-submission
                 (fn-nntp-post-step ps archive config observation ca
                                    (list :article b1)))
                (fn-post-result-submission
                 (fn-nntp-post-step ps archive config observation cb
                                    (list :article b2)))
                (not (fn-inj-nth 1 (fn-af-proto-article-check
                                    (fn-article-result-article
                                     (fn-article-parse
                                      (fn-post-body-octets b1))))))
                (not (fn-inj-nth 1 (fn-af-proto-article-check
                                    (fn-article-result-article
                                     (fn-article-parse
                                      (fn-post-body-octets b2))))))
                (not (and (equal (fn-clock-wall ca) (fn-clock-wall cb))
                          (equal (fn-clock-monotonic ca)
                                 (fn-clock-monotonic cb)))))
           (not (equal (fn-inj-decision-msgid
                        (fn-post-result-submission
                         (fn-nntp-post-step ps archive config observation ca
                                            (list :article b1))))
                       (fn-inj-decision-msgid
                        (fn-post-result-submission
                         (fn-nntp-post-step ps archive config observation cb
                                            (list :article b2)))))))
  :hints (("Goal"
           :use ((:instance fn-post-submission-is-the-decision-by-definition
                            (injection ca) (body b1))
                 (:instance fn-post-submission-is-the-decision-by-definition
                            (injection cb) (body b2))
                 (:instance fn-post-submission-is-an-injected-article
                            (injection ca) (wire-event (list :article b1)))
                 (:instance fn-post-submission-is-an-injected-article
                            (injection cb) (wire-event (list :article b2)))
                 (:instance fn-inj-generated-identity-is-the-clock-identity
                            (source (fn-post-body-octets b1))
                            (observation ca))
                 (:instance fn-inj-generated-identity-is-the-clock-identity
                            (source (fn-post-body-octets b2))
                            (observation cb))
                 (:instance
                  fn-inj-generated-identity-separates-different-clock-readings
                  (a ca) (b cb)))
           :in-theory (disable fn-nntp-post-step fn-inj-decide
                               fn-inj-injectedp fn-inj-decision-msgid
                               fn-inj-generated-message-id
                               fn-inj-generated-identity-is-the-clock-identity
                               fn-post-submission-is-an-injected-article
                               fn-clock-observationp fn-clock-wall
                               fn-clock-monotonic fn-article-parse
                               fn-af-proto-article-check
                               fn-article-result-article)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Export theory

(deftheory fn-nntp-post-vocabulary
  (quote (fn-post-sessionp fn-post-open-session fn-post-session-consistentp
          fn-post-offeredp fn-post-refusal-line fn-post-single
          fn-post-store-refusalp fn-post-store-refusal-line
          fn-post-body-octets
          fn-nntp-post-step fn-nntp-post-outcome)))

(in-theory (disable fn-nntp-post-vocabulary))

; The same POST machine with the pinned reader dispatcher in its ordinary
; command arm.  While awaiting an article the original machine performs the
; injection decision, and no Message-ID lookup can occur in that state.
(defun fn-nntp-post-step-pinned
    (ps archive index verdicts config observation injection wire-event)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (not (fn-post-sessionp ps)) (fn-post-session-awaiting ps))
      (fn-nntp-post-step ps archive config observation injection wire-event)
    (let ((r (fn-nntp-step-pinned
              (fn-post-session-base ps) archive index verdicts
              (fn-nntp-env observation nil
                           (and (fn-inj-config-allow config) t))
              wire-event)))
      (if (fn-post-offeredp (fn-nntp-result-effects r))
          (if (fn-inj-config-allow config)
              (fn-post-make-result
               (fn-post-make-session (fn-nntp-result-session r) t)
               (fn-nntp-result-effects r) nil)
            (fn-post-make-result
             (fn-post-make-session (fn-nntp-result-session r) nil)
             (fn-post-single ps "440 posting not permitted") nil))
        (fn-post-make-result
         (fn-post-make-session (fn-nntp-result-session r) nil)
         (fn-nntp-result-effects r) nil)))))

(verify-guards fn-nntp-post-step-pinned)

(defthm fn-post-step-pinned-preserves-consistent-session
  (implies (and (fn-post-session-consistentp ps archive)
                (fn-gidx-pin-correspondencep index archive))
           (fn-post-session-consistentp
            (fn-post-result-session
             (fn-nntp-post-step-pinned
              ps archive index verdicts config observation injection wire-event))
            archive))
  :hints (("Goal"
           :in-theory
           (e/d (fn-nntp-post-step-pinned fn-post-session-consistentp
                  fn-post-sessionp)
                (fn-nntp-step-pinned fn-nntp-session-consistentp
                 fn-nntp-sessionp fn-nntp-projectionp fn-nntp-result-session
                 fn-post-offeredp fn-nntp-post-step))
           :use ((:instance fn-nntp-consistent-session-is-session
                            (session
                             (fn-nntp-result-session
                              (fn-nntp-step-pinned
                               (fn-post-session-base ps) archive index verdicts
                               (fn-nntp-env observation nil
                                            (and (fn-inj-config-allow config) t))
                               wire-event))))))))
