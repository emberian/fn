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
(include-book "protocol-table") ; reply texts: (fn-proto-text ROW KEY)
(include-book "injection")
(include-book "group-status")
; P3 (PRF-228): the moderated-group gate.
(include-book "moderation")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-nntp-effectp)
                          (:definition fn-nntp-effectsp))))

(local (in-theory (enable fn-nntp-syntax-vocabulary
                          fn-nntp-session-vocabulary
                          fn-nntp-projection-vocabulary
                          fn-nntp-responses-vocabulary
                          fn-nntp-vocabulary)))
; books/injection.lisp withdraws its total list primitives at export; the two
; record blocks below are stated over them, so they are open here.
(local (in-theory (enable fn-inj-nth fn-inj-car fn-inj-cdr)))
;; Rules the vocabularies above bring that this book's proofs try on every
;; true-listp goal and never use (accumulated-persistence, 2026-09-28, lane
;; d26-books).  The rest of that list, fn-nntp-article-idp-is-consp (1.73M
;; frames here) first, is now withdrawn at its source (lane rule-hygiene).
(local (in-theory (disable fn-nntp-closed-step-has-no-effects
                           fn-nntp-message-id-tail-is-true-listp)))

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
   ((equal reason :unparsable) (fn-proto-text "POST" :refused-unparsable))
   ;; PRF-230: the store profile's header limits, each by its field name.
   ((equal reason :header-fields-limit) (fn-proto-text "POST" :refused-header-fields-limit))
   ((equal reason :header-lines-limit) (fn-proto-text "POST" :refused-header-lines-limit))
   ((equal reason :header-octets-limit) (fn-proto-text "POST" :refused-header-octets-limit))
   ;; O2 (books/group-status.lisp): RFC 3977 section 7.6.3 status "n".
   ((equal reason :group-read-only) (fn-proto-text "POST" :refused-group-read-only))
   ;; P3 (books/moderation.lisp): RFC 5537 section 3.5 item 7 and section 7.
   ((equal reason :approval-not-moderator) (fn-proto-text "POST" :refused-approval-not-moderator))
   ((equal reason :moderation-unavailable) (fn-proto-text "POST" :refused-moderation-unavailable))
   ((equal reason :injection-info) (fn-proto-text "POST" :refused-injection-info))
   ((equal reason :xref) (fn-proto-text "POST" :refused-xref))
   ((equal reason :injection-date-present) (fn-proto-text "POST" :refused-injection-date-present))
   ((equal reason :path-present) (fn-proto-text "POST" :refused-path-present))
   ((equal reason :path-malformed) (fn-proto-text "POST" :refused-path-malformed))
   ((equal reason :path-duplicate) (fn-proto-text "POST" :refused-path-duplicate))
   ((equal reason :path-posted) (fn-proto-text "POST" :refused-path-posted))
   ((equal reason :newsgroups-missing) (fn-proto-text "POST" :refused-newsgroups-missing))
   ((equal reason :newsgroups-duplicate) (fn-proto-text "POST" :refused-newsgroups-duplicate))
   ((equal reason :newsgroups-invalid) (fn-proto-text "POST" :refused-newsgroups-invalid))
   ((equal reason :message-id-duplicate) (fn-proto-text "POST" :refused-message-id-duplicate))
   ((equal reason :message-id-invalid) (fn-proto-text "POST" :refused-message-id-invalid))
   ((equal reason :from-missing) (fn-proto-text "POST" :refused-from-missing))
   ((equal reason :from-duplicate) (fn-proto-text "POST" :refused-from-duplicate))
   ((equal reason :from-invalid) (fn-proto-text "POST" :refused-from-invalid))
   ((equal reason :subject-missing) (fn-proto-text "POST" :refused-subject-missing))
   ((equal reason :subject-duplicate) (fn-proto-text "POST" :refused-subject-duplicate))
   ((equal reason :date-duplicate) (fn-proto-text "POST" :refused-date-duplicate))
   ((equal reason :no-groups) (fn-proto-text "POST" :refused-no-groups))
   ((equal reason :unknown-group) (fn-proto-text "POST" :refused-unknown-group))
   ((equal reason :oversize) (fn-proto-text "POST" :refused-oversize))
   ((equal reason :clock-unusable) (fn-proto-text "POST" :refused-clock-unusable))
   ((equal reason :clock-out-of-range) (fn-proto-text "POST" :refused-clock-out-of-range))
   ((equal reason :posting-disallowed) (fn-proto-text "POST" :refused-posting-disallowed))
   (t (fn-proto-text "POST" :refused-unnamed))))

; books/wire.lisp delivers an (:article lines) event, where each line is its
; octets without CRLF and dot-stuffing has already been undone.  Reassembling
; the exact source the posting agent sent is a decision about octets, so it is
; made here and not in the host.
;
; The executable is a loop (D27; the class of PKT-481): each line is laid
; onto an accumulator in reverse, CRLF after it, and the whole is turned
; round once.  The recursion it replaced took one control-stack frame per
; line, and a frame per octet of one line inside fn-inj-append; the profile
; admits an article of one line as long as the article, so both were a
; remote stop (planning/evidence/served-line-iterative-2026-09-26.md).
(defun fn-post-body-onto (lines acc)
  (declare (xargs :guard t))
  (if (consp lines)
      (fn-post-body-onto (cdr lines)
                         (cons 10 (cons 13 (fn-ag-rev-onto (car lines) acc))))
    acc))

(defun fn-post-body-octets-iter (lines)
  (declare (xargs :guard t))
  (fn-ag-rev-onto (fn-post-body-onto lines nil) nil))

(defun fn-post-body-octets (lines)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp lines)
           (fn-inj-append (car lines)
                          (fn-inj-append '(13 10) (fn-post-body-octets (cdr lines))))
         nil)
       :exec (fn-post-body-octets-iter lines)))

(local (defthm fn-post-rev-onto-is-revappend
         (equal (fn-ag-rev-onto x acc) (revappend x acc))))

(local (defthm fn-post-inj-append-is-append
         (equal (fn-inj-append a b) (append a b))
         :hints (("Goal" :in-theory (enable fn-inj-append)))))

(local (defthm fn-post-body-octets-true-listp
         (true-listp (fn-post-body-octets lines))))

(local (defthm fn-post-body-onto-is-revappend
         (equal (fn-post-body-onto lines acc)
                (revappend (fn-post-body-octets lines) acc))))

;  KEYSTONE (D27, constant stack on the served POST).  The loop the host
; runs is the reassembly the specification defines, on every argument; with
; it the guard proof of fn-post-body-octets makes the loop the executable.
(defthm fn-post-body-octets-iter-is-body-octets
  (equal (fn-post-body-octets-iter lines)
         (fn-post-body-octets lines)))

(verify-guards fn-post-body-octets)

(local (in-theory (disable fn-post-rev-onto-is-revappend fn-post-inj-append-is-append
                           fn-post-body-octets-true-listp fn-post-body-onto-is-revappend)))

(defun fn-post-single (ps text)
  (declare (xargs :guard t))
  (fn-nntp-result-effects (fn-nntp-single (fn-post-session-base ps) text)))

; -----------------------------------------------------------------------------
; The composed step
;
; This is the function the serving host calls, once per wire event, at
; host/reader-host.lisp `fn-reader-chunk`.

; P3: an accepted article the read-only gate passes goes through the
; moderated-group gate (books/moderation.lisp `fn-mod-gate'), which returns
; the decision unchanged unless the article names a moderated group.
(defun fn-post-gated-decision (source config injection)
  (declare (xargs :guard t))
  (let ((decision (fn-inj-decide source config injection)))
    (if (fn-inj-injectedp decision)
        (if (fn-gst-post-gate source config)
            (fn-inj-refuse :group-read-only)
          (fn-mod-gate source config injection decision))
      decision)))

; A refusal of the decision is unchanged; an accepted article is refused
; :group-read-only exactly when the gate names a closed group, and is
; otherwise what the moderated-group gate makes of it.
(defthm fn-post-gated-decision-unfolds
  (equal (fn-post-gated-decision source config injection)
         (if (fn-inj-injectedp (fn-inj-decide source config injection))
             (if (fn-gst-post-gate source config)
                 (fn-inj-refuse :group-read-only)
               (fn-mod-gate source config injection
                            (fn-inj-decide source config injection)))
           (fn-inj-decide source config injection))))

; KEYSTONE (P3, PRF-228): an unapproved article is never visible in a
; moderated group.  Whatever the served POST's decision commits of an
; ordinary article without an Approved field names no group whose status in
; the connection's configuration is moderated: the committed memberships are
; the decision's groups (books/owner.lisp `fn-own-sub-feed-base-groups'),
; so the article is held (in its queue's envelope) or refused, never posted.
; Subject: `fn-post-gated-decision', called by `fn-nntp-post-step' below
; (host line: host/reader-host.lisp `fn-reader-chunk' through
; books/served.lisp).
(defthm fn-post-unapproved-article-is-never-in-a-moderated-group
  (implies (and (fn-mod-facts source config)
                (not (fn-mod-facts-approvedp (fn-mod-facts source config))))
           (not (and (fn-inj-injectedp (fn-post-gated-decision source config
                                                               injection))
                     (fn-mod-named-entries
                      (fn-inj-decision-groups
                       (fn-post-gated-decision source config injection))
                      (fn-inj-config-closed config)))))
  :hints (("Goal" :in-theory (e/d (fn-post-gated-decision)
                                  (fn-mod-gate fn-inj-decide fn-mod-facts
                                   fn-gst-post-gate fn-mod-named-entries))
           :use ((:instance fn-mod-gate-unapproved-names-no-moderated-group
                            (observation injection)
                            (decision (fn-inj-decide source config
                                                     injection)))))))

; KEYSTONE (P3, PRF-228): an approved article from a moderator is visible.
; An ordinary article the injection accepts and the read-only gate passes,
; carrying an Approved field, every named moderated group of which the
; connection's configuration marks :approver (its login moderates it,
; books/nntp-auth.lisp `fn-auth-moderation-config'), is committed exactly as
; the injection decides: into every group it names, the moderated ones
; included.
(defthm fn-post-moderator-approved-article-is-committed
  (implies (and (not (fn-gst-post-gate source config))
                (fn-mod-facts-approvedp (fn-mod-facts source config))
                (fn-mod-all-approverp
                 (fn-mod-named-entries
                  (fn-inj-decision-groups (fn-inj-decide source config injection))
                  (fn-inj-config-closed config))))
           (equal (fn-post-gated-decision source config injection)
                  (fn-inj-decide source config injection)))
  :hints (("Goal" :in-theory (e/d (fn-post-gated-decision fn-mod-gate
                                   fn-mod-facts-approvedp)
                                  (fn-inj-decide fn-mod-facts
                                   fn-gst-post-gate fn-mod-named-entries
                                   fn-mod-all-approverp)))))

; KEYSTONE (P3, PRF-228): an Approved field from anyone else is refused by
; name.  When a named group is moderated and some named moderated group is
; not :approver on this connection, the decision is the refusal
; :approval-not-moderator (441, `fn-post-refusal-line').
(defthm fn-post-forged-approval-is-refused-by-name
  (implies (and (not (fn-gst-post-gate source config))
                (fn-mod-facts-approvedp (fn-mod-facts source config))
                (consp (fn-mod-named-entries
                        (fn-inj-decision-groups
                         (fn-inj-decide source config injection))
                        (fn-inj-config-closed config)))
                (not (fn-mod-all-approverp
                      (fn-mod-named-entries
                       (fn-inj-decision-groups
                        (fn-inj-decide source config injection))
                       (fn-inj-config-closed config)))))
           (equal (fn-post-gated-decision source config injection)
                  (fn-inj-refuse :approval-not-moderator)))
  :hints (("Goal" :in-theory (e/d (fn-post-gated-decision fn-mod-gate
                                   fn-mod-facts-approvedp)
                                  (fn-inj-decide fn-mod-facts
                                   fn-gst-post-gate fn-mod-named-entries
                                   fn-mod-all-approverp fn-inj-refuse))
           :cases ((fn-inj-injectedp (fn-inj-decide source config injection))))))

; The fifth element of the reader listing (PRF-243): the served groups'
; creation facts (PKT-665), projected by books/owner-agent.lisp
; `fn-oag-listing'.
(defun fn-nntp-listing-facts (listing)
  (declare (xargs :guard t))
  (if (and (consp listing) (consp (cdr listing)) (consp (cddr listing))
           (consp (cdddr listing)) (consp (cddddr listing)))
      (car (cddddr listing))
    nil))

; The reader environment of the served step: the connection's pinned clock
; observation, the served groups' creation facts (PKT-665, PRF-243: the
; listing's fifth element), the posting bit, the reader listing (PRF-195)
; and the closed groups (O2, PRF-196), all from the connection's pinned
; configuration.
(defun fn-post-reader-env (config observation)
  (declare (xargs :guard t))
  (fn-nntp-env-full observation
                    (fn-nntp-listing-facts (fn-inj-config-listing config))
                    (and (fn-inj-config-allow config) t)
                    (fn-inj-config-listing config)
                    (fn-inj-config-closed config)))

; The step's lemmas treat the environment as one term; the facts about it
; (fn-post-reader-env-is-an-env below, and its closed list) are stated once.
(in-theory (disable fn-post-reader-env))

(defthm fn-post-reader-env-posting
  (equal (fn-nntp-env-posting (fn-post-reader-env config observation))
         (and (fn-inj-config-allow config) t))
  :hints (("Goal" :in-theory (enable fn-post-reader-env fn-nntp-env
                                     fn-nntp-env-full
                                     fn-nntp-env-posting))))

(defthm fn-post-reader-env-observation
  (equal (fn-nntp-env-observation (fn-post-reader-env config observation))
         observation)
  :hints (("Goal" :in-theory (enable fn-post-reader-env fn-nntp-env
                                     fn-nntp-env-full
                                     fn-nntp-env-observation))))

(defthm fn-post-reader-env-facts
  (equal (fn-nntp-env-facts (fn-post-reader-env config observation))
         (fn-nntp-listing-facts (fn-inj-config-listing config)))
  :hints (("Goal" :in-theory (enable fn-post-reader-env fn-nntp-env
                                     fn-nntp-env-full
                                     fn-nntp-env-facts))))

; The listing LIST NEWSGROUPS and LIST MOTD read is the configuration's.
(defthm fn-post-reader-env-listing
  (equal (fn-nntp-env-listing (fn-post-reader-env config observation))
         (fn-inj-config-listing config))
  :hints (("Goal" :in-theory (enable fn-post-reader-env fn-nntp-env-full
                                     fn-nntp-env-listing))))

; The closed list LIST ACTIVE reads is the configuration's.
(defthm fn-post-reader-env-closed
  (equal (fn-nntp-env-closed (fn-post-reader-env config observation))
         (fn-inj-config-closed config))
  :hints (("Goal" :in-theory (enable fn-post-reader-env fn-nntp-env
                                     fn-nntp-env-full
                                     fn-nntp-env-closed))))

(defun fn-nntp-post-step (ps archive config observation injection wire-event fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (not (fn-post-sessionp ps))
      (fn-post-make-result ps nil nil)
    (if (fn-post-session-awaiting ps)
        (if (and (consp wire-event)
                 (equal (car wire-event) :article)
                 (consp (cdr wire-event))
                 (null (cdr (cdr wire-event))))
            (let ((decision
                   ;; O2: the read-only gate (books/group-status.lisp) turns
                   ;; an article the injection would accept into a refusal
                   ;; by name; every refusal the decision makes keeps its
                   ;; own reason.
                   (fn-post-gated-decision
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
          ; The wire closed the article at the served body limit (the
          ; profile's article bound, `fn-own-body-limit'; books/wire.lisp
          ; `fn-wire-close' :body-overlimit): the refusal names the size, the
          ; same line an injection :oversize gives.  Any other event is an
          ; article that was not received.
          (fn-post-make-result
           (fn-post-make-session (fn-post-session-base ps) nil)
           (fn-post-single ps (if (equal wire-event '(:reject :body-overlimit))
                                  (fn-post-refusal-line :oversize)
                                (fn-proto-text "POST" :not-received)))
           nil))
      ; The reader environment is built here, where the dispatcher is called:
      ; the connection's pinned clock observation and the persisted
      ; group-creation facts.  The served tree persists no creation facts yet
      ; (planning/lanes/HANDOFF-w3-reader-profile.md, proposal 3), so the fact
      ; list is empty and NEWGROUPS reports no group rather than an invented
      ; creation date.
      ; O2: the environment carries the configuration's closed groups
      ; (books/group-status.lisp), so LIST ACTIVE's status field is the
      ; POST gate's list, and the reader listing (PRF-195) with it.
      (let ((r (fn-nntp-step (fn-post-session-base ps) archive
                             (fn-post-reader-env config observation)
                             wire-event fn-arena)))
        (if (fn-post-offeredp (fn-nntp-result-effects r))
            (if (fn-inj-config-allow config)
                (fn-post-make-result
                 (fn-post-make-session (fn-nntp-result-session r) t)
                 (fn-nntp-result-effects r) nil)
              (fn-post-make-result
               (fn-post-make-session (fn-nntp-result-session r) nil)
               (fn-post-single ps (fn-proto-text "POST" :not-permitted))
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
; :conflict are D25's two answers (books/poster-bytes.lisp fn-pb-action-over,
; which the host's books/store-intern.lisp fn-store-existing-action is over
; alpha);
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
                       ;; A crosspost whose group memberships the history
                       ;; budget cannot pay for, the article alone fitting
                       ;; (books/store-capacity-vector.lisp
                       ;; fn-cvec-article-refusal-word; lane membership-budget):
                       ;; "441 posting failed; the store cannot pay for this article's groups: ..."
                       :memberships
                       :storage-failed
                       ;; A signed POST refused at its FN-Authorship carrier
                       ;; (books/peer-authored-accept.lisp fn-pa-served-word):
                       ;; the plan's reason, or the signature observation.
                       :article :carrier :carrier-shape :local-enrollment
                       :signature
                       ;; A verified signed article whose kind-4 composite
                       ;; was not formed, or exceeds the profile's record
                       ;; field (books/store-budget-naming.lisp
                       ;; fn-sbud-signed-event-boundary).
                       :event :signed-record
                       ;; A control article the filing plan refused
                       ;; (books/peer-authored-accept.lisp fn-pa-filing-plan).
                       :control-not-filed :control-malformed
                       ;; A bound login refused by the posting policy
                       ;; (books/login-binding.lisp fn-lb-gate).
                       :login-not-bound :login-unsigned
                       ;; PRF-335: a peer's outbound feed queue has no room
                       ;; for the article's feed obligation
                       ;; (books/owner.lisp fn-own-intent-refusal-word).
                       :feed-queue-full))
       t))

; The reason text of a Store refusal, one per kind: the one table.  POST's
; 441 line (below) and IHAVE's 437 line (books/peer-inbound.lisp
; fn-peer-transit-refusal-line) both render it after their own code, so a
; poster and a relaying peer read the same reason for the same word.
(defun fn-post-store-refusal-text (kind)
  (declare (xargs :guard t))
  (cond
   ((equal kind :duplicate)
    "this article is already stored here")
   ((equal kind :conflict)
    "a different article with this Message-ID is stored here")
   ((equal kind :malformed)
    "the store refused the article as malformed")
   ((equal kind :unaffordable)
    "the store is full: no capacity for this article (unaffordable); the node's operator can raise it")
   ((equal kind :memberships)
    "the store cannot pay for this article's groups: each group it is posted to is charged to the history budget, and the article alone would fit; post it to fewer groups (memberships)")
   ((equal kind :storage-failed)
    "the store could not write the article, nothing was stored")
   ((equal kind :article)
    "the article carrying FN-Authorship does not parse")
   ((equal kind :carrier)
    "the FN-Authorship carrier is malformed")
   ((equal kind :carrier-shape)
    "the FN-Authorship carrier has the wrong shape")
   ((equal kind :local-enrollment)
    "the signer has no current enrollment here (local-enrollment)")
   ((equal kind :signature)
    "the author signature does not verify")
   ((equal kind :event)
    "the signed article did not form a Store event (event)")
   ((equal kind :signed-record)
    "the signed article with its authored source exceeds the configured record size (signed-record)")
   ((equal kind :control-not-filed)
    "control message not filed: its control group is not configured here (control-not-filed)")
   ((equal kind :control-malformed)
    "the Control header field is malformed (control-malformed)")
   ((equal kind :login-not-bound)
    "the login is not bound to this signing principal")
   ((equal kind :login-unsigned)
    "this login posts only articles signed by its bound principal")
   ((equal kind :feed-queue-full)
    "a peer's outbound feed queue is full, nothing was stored (feed-queue-full); the peer is behind, and the node's operator sees which one in health")
   (t "the article was refused")))

(defun fn-post-store-refusal-line (kind)
  (declare (xargs :guard t))
  (string-append "441 posting failed; " (fn-post-store-refusal-text kind)))

(defconst *fn-post-malformed-session-line*
  (fn-proto-text "POST" :malformed-session))

(defconst *fn-post-durable-key-change-refused-line*
  (fn-proto-text "POST" :key-change-refused))

(defun fn-nntp-post-outcome (ps completion)
  (declare (xargs :guard t))
  (if (not (fn-post-sessionp ps))
      (fn-post-make-result ps (fn-post-single ps *fn-post-malformed-session-line*)
                           nil)
    (fn-post-make-result
     ps
     (fn-post-single
      ps
      (cond ((equal completion :durable) (fn-proto-text "POST" :received))
            ;; PKT-473 (PRF-184): durable, and the key change the article
            ;; carried was refused by the Store (books/owner.lisp
            ;; fn-own-post-rendering).  RFC 3977 section 6.3.1: 240, its
            ;; text is fn's.
            ((equal completion :durable-key-change-refused)
             *fn-post-durable-key-change-refused-line*)
            ((equal completion :clock-unusable)
             (fn-post-refusal-line :clock-unusable))
            ((fn-post-store-refusalp completion)
             (fn-post-store-refusal-line completion))
            (t (fn-proto-text "POST" :uncertain))))
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
(verify-guards fn-post-store-refusal-text)
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
             (fn-nntp-post-step ps archive config observation injection wire-event fn-arena))
            archive))
  :hints (("Goal"
           :use ((:instance fn-nntp-step-preserves-consistent-session
                            (session (fn-post-session-base ps))
                            (env (fn-post-reader-env config observation)))
                 (:instance fn-nntp-consistent-session-is-session
                            (session (fn-nntp-result-session
                                      (fn-nntp-step (fn-post-session-base ps)
                                                    archive
                                                    (fn-post-reader-env config observation)
                                                    wire-event fn-arena))))
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
             (fn-nntp-post-step ps archive config observation injection wire-event fn-arena))))
  :hints (("Goal"
           :use ((:instance fn-nntp-step-effects-well-formed
                            (session (fn-post-session-base ps))
                            (env (fn-post-reader-env config observation))))
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
            (fn-nntp-post-step ps archive config observation injection wire-event fn-arena))
           (fn-inj-injectedp
            (fn-post-result-submission
             (fn-nntp-post-step ps archive config observation injection wire-event fn-arena))))
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
                                      (list :article body) fn-arena))
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
                                           injection (list :article body) fn-arena))
                       nil)
                (equal (fn-post-result-effects
                        (fn-nntp-post-step ps archive config observation
                                           injection (list :article body) fn-arena))
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
                                     wire-event fn-arena)))))
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

;; PKT-473 (PRF-184).  The durable reply naming a refused key change: a 240
;; whose text is its own, the reply of no other completion (so neither the
;; plain 240 nor any 441 is ever read as it, and it is never read as them).
(defthm fn-post-outcome-names-a-refused-key-change-only-for-its-completion
  (implies (fn-post-sessionp ps)
           (and (equal (fn-post-result-effects
                        (fn-nntp-post-outcome ps :durable-key-change-refused))
                       (fn-post-single ps *fn-post-durable-key-change-refused-line*))
                (implies (not (equal completion :durable-key-change-refused))
                         (not (equal (fn-post-result-effects
                                      (fn-nntp-post-outcome ps completion))
                                     (fn-post-result-effects
                                      (fn-nntp-post-outcome
                                       ps :durable-key-change-refused)))))))
  :hints (("Goal" :in-theory (e/d (fn-post-single fn-nntp-single
                                   fn-post-store-refusalp)
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
;; What the served step submits for an article body is the gated decision
;; on its octets.
(defthm fn-post-submission-is-the-gated-decision-by-definition
  (implies (fn-post-result-submission
            (fn-nntp-post-step ps archive config observation injection
                               (list :article body) fn-arena))
           (equal (fn-post-result-submission
                   (fn-nntp-post-step ps archive config observation injection
                                      (list :article body) fn-arena))
                  (fn-post-gated-decision (fn-post-body-octets body) config
                                          injection)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-post-step)
                                  (fn-post-gated-decision
                                   fn-post-gated-decision-unfolds
                                   fn-inj-injectedp
                                   fn-nntp-step fn-post-offeredp
                                   fn-post-refusal-line
                                   fn-post-sessionp fn-post-body-octets))))
  :rule-classes nil)

; P3: the gated decision, when injected, is the injection's decision on the
; source or the envelope that forwards it to a moderation queue, whose
; Message-ID is the source's with the envelope prefix
; (books/moderation.lisp `fn-mod-gate-is-the-decision-or-its-envelope'); in
; both cases the injection accepted the source.
(defthm fn-post-gated-decision-is-the-decision-or-its-envelope
  (implies (fn-inj-injectedp (fn-post-gated-decision source config injection))
           (and (fn-inj-injectedp (fn-inj-decide source config injection))
                (or (equal (fn-post-gated-decision source config injection)
                           (fn-inj-decide source config injection))
                    (equal (fn-inj-decision-msgid
                            (fn-post-gated-decision source config injection))
                           (fn-mod-envelope-msgid
                            (fn-inj-decision-msgid
                             (fn-inj-decide source config injection)))))))
  :hints (("Goal" :in-theory (e/d (fn-post-gated-decision)
                                  (fn-inj-decide fn-mod-gate fn-gst-post-gate
                                   fn-mod-envelope-msgid))
           :use ((:instance fn-mod-gate-is-the-decision-or-its-envelope
                            (observation injection)
                            (decision (fn-inj-decide source config
                                                     injection))))))
  :rule-classes nil)

(defthm fn-post-submission-is-the-decision-or-its-envelope
  (implies (fn-post-result-submission
            (fn-nntp-post-step ps archive config observation injection
                               (list :article body) fn-arena))
           (and (fn-inj-injectedp
                 (fn-inj-decide (fn-post-body-octets body) config injection))
                (or (equal (fn-post-result-submission
                            (fn-nntp-post-step ps archive config observation
                                               injection (list :article body) fn-arena))
                           (fn-inj-decide (fn-post-body-octets body) config
                                          injection))
                    (equal (fn-inj-decision-msgid
                            (fn-post-result-submission
                             (fn-nntp-post-step ps archive config observation
                                                injection (list :article body) fn-arena)))
                           (fn-mod-envelope-msgid
                            (fn-inj-decision-msgid
                             (fn-inj-decide (fn-post-body-octets body) config
                                            injection)))))))
  :hints (("Goal" :in-theory (disable fn-inj-decide fn-inj-injectedp
                                      fn-nntp-post-step fn-post-gated-decision
                                      fn-mod-envelope-msgid)
           :use ((:instance fn-post-submission-is-the-gated-decision-by-definition)
                 (:instance fn-post-submission-is-an-injected-article
                            (wire-event (list :article body)))
                 (:instance fn-post-gated-decision-is-the-decision-or-its-envelope
                            (source (fn-post-body-octets body))))))
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
                                    (list :article b1) fn-arena))
                (fn-post-result-submission
                 (fn-nntp-post-step ps archive config observation cb
                                    (list :article b2) fn-arena))
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
                                            (list :article b1) fn-arena)))
                       (fn-inj-decision-msgid
                        (fn-post-result-submission
                         (fn-nntp-post-step ps archive config observation cb
                                            (list :article b2) fn-arena))))))
  :hints (("Goal"
           :use ((:instance fn-post-submission-is-the-decision-or-its-envelope
                            (injection ca) (body b1))
                 (:instance fn-post-submission-is-the-decision-or-its-envelope
                            (injection cb) (body b2))
                 (:instance fn-mod-generated-id-opens
                            (observation ca))
                 (:instance fn-mod-generated-id-opens
                            (observation cb))
                 (:instance fn-mod-envelope-msgid-injective
                            (a (fn-inj-generated-message-id ca config))
                            (b (fn-inj-generated-message-id cb config)))
                 (:instance fn-mod-envelope-msgid-is-not-a-generated-id
                            (m (fn-inj-generated-message-id ca config))
                            (observation cb))
                 (:instance fn-mod-envelope-msgid-is-not-a-generated-id
                            (m (fn-inj-generated-message-id cb config))
                            (observation ca))
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
           ; The rewriter tried the clock-line rule on every submission term
           ; and opened fn-post-sessionp to relieve its hypothesis, never
           ; usefully: 1,390,925 steps with it enabled, 10,367 now.
           :in-theory (disable fn-nntp-post-step fn-inj-decide
                               fn-inj-injectedp fn-inj-decision-msgid
                               fn-inj-generated-message-id
                               fn-inj-generated-identity-is-the-clock-identity
                               fn-post-submission-is-an-injected-article
                               fn-mod-envelope-msgid
                               fn-mod-envelope-msgid-injective
                               fn-mod-envelope-msgid-is-not-a-generated-id
                               fn-clock-observationp fn-clock-wall
                               fn-clock-monotonic fn-article-parse
                               fn-af-proto-article-check
                               fn-article-result-article
                               fn-post-without-a-clock-refuses-with-the-clock-line)))
  :rule-classes nil)

; -----------------------------------------------------------------------------
; Export theory

(deftheory fn-nntp-post-vocabulary
  (quote (fn-post-sessionp fn-post-open-session fn-post-session-consistentp
          fn-post-offeredp fn-post-refusal-line fn-post-single
          fn-post-store-refusalp fn-post-store-refusal-text fn-post-store-refusal-line
          fn-post-body-onto fn-post-body-octets-iter fn-post-body-octets
          fn-nntp-post-step fn-nntp-post-outcome)))

(in-theory (disable fn-nntp-post-vocabulary))

; The same POST machine with the pinned reader dispatcher in its ordinary
; command arm.  While awaiting an article the original machine performs the
; injection decision, and no Message-ID lookup can occur in that state.
(defun fn-nntp-post-step-pinned
    (ps archive index verdicts config observation injection wire-event fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (or (not (fn-post-sessionp ps)) (fn-post-session-awaiting ps))
      (fn-nntp-post-step ps archive config observation injection wire-event fn-arena)
    (let ((r (fn-nntp-step-pinned
              (fn-post-session-base ps) archive index verdicts
              (fn-post-reader-env config observation)
              wire-event fn-arena)))
      (if (fn-post-offeredp (fn-nntp-result-effects r))
          (if (fn-inj-config-allow config)
              (fn-post-make-result
               (fn-post-make-session (fn-nntp-result-session r) t)
               (fn-nntp-result-effects r) nil)
            (fn-post-make-result
             (fn-post-make-session (fn-nntp-result-session r) nil)
             (fn-post-single ps (fn-proto-text "POST" :not-permitted)) nil))
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
              ps archive index verdicts config observation injection wire-event fn-arena))
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
                               (fn-post-reader-env config observation)
                               wire-event fn-arena))))))))
