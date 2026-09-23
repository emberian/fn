; fn: what the SERVED path guarantees about authentication.
;
; books/nntp-auth.lisp proves things about fn-auth-step; this book proves
; the same things about the function the host calls.  The chain is
;
;   tools/run_owner.py Owner.serve  -- one call per recv
;     -> fn-owner-chunk        (host/owner-host.lisp)
;       -> fn-own-read         (books/owner.lisp)
;         -> fn-served-step    (books/served.lisp)   THE SUBJECT
;           -> fn-served-feed -> fn-served-dispatch -> fn-auth-step
;
; and `fn-own-read-is-served-step-on-pinned-prefix' (books/owner-invariants)
; is the theorem that says the second-to-last arrow is an equality, so a
; property of `fn-served-step' is a property of the served port.
;
; WHAT IS PROVED HERE, and what each theorem is FOR.
;
; K1  fn-served-dispatch-of-a-refused-post-leaves-the-wire-in-place.  The
;     load-bearing step.  fn-served-dispatch switches the wire into article
;     mode on EXACTLY the begin-article effect, so a POST the auth layer
;     refused leaves the framing alone: no body can follow, and a submission
;     leaves only from a framed body.
;
; The configuration vocabulary K2 below would need -- fn-auth-postingp is
; false under it for EVERY session, before and after any AUTHINFO exchange,
; because the property is about the pinned configuration and not about who
; has logged in -- is here and proved
; (fn-auth-no-posters-means-no-posting).
;
; OPEN, and not weakened into something smaller.  K2, the fold-level
; statement
;
;   (implies (and (fn-served-connp conn)
;                 (fn-auth-config-no-postersp
;                  (fn-auth-session-config (fn-served-conn-session conn)))
;                 (equal (fn-wire-state-mode (fn-served-conn-wire conn))
;                        :command)
;                 (null (fn-peer-session-peer
;                        (fn-auth-session-base (fn-served-conn-session conn)))))
;            (null (fn-served-submission
;                   (fn-served-result-effects (fn-served-step conn octets)))))
;
; is NOT proved.  It is an induction over fn-served-feed carrying three
; facts; the first is proved and the other two do not exist in this tree:
;
;   (1) `fn-auth-step-preserves-the-config' -- every branch keeps the
;       session's pinned configuration.  PROVED 2026-09-22 in
;       books/nntp-auth.lisp, and with no hypothesis at all rather than the
;       five-branch inspection this note described, because the non-session
;       branch returns its argument.  Teeth in
;       tests/acl2/nntp-auth-teeth-tests.lisp.
;   (2) a WIRE lemma: in command mode fn-wire-feed-byte emits only
;       (:command ...) events and leaves the mode :command or :closed.
;       books/wire-invariants has fn-wire-feed-byte-emits-at-most-one-event
;       and the article-mode direction (fn-wire-article-event-resumes-
;       command-mode, books/served) but not this one.  It belongs in
;       books/wire-invariants.
;   (3) a READER lemma: fn-nntp-post-step emits a submission only from an
;       (:article ...) event.  books/nntp-post has
;       fn-post-submission-is-an-injected-article, which types the
;       submission, and fn-post-refused-body-submits-nothing, which is
;       about the body -- neither says where a submission can come from.
;       It belongs in books/nntp-post.
;
; With (2) and (3), K2 is the append law plus K1.  Recorded in
; planning/proofs.json (PRF-031) as OB-AUTH-FOLD rather than approximated by a
; theorem about a branch nobody reaches.
;
; ALSO NOT PROVED HERE, and not hidden.  The converse -- that a principal
; enrolled WITH the posting flag can post -- is not a theorem: it is
; exhibited by the live client transcripts of tests/test_auth.py and
; planning/evidence/auth-w10-2026-09-20.md, which is evidence about those
; runs and nothing more.  Nor does anything here say a wrong password
; fails; that is A-CRYPTO (specs/failures.md).

(in-package "ACL2")
(include-book "served")

(local (in-theory (enable fn-nntp-syntax-vocabulary
                          fn-nntp-session-vocabulary
                          fn-nntp-responses-vocabulary)))

; -----------------------------------------------------------------------------
; The configuration under which nobody may post
;
; Not "the credential list is empty": a configuration with credentials that
; all lack the posting flag is the interesting case, and the one an operator
; running a read-only server actually writes.

(defun fn-auth-no-posting-credsp (creds)
  (declare (xargs :guard t))
  (if (consp creds)
      (and (not (fn-auth-cred-postingp (car creds)))
           (fn-auth-no-posting-credsp (cdr creds)))
    t))

(defun fn-auth-config-no-postersp (acfg)
  ; Authentication is required, and no enrolled principal may post.  Under
  ; this configuration fn-auth-postingp is false for every session, before
  ; and after any AUTHINFO exchange.
  (declare (xargs :guard t))
  (and (fn-auth-config-requiredp acfg)
       (fn-auth-no-posting-credsp (fn-auth-config-creds acfg))
       t))

(defthm fn-auth-found-cred-cannot-post
  (implies (and (fn-auth-no-posting-credsp creds)
                (fn-auth-find-cred name creds))
           (not (fn-auth-cred-postingp (fn-auth-find-cred name creds))))
  :hints (("Goal" :induct (fn-auth-find-cred name creds)
           :in-theory (e/d (fn-auth-find-cred fn-auth-no-posting-credsp)
                           (fn-auth-cred-postingp fn-auth-cred-name)))))

(defthm fn-auth-no-posters-means-no-posting
  (implies (fn-auth-config-no-postersp (fn-auth-session-config as))
           (not (fn-auth-postingp as)))
  :hints (("Goal"
           :in-theory (e/d (fn-auth-postingp fn-auth-config-no-postersp)
                           (fn-auth-find-cred fn-auth-cred-postingp
                            fn-auth-cred-principal fn-auth-no-posting-credsp
                            fn-auth-config-requiredp fn-auth-config-creds)))))

; -----------------------------------------------------------------------------
; K1.  A refused POST does not touch the framing.

(defun fn-served-post-command-eventp (event)
  (declare (xargs :guard t))
  (and (consp event)
       (equal (car event) :command)
       (consp (cdr event))
       (null (cdr (cdr event)))
       (fn-nntp-command-inputp (car (cdr event)))
       (consp (fn-nntp-tokenize (car (cdr event))))
       (fn-nntp-keyword-tokenp (car (fn-nntp-tokenize (car (cdr event)))))
       (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize (car (cdr event))))
       (fn-nntp-keywordp (car (fn-nntp-tokenize (car (cdr event)))) "POST")
       t))

; Nothing the auth layer emits is a submission: fn-auth-effectp is an NNTP
; effect or the handshake instruction, and a `(:submit ...)` is neither.
; The submission on a served read comes from fn-served-dispatch appending
; one, and it appends one only when the dispatcher produced it.
(defthm fn-auth-effects-carry-no-submission
  (implies (fn-auth-effectsp effects)
           (not (fn-served-submission effects)))
  :hints (("Goal" :induct (fn-served-submission effects)
           :in-theory (e/d (fn-auth-effectsp fn-auth-effectp fn-nntp-effectp
                            fn-served-submission fn-nntp-close-effect
                            fn-nntp-begin-article-effect
                            fn-auth-starttls-effect)
                           (fn-nntp-replyp fn-octet-listp)))))

; POST is resolved by fn-auth-command before the pinned reader/trie can run.
; This is the exact auth transition called by fn-served-dispatch.
(defthm fn-auth-step-pinned-post-without-permission-is-not-offered
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (not (fn-auth-postingp as))
                (fn-nntp-command-inputp line)
                (consp (fn-nntp-tokenize line))
                (fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "POST"))
           (and (not (fn-post-offeredp
                      (fn-post-result-effects
                       (fn-auth-step-pinned as archive index verdicts config
                                            observation injection
                                            (list :command line)))))
                (null (fn-post-result-submission
                       (fn-auth-step-pinned as archive index verdicts config
                                            observation injection
                                            (list :command line))))
                (equal (fn-post-result-session
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       as)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-auth-step-pinned fn-auth-tls-eventp)
                           (fn-peer-step-pinned fn-auth-delegate-pinned
                            fn-auth-command fn-auth-sessionp fn-auth-postingp
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-keyword-tokenp fn-nntp-keywordp
                            fn-post-offeredp
                            fn-nntp-command-arguments-at-mostp))
           :use ((:instance fn-auth-post-without-permission-is-not-offered
                            (keyword (car (fn-nntp-tokenize line)))
                            (args (cdr (fn-nntp-tokenize line))))))))

(defthm fn-served-dispatch-of-a-refused-post-leaves-the-wire-in-place
  (implies (and (fn-served-connp conn)
                (not (fn-auth-session-handshakingp
                      (fn-served-conn-session conn)))
                (not (fn-auth-postingp (fn-served-conn-session conn)))
                (fn-served-post-command-eventp event))
           (and (equal (fn-served-conn-wire
                        (fn-served-result-conn (fn-served-dispatch conn event)))
                       (fn-served-conn-wire conn))
                (equal (fn-served-conn-session
                        (fn-served-result-conn (fn-served-dispatch conn event)))
                       (fn-served-conn-session conn))
                (null (fn-served-submission
                       (fn-served-result-effects
                        (fn-served-dispatch conn event))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-served-dispatch fn-served-post-command-eventp)
                           (fn-auth-step-pinned fn-auth-sessionp fn-auth-postingp
                            fn-wire-begin-article fn-post-offeredp
                            fn-served-submission fn-served-connp
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-keyword-tokenp fn-nntp-keywordp
                            fn-nntp-command-arguments-at-mostp
                            fn-served-connp-is-consistent-session
                            fn-auth-step-pinned-effects-well-formed
                            fn-auth-effects-carry-no-submission
                            fn-auth-step-pinned-post-without-permission-is-not-offered))
           :use ((:instance fn-auth-step-pinned-post-without-permission-is-not-offered
                            (as (fn-served-conn-session conn))
                            (archive (fn-served-conn-archive conn))
                            (index (fn-served-conn-index conn))
                            (verdicts (fn-served-conn-verdicts conn))
                            (config (fn-served-conn-config conn))
                            (observation (fn-served-conn-observation conn))
                            (injection (fn-served-conn-injection conn))
                            (line (car (cdr event))))
                 (:instance fn-served-connp-is-consistent-session (c conn))
                 (:instance fn-served-connp-is-index-correspondence (c conn))
                 (:instance fn-auth-step-pinned-effects-well-formed
                            (as (fn-served-conn-session conn))
                            (archive (fn-served-conn-archive conn))
                            (index (fn-served-conn-index conn))
                            (verdicts (fn-served-conn-verdicts conn))
                            (config (fn-served-conn-config conn))
                            (observation (fn-served-conn-observation conn))
                            (injection (fn-served-conn-injection conn))
                            (wire-event event))
                 (:instance fn-auth-effects-carry-no-submission
                            (effects (fn-post-result-effects
                                      (fn-auth-step-pinned
                                       (fn-served-conn-session conn)
                                       (fn-served-conn-archive conn)
                                       (fn-served-conn-index conn)
                                       (fn-served-conn-verdicts conn)
                                       (fn-served-conn-config conn)
                                       (fn-served-conn-observation conn)
                                       (fn-served-conn-injection conn)
                                       event))))))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).

(deftheory fn-auth-served-vocabulary
  '((:d fn-auth-no-posting-credsp) (:d fn-auth-config-no-postersp)
    (:d fn-served-post-command-eventp)))

(in-theory (disable fn-auth-served-vocabulary))
