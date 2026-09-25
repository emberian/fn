; fn: what the SERVED path guarantees about authentication.
;
; books/nntp-auth.lisp proves things about fn-auth-step; this book proves
; the same things about the function the host calls.  The chain is
;
;   tools/run_owner.py Owner.serve  -- one call per recv
;     -> fn-owner-chunk        (host/owner-host.lisp)
;       -> fn-own-read         (books/owner.lisp)
;         -> fn-served-step    (books/served.lisp)   THE SUBJECT
;           -> fn-served-feed -> fn-served-dispatch -> fn-auth-step-pinned
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
; K2 is proved in books/nntp-auth-fold.lisp over the host-called
; fn-served-step.  Its premise carries a valid connection, a pinned
; no-posters authentication configuration, and no pending local POST body.
; fn-auth-fold-step-has-no-local-submission checks the ENTIRE effect list,
; while fn-auth-fold-step-preserves-safe-connp carries the premise over
; reads.  A no-posting credential may still bind an authorized transit peer
; role through AUTHINFO; TAKETHIS then emits fn-peer-submissionp, distinct
; from fn-inj-injectedp.  A reachable complete-read witness in
; tests/acl2/nntp-auth-fold-tests.lisp refutes the former claim that no
; submission of any kind can leave.  The proof factors POST-command origin
; through the pinned reader/peer path and folds dispatch events and bytes;
; it requires no blanket restriction on transit peer policy.
;
; P1 (the section "P1 at the host-called step" below) states the 483, the
; 480 and the posting allowance over fn-auth-step-pinned and over
; fn-served-dispatch.
;
; ALSO NOT PROVED HERE, and not hidden.  The converse -- that a principal
; enrolled WITH the posting flag can post -- is proved only up to this
; layer: fn-auth-step-pinned-post-by-a-principal-with-the-flag-is-delegated
; says the authentication layer hands such a POST, unchanged, to the pinned
; reader/injection path, where the pinned injection configuration still
; decides.  That the whole POST then succeeds is exhibited by the live
; client transcripts of tests/test_auth.py and
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
                           (fn-nntp-replyp fn-octet-listp fn-nntp-effectsp
                            fn-auth-nntp-effects-are-auth-effects
                            fn-nntp-article-idp-is-consp
                            fn-nntp-response-text-true-listp
                            fn-nntp-message-id-token-is-response-text
                            (:linear fn-cp-id-length-bound))))))

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
                            fn-served-conn-pinned-index fn-gidx-pin-correspondencep
                            fn-gidx-pin-trie fn-gidx-pinp
                            fn-midx-correspondencep
                            fn-served-connp-is-group-correspondence
                            fn-served-connp-is-pinned-trie-correspondence
                            fn-wire-begin-article fn-post-offeredp
                            fn-served-submission fn-served-connp
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-keyword-tokenp fn-nntp-keywordp
                            fn-nntp-command-arguments-at-mostp
                            fn-served-connp-is-consistent-session
                            fn-auth-step-pinned-effects-well-formed
                            fn-auth-effects-carry-no-submission
                            fn-auth-step-pinned-post-without-permission-is-not-offered
                            fn-auth-nntp-effects-are-auth-effects
                            fn-nntp-article-idp-is-consp
                            fn-nntp-response-text-true-listp
                            fn-nntp-message-id-token-is-response-text
                            (:linear fn-served-step-nntp-steps-is-bounded)
                            (:linear fn-cp-id-length-bound)))
           :use ((:instance fn-auth-step-pinned-post-without-permission-is-not-offered
                            (as (fn-served-conn-session conn))
                            (archive (fn-served-conn-archive conn))
                            (index (fn-served-conn-pinned-index conn))
                            (verdicts (fn-served-conn-verdicts conn))
                            (config (fn-served-conn-config conn))
                            (observation (fn-served-conn-observation conn))
                            (injection (fn-served-conn-injection conn))
                            (line (car (cdr event))))
                 (:instance fn-served-connp-is-consistent-session (c conn))
                 (:instance fn-served-connp-is-group-correspondence (c conn))
                 (:instance fn-served-connp-is-pinned-trie-correspondence (c conn))
                 (:instance fn-auth-step-pinned-effects-well-formed
                            (as (fn-served-conn-session conn))
                            (archive (fn-served-conn-archive conn))
                            (index (fn-served-conn-pinned-index conn))
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
                                       (fn-served-conn-pinned-index conn)
                                       (fn-served-conn-verdicts conn)
                                       (fn-served-conn-config conn)
                                       (fn-served-conn-observation conn)
                                       (fn-served-conn-injection conn)
                                       event))))))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).

; The two public steps share the authentication gate.  On a command answered
; by that gate, the historical verdict/index arguments are immaterial: only
; delegation can observe them.  The premise is about the parsed command, not
; about a guessed index correspondence, so AUTHINFO and the permission refusals
; retain their decision even before an index is available.
(defthm fn-auth-step-pinned-agrees-with-auth-step-on-handled-command
  (implies (and (fn-nntp-command-inputp line)
                (consp (fn-nntp-tokenize line))
                (fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (fn-auth-command as config
                                 (car (fn-nntp-tokenize line))
                                 (cdr (fn-nntp-tokenize line))))
           (equal (fn-auth-step-pinned
                   as archive index verdicts config observation injection
                   (list :command line))
                  (fn-auth-step as archive config observation injection
                                (list :command line))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-auth-step-pinned fn-auth-step)
                           (fn-auth-command fn-auth-sessionp
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp)))))

; -----------------------------------------------------------------------------
; P1 at the host-called step: 483, 480 and the posting allowance.
;
; host/owner-host.lisp:1240 (fn-owner-chunk) calls fn-ocfg-read-tls-prefix,
; which reaches fn-served-dispatch (books/served.lisp:616); the one call that
; dispatcher makes into the authentication layer is fn-auth-step-pinned
; (books/served.lisp:617).  The 480 and 483 keystones of books/nntp-auth are
; stated over the sibling fn-auth-step.  Each theorem below is stated over
; fn-auth-step-pinned or over fn-served-dispatch, and the 480 and 483 ones are
; proved by instantiating the fn-auth-step keystone together with the bridge
; fn-auth-step-pinned-agrees-with-auth-step-on-handled-command above, whose
; premise the two answer lemmas discharge.  Teeth:
; tests/acl2/nntp-auth-teeth-tests.lisp, keystones 11 to 17.

; A keyword token is never nil, so a tokenization whose first token is one
; is a cons.  (books/nntp-auth proves the same fact locally.)
(local (defthm fn-auth-served-keyword-token-car-has-a-cons
  (implies (fn-nntp-keyword-tokenp (car x)) (consp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-nntp-keyword-tokenp)))))

; AUTHINFO and POST are keyword tokens once matched: the matched text is.
; POST is restricted, so books/nntp-auth's exported lemma covers it; the
; AUTHINFO case upcases, and upcasing keeps nothing that was not a keyword
; token (the same argument books/nntp-auth makes locally).
(local (defthm fn-auth-served-upcase-keeps-a-rest-byte
  (implies (fn-nntp-keyword-rest-bytep (fn-nntp-upcase-byte b))
           (fn-nntp-keyword-rest-bytep b))
  :hints (("Goal" :in-theory (enable fn-nntp-keyword-rest-bytep
                                     fn-nntp-keyword-first-bytep
                                     fn-nntp-upcase-byte)))))

(local (defthm fn-auth-served-upcase-keyword-consp
  (equal (consp (fn-nntp-upcase-keyword x)) (consp x))
  :hints (("Goal" :in-theory (enable fn-nntp-upcase-keyword)))))

(local (defthm fn-auth-served-upcase-keeps-a-keyword-tail
  (implies (fn-nntp-keyword-tailp (fn-nntp-upcase-keyword x))
           (fn-nntp-keyword-tailp x))
  :hints (("Goal" :in-theory (enable fn-nntp-keyword-tailp
                                     fn-nntp-upcase-keyword)))))

(local (defthm fn-auth-served-upcase-keeps-a-keyword-token
  (implies (fn-nntp-keyword-tokenp (fn-nntp-upcase-keyword x))
           (fn-nntp-keyword-tokenp x))
  :hints (("Goal" :in-theory (e/d (fn-nntp-keyword-tokenp
                                   fn-nntp-upcase-keyword
                                   fn-nntp-keyword-first-bytep
                                   fn-nntp-upcase-byte)
                                  (fn-nntp-keyword-tailp))))))

(defthm fn-auth-authinfo-keyword-is-a-keyword-token
  (implies (fn-nntp-keywordp keyword "AUTHINFO")
           (fn-nntp-keyword-tokenp keyword))
  :hints (("Goal" :in-theory (e/d (fn-nntp-keywordp)
                                  (fn-nntp-keyword-tokenp
                                   fn-nntp-upcase-keyword))
           :use ((:instance fn-auth-served-upcase-keeps-a-keyword-token
                            (x keyword))))))

(defthm fn-auth-post-keyword-is-restricted
  (implies (fn-nntp-keywordp keyword "POST")
           (fn-auth-restricted-keywordp keyword))
  :hints (("Goal" :in-theory (e/d (fn-auth-restricted-keywordp)
                                  (fn-nntp-keywordp)))))

; The two answer lemmas: the bridge's premise, on the gate and on AUTHINFO.
(defthm fn-auth-command-answers-a-gated-keyword
  (implies (and (fn-auth-config-requiredp (fn-auth-session-config as))
                (not (fn-auth-session-subject as))
                (fn-auth-restricted-keywordp keyword))
           (fn-auth-command as config keyword args))
  :hints (("Goal" :in-theory (e/d (fn-auth-command fn-auth-gatedp)
                                  (fn-auth-single fn-auth-restricted-keywordp
                                   fn-auth-config-requiredp)))))

(defthm fn-auth-command-answers-authinfo
  (implies (fn-nntp-keywordp keyword "AUTHINFO")
           (fn-auth-command as config keyword args))
  :hints (("Goal" :in-theory (e/d (fn-auth-command fn-auth-authinfo)
                                  (fn-auth-gatedp fn-auth-single
                                   fn-auth-postingp fn-nntp-keywordp
                                   fn-auth-token-argp fn-auth-find-cred
                                   fn-auth-checkp
                                   fn-auth-bind-principal-peer)))))

; A single reply is a proper list and is not the 340 offer.
(local (defthm fn-auth-served-single-shape
  (and (true-listp (fn-auth-single as text))
       (not (fn-post-offeredp (fn-auth-single as text))))
  :hints (("Goal" :in-theory (enable fn-auth-single fn-nntp-result-effects
                                     fn-nntp-single fn-nntp-make-result
                                     fn-post-offeredp
                                     fn-nntp-begin-article-effect)))))

; KEYSTONE (b), step.  A restricted command on an unauthenticated connection
; under a configuration that requires authentication is answered 480 and is
; not performed, by the function the served dispatcher calls.
(defthm fn-auth-step-pinned-gated-command-is-refused-and-not-performed
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (fn-auth-config-requiredp (fn-auth-session-config as))
                (not (fn-auth-session-subject as))
                (fn-nntp-command-inputp line)
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (fn-auth-restricted-keywordp (car (fn-nntp-tokenize line))))
           (and (null (fn-post-result-submission
                       (fn-auth-step-pinned as archive index verdicts config
                                            observation injection
                                            (list :command line))))
                (not (fn-post-offeredp
                      (fn-post-result-effects
                       (fn-auth-step-pinned as archive index verdicts config
                                            observation injection
                                            (list :command line)))))
                (equal (fn-post-result-session
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       as)
                (equal (fn-post-result-effects
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       (fn-auth-single as "480 authentication required"))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable fn-auth-step-pinned fn-auth-step fn-auth-command
                               fn-auth-single fn-auth-restricted-keywordp
                               fn-auth-sessionp fn-auth-config-requiredp
                               fn-nntp-tokenize fn-nntp-command-inputp
                               fn-nntp-keyword-tokenp fn-post-offeredp
                               fn-nntp-command-arguments-at-mostp
                               fn-auth-command-answers-a-gated-keyword
                               fn-auth-restricted-keyword-is-a-keyword-token
                               fn-auth-gated-command-is-refused-and-not-performed
                               fn-auth-step-pinned-agrees-with-auth-step-on-handled-command)
           :use ((:instance fn-auth-gated-command-is-refused-and-not-performed)
                 (:instance
                  fn-auth-step-pinned-agrees-with-auth-step-on-handled-command)
                 (:instance fn-auth-restricted-keyword-is-a-keyword-token
                            (keyword (car (fn-nntp-tokenize line))))
                 (:instance fn-auth-command-answers-a-gated-keyword
                            (keyword (car (fn-nntp-tokenize line)))
                            (args (cdr (fn-nntp-tokenize line))))))))

; KEYSTONE (a), step.  Under a protected-only policy, AUTHINFO on a clear
; connection is answered 483 and nothing else happens: the session is the
; one the command arrived on (no name cached, no subject installed) and the
; reply does not depend on the arguments, so the secret is never compared.
(defthm fn-auth-step-pinned-protected-only-refuses-authinfo-before-tls
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (not (fn-auth-session-subject as))
                (fn-auth-config-protected-onlyp (fn-auth-session-config as))
                (not (fn-auth-session-tlsp as))
                (fn-nntp-command-inputp line)
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "AUTHINFO"))
           (and (equal (fn-post-result-effects
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       (fn-auth-single
                        as
                        "483 a protected channel is required; use STARTTLS"))
                (equal (fn-post-result-session
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       as)
                (null (fn-post-result-submission
                       (fn-auth-step-pinned as archive index verdicts config
                                            observation injection
                                            (list :command line))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable fn-auth-step-pinned fn-auth-step fn-auth-command
                               fn-auth-single fn-auth-sessionp
                               fn-auth-config-protected-onlyp
                               fn-nntp-tokenize fn-nntp-command-inputp
                               fn-nntp-keyword-tokenp fn-nntp-keywordp
                               fn-nntp-command-arguments-at-mostp
                               fn-auth-command-answers-authinfo
                               fn-auth-authinfo-keyword-is-a-keyword-token
                               fn-auth-step-protected-only-refuses-authinfo-before-tls
                               fn-auth-step-pinned-agrees-with-auth-step-on-handled-command)
           :use ((:instance fn-auth-step-protected-only-refuses-authinfo-before-tls)
                 (:instance
                  fn-auth-step-pinned-agrees-with-auth-step-on-handled-command)
                 (:instance fn-auth-authinfo-keyword-is-a-keyword-token
                            (keyword (car (fn-nntp-tokenize line))))
                 (:instance fn-auth-command-answers-authinfo
                            (keyword (car (fn-nntp-tokenize line)))
                            (args (cdr (fn-nntp-tokenize line))))))))

; The served connection is rebuilt from its own fields by the dispatcher;
; with the wire and the session unchanged it is the same connection.
(local (defthm fn-served-connp-is-shape
  (implies (fn-served-connp c) (fn-served-conn-shapep c))
  :hints (("Goal" :in-theory (enable fn-served-connp)))))

(local (defthm fn-served-nine-list-rebuilt
  (implies (and (true-listp c) (equal (len c) 10))
           (equal (list (car c) (cadr c) (caddr c) (cadddr c)
                        (car (cddddr c)) (cadr (cddddr c))
                        (caddr (cddddr c)) (cadddr (cddddr c))
                        (car (cddddr (cddddr c)))
                        (cadr (cddddr (cddddr c))))
                  c))
  :hints (("Goal" :in-theory (union-theories
                              '(len true-listp car-cons cdr-cons
                                cons-car-cdr fix)
                              (theory 'ground-zero))))))

(local (defthm fn-served-conn-rebuilt-from-its-fields
  (implies (fn-served-conn-shapep c)
           (equal (fn-served-make-conn-group-indexed
                   (fn-served-conn-wire c) (fn-served-conn-session c)
                   (fn-served-conn-archive c) (fn-served-conn-config c)
                   (fn-served-conn-observation c)
                   (fn-served-conn-injection c) (fn-served-conn-verdicts c)
                   (fn-served-conn-index c) (fn-served-conn-group-index c) (fn-served-conn-control c))
                  c))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-served-conn-shapep
                                fn-served-make-conn-group-indexed
                                fn-served-conn-wire fn-served-conn-session
                                fn-served-conn-archive fn-served-conn-config
                                fn-served-conn-observation
                                fn-served-conn-injection
                                fn-served-conn-verdicts fn-served-conn-index
                                fn-served-conn-group-index
                                fn-served-conn-control
                                fn-ag-car fn-ag-cdr)
                              (theory 'ground-zero))
           :use ((:instance fn-served-nine-list-rebuilt))))))

(local (defthm fn-served-connp-has-an-auth-session
  (implies (fn-served-connp c)
           (fn-auth-sessionp (fn-served-conn-session c)))
  :hints (("Goal" :in-theory (e/d (fn-auth-session-consistentp)
                                  (fn-served-connp fn-auth-sessionp
                                   fn-peer-session-consistentp
                                   fn-served-connp-is-consistent-session))
           :use ((:instance fn-served-connp-is-consistent-session))))))

; KEYSTONE (b), served.  One dispatched restricted command on an
; unauthenticated connection whose policy requires authentication leaves the
; ENTIRE connection as it was -- wire framing, session, pinned archive and
; indexes -- and its only effect is the 480 line, so no :submit effect leaves.
(defthm fn-served-dispatch-of-a-gated-command-is-480-and-changes-nothing
  (implies (and (fn-served-connp conn)
                (not (fn-auth-session-handshakingp
                      (fn-served-conn-session conn)))
                (fn-auth-config-requiredp
                 (fn-auth-session-config (fn-served-conn-session conn)))
                (not (fn-auth-session-subject (fn-served-conn-session conn)))
                (fn-nntp-command-inputp line)
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (fn-auth-restricted-keywordp (car (fn-nntp-tokenize line))))
           (and (equal (fn-served-result-conn
                        (fn-served-dispatch conn (list :command line)))
                       conn)
                (equal (fn-served-result-effects
                        (fn-served-dispatch conn (list :command line)))
                       (fn-auth-single (fn-served-conn-session conn)
                                       "480 authentication required"))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-served-dispatch)
                           (fn-auth-step-pinned fn-auth-single fn-auth-sessionp
                            fn-auth-config-requiredp fn-auth-restricted-keywordp
                            fn-served-conn-pinned-index fn-served-connp
                            fn-served-make-conn-group-indexed
                            fn-post-offeredp
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-command-arguments-at-mostp
                            fn-auth-step-pinned-gated-command-is-refused-and-not-performed))
           :use ((:instance fn-auth-step-pinned-gated-command-is-refused-and-not-performed
                            (as (fn-served-conn-session conn))
                            (archive (fn-served-conn-archive conn))
                            (index (fn-served-conn-pinned-index conn))
                            (verdicts (fn-served-conn-verdicts conn))
                            (config (fn-served-conn-config conn))
                            (observation (fn-served-conn-observation conn))
                            (injection (fn-served-conn-injection conn)))
                 (:instance fn-served-connp-has-an-auth-session (c conn))
                 (:instance fn-served-conn-rebuilt-from-its-fields (c conn))))))

; KEYSTONE (a), served.  AUTHINFO on a clear connection under protected-only
; leaves the entire connection as it was and answers exactly 483.
(defthm fn-served-dispatch-of-authinfo-on-a-clear-connection-is-483-and-changes-nothing
  (implies (and (fn-served-connp conn)
                (not (fn-auth-session-handshakingp
                      (fn-served-conn-session conn)))
                (not (fn-auth-session-subject (fn-served-conn-session conn)))
                (fn-auth-config-protected-onlyp
                 (fn-auth-session-config (fn-served-conn-session conn)))
                (not (fn-auth-session-tlsp (fn-served-conn-session conn)))
                (fn-nntp-command-inputp line)
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "AUTHINFO"))
           (and (equal (fn-served-result-conn
                        (fn-served-dispatch conn (list :command line)))
                       conn)
                (equal (fn-served-result-effects
                        (fn-served-dispatch conn (list :command line)))
                       (fn-auth-single
                        (fn-served-conn-session conn)
                        "483 a protected channel is required; use STARTTLS"))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-served-dispatch)
                           (fn-auth-step-pinned fn-auth-single fn-auth-sessionp
                            fn-auth-config-protected-onlyp
                            fn-served-conn-pinned-index fn-served-connp
                            fn-served-make-conn-group-indexed
                            fn-post-offeredp fn-nntp-keywordp
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-command-arguments-at-mostp
                            fn-auth-step-pinned-protected-only-refuses-authinfo-before-tls))
           :use ((:instance fn-auth-step-pinned-protected-only-refuses-authinfo-before-tls
                            (as (fn-served-conn-session conn))
                            (archive (fn-served-conn-archive conn))
                            (index (fn-served-conn-pinned-index conn))
                            (verdicts (fn-served-conn-verdicts conn))
                            (config (fn-served-conn-config conn))
                            (observation (fn-served-conn-observation conn))
                            (injection (fn-served-conn-injection conn)))
                 (:instance fn-served-connp-has-an-auth-session (c conn))
                 (:instance fn-served-conn-rebuilt-from-its-fields (c conn))))))

; (c) The posting allowance follows the authenticated credential.
;
; Three statements, all over fn-auth-step-pinned.  A login installs exactly
; the credential's flag; an authenticated principal whose credential lacks
; the flag is answered 440 and nothing happens; one whose credential carries
; it is not refused by this layer at all -- its POST is delegated, whole, to
; the pinned reader/injection path, where the pinned injection configuration
; still decides (books/nntp-post).

(local (defthm fn-auth-served-bind-keeps-the-auth-fields
  (and (equal (fn-auth-session-config (fn-auth-bind-principal-peer as p))
              (fn-auth-session-config as))
       (equal (fn-auth-session-pending (fn-auth-bind-principal-peer as p))
              (fn-auth-session-pending as))
       (equal (fn-auth-session-subject (fn-auth-bind-principal-peer as p))
              (fn-auth-session-subject as)))
  :hints (("Goal" :in-theory (e/d (fn-auth-bind-principal-peer
                                   fn-auth-with-base)
                                  (fn-auth-principal-match))))))

(local (defthm fn-auth-served-command-login-installs-the-flag
  (implies (and (not (fn-auth-session-subject as))
                (fn-auth-session-subject
                 (fn-post-result-session (fn-auth-command as config keyword args))))
           (iff (fn-auth-postingp
                 (fn-post-result-session (fn-auth-command as config keyword args)))
                (fn-auth-cred-postingp
                 (fn-auth-find-cred (fn-auth-session-pending as)
                                    (fn-auth-config-creds
                                     (fn-auth-session-config as))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-command fn-auth-authinfo fn-auth-starttls
                            fn-auth-postingp fn-auth-checkp)
                           (fn-auth-single fn-auth-bind-principal-peer
                            fn-auth-clear-principal-peer
                            fn-auth-gatedp fn-auth-find-cred
                            fn-authsec-checkp fn-auth-cred-postingp
                            fn-auth-cred-principal fn-auth-token-argp
                            fn-auth-sessionp
                            fn-nntp-keywordp fn-nntp-keyword-tokenp
                            fn-nntp-multi fn-auth-capability-lines-for-peer
                            fn-auth-peer-record fn-inj-config-allow
                            fn-auth-config-protected-onlyp
                            fn-auth-config-tls-availablep
                            fn-auth-config-requiredp))))))

(local (defthm fn-auth-served-delegate-keeps-the-subject
  (equal (fn-auth-session-subject
          (fn-post-result-session
           (fn-auth-delegate-pinned as archive index verdicts config
                                    observation injection wire-event)))
         (fn-auth-session-subject as))
  :hints (("Goal" :in-theory (e/d (fn-auth-delegate-pinned fn-auth-with-base)
                                  (fn-peer-step-pinned))))))

; KEYSTONE (c1).  Whatever the wire event, a step that takes a connection
; with no subject to one with a subject installs the posting allowance of the
; credential enrolled under the cached name, and nothing else.
(defthm fn-auth-step-pinned-login-installs-the-credential-posting-flag
  (implies (and (not (fn-auth-session-subject as))
                (fn-auth-session-subject
                 (fn-post-result-session
                  (fn-auth-step-pinned as archive index verdicts config
                                       observation injection wire-event))))
           (iff (fn-auth-postingp
                 (fn-post-result-session
                  (fn-auth-step-pinned as archive index verdicts config
                                       observation injection wire-event)))
                (fn-auth-cred-postingp
                 (fn-auth-find-cred (fn-auth-session-pending as)
                                    (fn-auth-config-creds
                                     (fn-auth-session-config as))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step-pinned fn-auth-tls-established)
                           (fn-auth-command fn-auth-delegate-pinned
                            fn-auth-postingp fn-auth-cred-postingp
                            fn-auth-find-cred fn-auth-sessionp
                            fn-auth-tls-eventp
                            fn-nntp-keyword-tokenp fn-nntp-tokenize
                            fn-nntp-command-inputp
                            fn-nntp-command-arguments-at-mostp)))))

; KEYSTONE (c2).  An authenticated principal whose credential lacks the
; posting flag is answered 440 to POST, and nothing happens.
(defthm fn-auth-step-pinned-post-by-a-principal-without-the-flag-is-440
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (fn-auth-session-subject as)
                (not (fn-auth-cred-postingp
                      (fn-auth-find-cred (fn-auth-session-pending as)
                                         (fn-auth-config-creds
                                          (fn-auth-session-config as)))))
                (fn-nntp-command-inputp line)
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "POST"))
           (and (equal (fn-post-result-effects
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       (fn-auth-single
                        as "440 posting not permitted for this principal"))
                (equal (fn-post-result-session
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       as)
                (null (fn-post-result-submission
                       (fn-auth-step-pinned as archive index verdicts config
                                            observation injection
                                            (list :command line))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step-pinned fn-auth-command fn-auth-gatedp
                            fn-auth-postingp fn-auth-tls-eventp)
                           (fn-auth-delegate-pinned fn-auth-single
                            fn-auth-sessionp fn-auth-find-cred
                            fn-auth-cred-postingp fn-auth-cred-principal
                            fn-auth-restricted-keywordp
                            fn-nntp-keywordp fn-nntp-keyword-tokenp
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-command-arguments-at-mostp
                            fn-auth-post-keyword-is-restricted
                            fn-auth-restricted-keyword-is-a-keyword-token))
           :use ((:instance fn-auth-post-keyword-is-restricted
                            (keyword (car (fn-nntp-tokenize line))))
                 (:instance fn-auth-restricted-keyword-is-a-keyword-token
                            (keyword (car (fn-nntp-tokenize line))))))))

; A credential found in a session's configuration names a principal, so a
; posting credential whose principal is the subject makes the session an
; authenticated one.
(local (defthm fn-auth-served-posting-cred-has-a-principal
  (implies (and (fn-auth-sessionp as)
                (fn-auth-cred-postingp
                 (fn-auth-find-cred name (fn-auth-config-creds
                                          (fn-auth-session-config as)))))
           (fn-auth-cred-principal
            (fn-auth-find-cred name (fn-auth-config-creds
                                     (fn-auth-session-config as)))))
  :hints (("Goal" :in-theory (e/d (fn-auth-sessionp fn-auth-configp
                                   fn-auth-credp)
                                  (fn-auth-find-cred fn-auth-cred-listp
                                   fn-authsec-verifierp
                                   fn-nntp-printable-tokenp
                                   fn-peer-sessionp
                                   fn-auth-find-cred-is-a-cred))
           :use ((:instance fn-auth-find-cred-is-a-cred
                            (creds (fn-auth-config-creds
                                    (fn-auth-session-config as)))))))))

; KEYSTONE (c3).  An authenticated principal whose credential carries the
; posting flag is not refused here: the step is exactly the delegation to the
; pinned reader/injection path.  No command-bound premise: a POST line the
; preflight refuses is delegated as well, so the conclusion holds of it.
; The subject premise is not written either; the fourth premise forces it,
; because a credential found in a session's configuration names a principal.
(defthm fn-auth-step-pinned-post-by-a-principal-with-the-flag-is-delegated
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (fn-auth-cred-postingp
                 (fn-auth-find-cred (fn-auth-session-pending as)
                                    (fn-auth-config-creds
                                     (fn-auth-session-config as))))
                (equal (fn-auth-cred-principal
                        (fn-auth-find-cred (fn-auth-session-pending as)
                                           (fn-auth-config-creds
                                            (fn-auth-session-config as))))
                       (fn-auth-session-subject as))
                (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "POST"))
           (equal (fn-auth-step-pinned as archive index verdicts config
                                       observation injection
                                       (list :command line))
                  (fn-auth-delegate-pinned as archive index verdicts config
                                           observation injection
                                           (list :command line))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step-pinned fn-auth-command fn-auth-gatedp
                            fn-auth-postingp fn-nntp-keywordp
                            fn-auth-tls-eventp)
                           (fn-auth-delegate-pinned fn-auth-single
                            fn-auth-sessionp fn-auth-find-cred
                            fn-auth-cred-postingp fn-auth-cred-principal
                            fn-auth-restricted-keywordp
                            fn-nntp-keyword-tokenp fn-nntp-upcase-keyword
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-command-arguments-at-mostp))
           :use ((:instance fn-auth-served-posting-cred-has-a-principal
                            (name (fn-auth-session-pending as)))))))

(deftheory fn-auth-served-vocabulary
  '((:d fn-auth-no-posting-credsp) (:d fn-auth-config-no-postersp)
    (:d fn-served-post-command-eventp)))

(in-theory (disable fn-auth-served-vocabulary))
