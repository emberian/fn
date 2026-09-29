;; fn: the peer role a login binds (PRF-049) and AUTHINFO SASL's way to it
;; (NNT-056): the step-level keystones over books/nntp-auth.lisp fn-auth-step.
;;
;; Split out of books/nntp-auth.lisp (lane sasl, 2026-09-28): each keystone
;; here unfolds the whole step, and with the SASL arms added the four of them
;; cost more prover steps than the rest of that book together; here they are
;; one narrow book the auth book's includers do not load.  The statements are
;; the ones books/nntp-auth.lisp carried, except that the PASS keystone now
;; names the SASL exchange as the other way in, and the new SASL keystone
;; says what that way installs.

(in-package "ACL2")
(include-book "nntp-auth")

(local (in-theory (disable (tau-system))))
(local (in-theory (enable fn-nntp-syntax-vocabulary
                          fn-nntp-session-vocabulary
                          fn-nntp-projection-vocabulary
                          fn-nntp-responses-vocabulary
                          fn-nntp-vocabulary
                          fn-nntp-post-vocabulary
                          fn-peer-vocabulary
                          fn-auth-vocabulary)))
(local (in-theory (disable fn-nntp-message-id-tail-is-true-listp)))
(local (in-theory (enable fn-inj-nth fn-inj-car fn-inj-cdr)))
(local (in-theory (disable fn-nntp-result-effects)))

; Local lemmas of books/nntp-auth.lisp these proofs read, restated here
; (local there, so they are not that book's exports).
(local (defthm fn-auth-configp-forward
  (implies (fn-auth-configp x)
           (and (booleanp (fn-auth-config-requiredp x))
                (booleanp (fn-auth-config-protected-onlyp x))
                (booleanp (fn-auth-config-tls-availablep x))
                (fn-auth-cred-listp (fn-auth-config-creds x))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-auth-configp) (fn-auth-cred-listp))))))

(local (defthm fn-auth-find-cred-principal-is-a-prin-id
  (implies (and (fn-auth-cred-listp creds) (fn-auth-find-cred name creds))
           (and (fn-prin-idp
                 (fn-auth-cred-principal (fn-auth-find-cred name creds)))
                (booleanp
                 (fn-auth-cred-postingp (fn-auth-find-cred name creds)))))
  :hints (("Goal" :in-theory (e/d (fn-auth-credp)
                                  (fn-prin-idp fn-authsec-verifierp
                                   fn-nntp-printable-tokenp
                                   fn-auth-find-cred fn-auth-cred-listp
                                   ; else the :use hypothesis is rewritten
                                   ; to T by this very rule and says nothing
                                   fn-auth-find-cred-is-a-cred))
           :use ((:instance fn-auth-find-cred-is-a-cred))))))

(local (defthm fn-auth-sessionp-forward-fields
  (implies (fn-auth-sessionp x)
           (and (fn-peer-sessionp (fn-auth-session-base x))
                (fn-auth-configp (fn-auth-session-config x))
                (fn-auth-pendingp (fn-auth-session-pending x))
                (or (null (fn-auth-session-subject x))
                    (fn-prin-idp (fn-auth-session-subject x)))
                (booleanp (fn-auth-session-tlsp x))
                (booleanp (fn-auth-session-handshakingp x))
                (fn-auth-ctxp (fn-auth-session-ctx x))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (disable fn-peer-sessionp fn-auth-configp
                                      fn-auth-pendingp fn-prin-idp)))))

(local (defthm fn-auth-pendingp-cases
  (and (fn-auth-pendingp nil)
       (implies (and (consp p) (true-listp p) (fn-nntp-printable-tokenp p))
                (fn-auth-pendingp p))
       (implies (fn-auth-redeem-statep p) (fn-auth-pendingp p))
       (implies (fn-sasl-statep p) (fn-auth-pendingp p)))
  :hints (("Goal" :in-theory (disable fn-nntp-printable-tokenp
                                      fn-auth-redeem-statep)))))

(local (defthm fn-auth-single-is-not-an-offer
  ; The 480, 440, 481 and 483 refusals are single replies, so none of them
  ; puts the wire into article mode.  With fn-nntp-result-effects closed
  ; this is no longer read off the term.
  (not (fn-post-offeredp (fn-auth-single as text)))
  :hints (("Goal" :in-theory (e/d (fn-auth-single fn-nntp-result-effects
                                   fn-nntp-single fn-nntp-make-result
                                   fn-post-offeredp
                                   fn-nntp-begin-article-effect)
                                  nil)))))

(local (defthm fn-auth-single-has-no-starttls
  ; A single reply is one (:reply ...) effect, so the handshake instruction
  ; is not in it.  With fn-nntp-result-effects closed this is no longer
  ; read off the term, and the two STARTTLS keystones are about exactly
  ; this membership.
  (not (member-equal '(:starttls) (fn-auth-single as text)))
  :hints (("Goal" :in-theory (e/d (fn-auth-single fn-nntp-result-effects
                                   fn-nntp-single fn-nntp-make-result
                                   fn-auth-starttls-effect)
                                  nil)))))

(local (defthm fn-auth-single-is-true-listp
  (true-listp (fn-auth-single as text))
  :hints (("Goal" :in-theory (e/d (fn-auth-single fn-nntp-result-effects
                                   fn-nntp-single fn-nntp-make-result)
                                  nil)))))

(local (defthm fn-auth-user-is-not-pass
  (implies (fn-nntp-keywordp keyword "USER")
           (not (fn-nntp-keywordp keyword "PASS")))
  :hints (("Goal" :in-theory (enable fn-nntp-keywordp)))))

(local (defthm fn-auth-token-argp-forward
  (implies (fn-auth-token-argp args)
           (and (consp args) (null (cdr args))
                (consp (car args)) (true-listp (car args))
                (fn-nntp-printable-tokenp (car args))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-auth-token-argp)
                                  (fn-nntp-printable-tokenp))))))

(local
 (defthm fn-auth-cfgp-gives-peer-rows
   (implies (fn-cfgp cfg)
            (fn-cfg-row-listp (fn-cfg-peers (fn-cfg-value cfg))))
   :hints (("Goal" :in-theory (enable fn-cfgp fn-cfg-valuep)))))

(local
 (defthm fn-auth-principal-peer-name-is-a-string
   (implies (and (fn-cfg-row-listp rows)
                 (fn-auth-principal-peer-name hex rows))
            (stringp (fn-auth-principal-peer-name hex rows)))
   :hints (("Goal" :induct (fn-auth-principal-peer-name hex rows)
            :in-theory (enable fn-auth-principal-peer-name fn-cfg-row-listp
                               fn-cfg-rowp fn-cfg-labelp fn-cfg-row-a
                               fn-record-ascii-stringp)))))

(local (defthm fn-auth-principal-match-is-a-string
  (or (null (fn-auth-principal-match principal cfg))
      (stringp (fn-auth-principal-match principal cfg)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-auth-principal-match)
                                  (fn-cfg-peer-find fn-digest-hex fn-cfgp))))))

(local (defthm fn-auth-principal-match-means-a-configuration
  (implies (fn-auth-principal-match principal cfg)
           (fn-cfgp cfg))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-auth-principal-match)
                                  (fn-cfg-peer-find fn-digest-hex fn-cfgp))))))

(local (defthm fn-auth-find-cred-name-is-a-token
  (implies (and (fn-auth-cred-listp creds)
                (consp (fn-auth-find-cred name creds)))
           (and (consp (fn-auth-cred-name (fn-auth-find-cred name creds)))
                (true-listp (fn-auth-cred-name (fn-auth-find-cred name creds)))
                (fn-nntp-printable-tokenp
                 (fn-auth-cred-name (fn-auth-find-cred name creds)))))
  :hints (("Goal" :use ((:instance fn-auth-find-cred-is-a-cred))
           :in-theory (e/d (fn-auth-credp)
                           (fn-auth-find-cred fn-auth-cred-listp
                            fn-auth-find-cred-is-a-cred
                            fn-nntp-printable-tokenp fn-prin-idp
                            fn-authsec-verifierp))))))

(local (defthm fn-auth-upcase-keeps-a-rest-byte
  (implies (fn-nntp-keyword-rest-bytep (fn-nntp-upcase-byte b))
           (fn-nntp-keyword-rest-bytep b))
  :hints (("Goal" :in-theory (enable fn-nntp-keyword-rest-bytep
                                     fn-nntp-keyword-first-bytep
                                     fn-nntp-upcase-byte)))))

(local (defthm fn-auth-upcase-keyword-is-consp-exactly-when-its-argument-is
  (equal (consp (fn-nntp-upcase-keyword x)) (consp x))
  :hints (("Goal" :in-theory (enable fn-nntp-upcase-keyword)))))

(local (defthm fn-auth-upcase-keeps-a-keyword-tail
  (implies (fn-nntp-keyword-tailp (fn-nntp-upcase-keyword x))
           (fn-nntp-keyword-tailp x))
  :hints (("Goal" :in-theory (enable fn-nntp-keyword-tailp
                                     fn-nntp-upcase-keyword)))))

(local (defthm fn-auth-upcase-keeps-a-keyword-token
  (implies (fn-nntp-keyword-tokenp (fn-nntp-upcase-keyword x))
           (fn-nntp-keyword-tokenp x))
  :hints (("Goal" :in-theory (e/d (fn-nntp-keyword-tokenp
                                   fn-nntp-upcase-keyword
                                   fn-nntp-keyword-first-bytep
                                   fn-nntp-upcase-byte)
                                  (fn-nntp-keyword-tailp))))))

(local (defthm fn-auth-keyword-match-is-a-keyword-token
  (implies (and (fn-nntp-keywordp keyword text)
                (fn-nntp-keyword-tokenp (fn-nntp-string-octets text)))
           (fn-nntp-keyword-tokenp keyword))
  :hints (("Goal" :in-theory (e/d (fn-nntp-keywordp)
                                  (fn-nntp-keyword-tokenp
                                   fn-nntp-upcase-keyword
                                   fn-nntp-string-octets))
           :use ((:instance fn-auth-upcase-keeps-a-keyword-token
                            (x keyword)))))))

(local (defthm fn-auth-a-keyword-token-car-has-a-cons
  (implies (fn-nntp-keyword-tokenp (car x)) (consp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-nntp-keyword-tokenp)))))

; -----------------------------------------------------------------------------
; THE PEER ROLE A LOGIN BINDS (PRF-049).
;
; A connection the owner opens through fn-ocfg-open (host/owner-host.lisp
; fn-owner-open) is a reader; books/owner-config.lisp
; fn-ocfg-open-begins-unbound says so of every open, whatever the owner's
; other connections have done.  The only transition that gives a reader a
; peer role is AUTHINFO PASS, and only for a principal the pinned
; configuration binds to exactly one peer record (fn-auth-principal-match).
; Three keystones over fn-auth-step, the function books/served.lisp
; fn-served-dispatch calls and host/owner-host.lisp fn-owner-chunk reaches
; through fn-own-read and fn-served-step:
;
;   fn-auth-step-binds-a-peer-role-only-by-a-principal-login   (only way in)
;   fn-auth-step-principal-login-binds-exactly-the-unique-match (the way in)
;   fn-auth-step-starttls-clears-a-principal-role               (the way out)
;
; Protected-only is not restated here: fn-auth-step-protected-only-refuses-
; authinfo-before-tls (PRF-031) says the session is unchanged by any AUTHINFO
; before TLS, and the first keystone's fourth conjunct says the same thing
; from the other side -- no step whatever binds a role on a cleartext
; connection under that policy.

; The peer half of fn-peer-step never moves the peer name: every branch
; rebuilds the session with fn-peer-with-base or fn-peer-with-transfer.
(local (defthm fn-auth-peer-step-keeps-the-peer
  (equal (fn-peer-session-peer
          (fn-post-result-session
           (fn-peer-step ps archive config observation injection wire-event fn-arena)))
         (fn-peer-session-peer ps))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-peer-step fn-peer-command fn-peer-delegate
                            fn-peer-with-base fn-peer-with-transfer)
                           (fn-nntp-post-step fn-peer-sessionp
                            fn-peer-decide-offer fn-peer-single
                            fn-peer-echo-reply fn-peer-msgid-argp
                            fn-peer-capability-lines fn-peer-check-code
                            fn-peer-ihave-offer-line
                            fn-nntp-multi fn-nntp-keywordp
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp))))))

;; AUTHINFO SASL's binding: the SASL transitions bind a role only through
;; fn-auth-sasl-finish's success arm, which is PASS's acceptance: the found
;; credential's principal as the subject, its login kept, and
;; fn-auth-bind-principal-peer of that principal.
(local (defthm fn-auth-sasl-refuse-keeps-the-role
  (equal (fn-auth-session-peer (fn-post-result-session (fn-auth-sasl-refuse as text)))
         (fn-auth-session-peer as))
  :hints (("Goal" :in-theory (enable fn-auth-sasl-refuse fn-auth-session-peer)))))

(defthm fn-auth-sasl-finish-binds-only-on-success
  (implies (and (not (fn-auth-session-peer as))
                (fn-auth-session-peer
                 (fn-post-result-session (fn-auth-sasl-finish as st response))))
           (let* ((acfg (fn-auth-session-config as))
                  (ctx (fn-auth-session-ctx as))
                  (cred (fn-auth-find-cred (fn-sasl-response-login st response)
                                           (fn-auth-config-creds acfg)))
                  (next (fn-post-result-session
                         (fn-auth-sasl-finish as st response))))
             (and (consp cred)
                  (fn-sasl-successp
                   (fn-sasl-step st response (fn-auth-cred-secret cred)
                                 (fn-auth-ctx-seed ctx) (fn-auth-ctx-binding ctx)))
                  (equal (fn-auth-session-pending next) (fn-auth-cred-name cred))
                  (equal (fn-auth-session-subject next)
                         (fn-auth-cred-principal cred))
                  (equal (fn-auth-session-peer next)
                         (fn-auth-principal-match
                          (fn-auth-cred-principal cred)
                          (fn-peer-session-cfg (fn-auth-session-base as))))
                  (fn-auth-principal-rolep next))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-sasl-finish fn-auth-bind-principal-peer
                            fn-auth-with-base fn-auth-session-peer
                            fn-auth-principal-rolep fn-auth-principal-match
                            fn-sasl-successp fn-sasl-outcome-kind
                            fn-auth-sasl-refuse)
                           (fn-auth-single fn-auth-find-cred fn-sasl-step
                            fn-sasl-response-login fn-auth-sasl-effects
                            fn-auth-sasl-line-okp
                            fn-nntp-single fn-cfg-peer-find fn-cfgp
                            fn-digest-hex fn-node-statep)))))

(local (defthm fn-auth-sasl-command-binds-only-on-success
  (implies (and (not (fn-auth-session-peer as))
                (fn-auth-session-peer
                 (fn-post-result-session (fn-auth-sasl-command as margs))))
           (fn-auth-session-peer
            (fn-post-result-session
             (fn-auth-sasl-finish
              as (fn-sasl-initial-state (fn-sasl-mech (car margs)))
              (mv-nth 1 (fn-auth-sasl-decode (cadr margs)))))))
  :hints (("Goal" :in-theory (e/d (fn-auth-sasl-command fn-auth-session-peer
                                   fn-auth-sasl-refuse)
                                  (fn-auth-sasl-finish
                                   fn-auth-sasl-decode fn-sasl-mech
                                   fn-sasl-offeredp fn-sasl-initial-state))))))

(local (defthm fn-auth-authinfo-binds-only-on-an-accepted-pass
  (implies (and (not (fn-auth-session-peer as))
                (fn-auth-session-peer
                 (fn-post-result-session (fn-auth-authinfo as args)))
                (not (fn-nntp-keywordp (car args) "SASL")))
           (and (not (fn-auth-session-subject as))
                (not (and (fn-auth-config-protected-onlyp
                           (fn-auth-session-config as))
                          (not (fn-auth-session-tlsp as))))
                (fn-nntp-keywordp (car args) "PASS")
                (fn-auth-token-argp (cdr args))
                (fn-auth-session-pending as)
                (fn-auth-checkp (fn-auth-find-cred
                                 (fn-auth-session-pending as)
                                 (fn-auth-config-creds
                                  (fn-auth-session-config as)))
                                (car (cdr args)))
                (equal (fn-auth-session-subject
                        (fn-post-result-session (fn-auth-authinfo as args)))
                       (fn-auth-cred-principal
                        (fn-auth-find-cred (fn-auth-session-pending as)
                                           (fn-auth-config-creds
                                            (fn-auth-session-config as)))))
                (equal (fn-auth-session-peer
                        (fn-post-result-session (fn-auth-authinfo as args)))
                       (fn-auth-principal-match
                        (fn-auth-cred-principal
                         (fn-auth-find-cred (fn-auth-session-pending as)
                                            (fn-auth-config-creds
                                             (fn-auth-session-config as))))
                        (fn-peer-session-cfg (fn-auth-session-base as))))
                (fn-auth-principal-rolep
                 (fn-post-result-session (fn-auth-authinfo as args)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-authinfo fn-auth-bind-principal-peer
                            fn-auth-with-base fn-auth-session-peer
                            fn-auth-principal-rolep fn-auth-principal-match)
                           (fn-auth-single fn-auth-find-cred fn-auth-checkp
                            fn-auth-token-argp fn-nntp-keywordp
                            fn-nntp-single fn-cfg-peer-find fn-cfgp
                            fn-auth-sasl-command
                            fn-digest-hex
                            fn-node-statep))))))

(local (defthm fn-auth-configured-session-has-a-node
  (implies (and (fn-peer-sessionp x)
                (fn-cfgp (fn-peer-session-cfg x)))
           (fn-node-statep (fn-peer-session-node x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d ((:d fn-peer-sessionp))
                                  ((:d fn-post-sessionp) (:d fn-peer-transferp)
                                   (:d fn-node-statep) (:d fn-cfgp)))))))

(local (defthm fn-auth-authinfo-accepted-pass-binds-the-match
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-peer as))
                (not (fn-auth-session-subject as))
                (not (and (fn-auth-config-protected-onlyp
                           (fn-auth-session-config as))
                          (not (fn-auth-session-tlsp as))))
                (fn-nntp-keywordp (car args) "PASS")
                (fn-auth-token-argp (cdr args))
                (fn-auth-session-pending as)
                (fn-auth-checkp (fn-auth-find-cred
                                 (fn-auth-session-pending as)
                                 (fn-auth-config-creds
                                  (fn-auth-session-config as)))
                                (car (cdr args))))
           (and (equal (fn-post-result-effects (fn-auth-authinfo as args))
                       (fn-auth-single as "281 authentication accepted"))
                (equal (fn-auth-session-subject
                        (fn-post-result-session (fn-auth-authinfo as args)))
                       (fn-auth-cred-principal
                        (fn-auth-find-cred (fn-auth-session-pending as)
                                           (fn-auth-config-creds
                                            (fn-auth-session-config as)))))
                (equal (fn-auth-session-peer
                        (fn-post-result-session (fn-auth-authinfo as args)))
                       (fn-auth-principal-match
                        (fn-auth-cred-principal
                         (fn-auth-find-cred (fn-auth-session-pending as)
                                            (fn-auth-config-creds
                                             (fn-auth-session-config as))))
                        (fn-peer-session-cfg (fn-auth-session-base as))))))
  :hints (("Goal"
           :do-not-induct t
           ; The match stays closed: the conclusion names it, and the node
           ; the binding tests comes from the configuration a match was
           ; read out of (fn-auth-principal-match-means-a-configuration).
           :in-theory (e/d (fn-auth-authinfo fn-auth-bind-principal-peer
                            fn-auth-with-base fn-auth-session-peer)
                           (fn-auth-sessionp fn-auth-pendingp fn-auth-single fn-auth-find-cred fn-auth-checkp
                            fn-auth-token-argp fn-nntp-keywordp
                            fn-nntp-single fn-cfg-peer-find fn-cfgp
                            fn-auth-principal-match fn-auth-sasl-command
                            fn-digest-hex fn-peer-sessionp fn-auth-configp
                            fn-nntp-printable-tokenp fn-prin-idp
                            fn-node-statep))))))

(local (defthm fn-auth-starttls-handshake-clears-a-principal-role
  (implies (and (not (fn-auth-session-handshakingp as))
                (fn-auth-session-handshakingp
                 (fn-post-result-session (fn-auth-starttls as args))))
           (and (null (fn-auth-session-subject
                       (fn-post-result-session (fn-auth-starttls as args))))
                (null (fn-auth-session-pending
                       (fn-post-result-session (fn-auth-starttls as args))))
                (not (fn-auth-principal-rolep
                      (fn-post-result-session (fn-auth-starttls as args))))
                (equal (fn-auth-session-peer
                        (fn-post-result-session (fn-auth-starttls as args)))
                       (if (fn-auth-principal-rolep as)
                           nil
                         (fn-auth-session-peer as)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-starttls fn-auth-clear-principal-peer
                            fn-auth-with-base fn-auth-session-peer
                            fn-auth-principal-rolep)
                           (fn-auth-single fn-nntp-single fn-cfg-peer-find
                            fn-cfgp))))))

(local (defthm fn-auth-starttls-keeps-a-reader
  (implies (not (fn-auth-session-peer as))
           (not (fn-auth-session-peer
                 (fn-post-result-session (fn-auth-starttls as args)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-starttls fn-auth-clear-principal-peer
                            fn-auth-with-base fn-auth-session-peer
                            fn-auth-principal-rolep)
                           (fn-auth-single fn-nntp-single fn-cfg-peer-find
                            fn-cfgp))))))

(local (defthm fn-auth-delegate-keeps-the-role-and-the-handshake
  (and (equal (fn-auth-session-peer
               (fn-post-result-session
                (fn-auth-delegate as archive config observation injection
                                  wire-event fn-arena)))
              (fn-auth-session-peer as))
       (equal (fn-auth-session-handshakingp
               (fn-post-result-session
                (fn-auth-delegate as archive config observation injection
                                  wire-event fn-arena)))
              (fn-auth-session-handshakingp as)))
  :hints (("Goal"
           :in-theory (e/d (fn-auth-delegate fn-auth-with-base
                            fn-auth-session-peer)
                           (fn-peer-step))))))

(local (defthm fn-auth-sasl-finish-keeps-the-handshake
  (equal (fn-auth-session-handshakingp
          (fn-post-result-session (fn-auth-sasl-finish as st response)))
         (fn-auth-session-handshakingp as))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-sasl-finish fn-auth-bind-principal-peer
                            fn-auth-with-base fn-auth-sasl-refuse)
                           (fn-auth-single fn-auth-find-cred fn-sasl-step
                            fn-sasl-response-login fn-auth-sasl-effects
                            fn-auth-sasl-line-okp
                            fn-nntp-single fn-auth-principal-match
                            fn-node-statep))))))

(local (defthm fn-auth-sasl-command-keeps-the-handshake
  (equal (fn-auth-session-handshakingp
          (fn-post-result-session (fn-auth-sasl-command as margs)))
         (fn-auth-session-handshakingp as))
  :hints (("Goal"
           :in-theory (e/d (fn-auth-sasl-command fn-auth-sasl-refuse)
                           (fn-auth-sasl-finish fn-auth-sasl-decode fn-auth-single
                            fn-sasl-mech fn-sasl-offeredp))))))

(local (defthm fn-auth-sasl-continue-keeps-the-handshake
  (equal (fn-auth-session-handshakingp
          (fn-post-result-session (fn-auth-sasl-continue as line)))
         (fn-auth-session-handshakingp as))
  :hints (("Goal"
           :in-theory (e/d (fn-auth-sasl-continue fn-auth-sasl-refuse)
                           (fn-auth-sasl-finish fn-auth-sasl-decode
                            fn-auth-single))))))

(local (defthm fn-auth-install-context-keeps-the-handshake
  (equal (fn-auth-session-handshakingp
          (fn-post-result-session (fn-auth-install-context as wire-event)))
         (fn-auth-session-handshakingp as))
  :hints (("Goal" :in-theory (enable fn-auth-install-context)))))

(local (defthm fn-auth-authinfo-keeps-the-handshake
  (equal (fn-auth-session-handshakingp
          (fn-post-result-session (fn-auth-authinfo as args)))
         (fn-auth-session-handshakingp as))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-authinfo fn-auth-bind-principal-peer
                            fn-auth-with-base)
                           (fn-auth-single fn-auth-find-cred fn-auth-checkp
                            fn-auth-token-argp fn-nntp-keywordp
                            fn-nntp-single fn-auth-principal-match
                            fn-auth-sasl-command
                            fn-node-statep))))))

(local (defthmd fn-auth-session-peer-folds
  (equal (fn-peer-session-peer (fn-auth-session-base as))
         (fn-auth-session-peer as))))


(local (defthm fn-auth-install-context-keeps-the-role
  (equal (fn-auth-session-peer
          (fn-post-result-session (fn-auth-install-context as wire-event)))
         (fn-auth-session-peer as))
  :hints (("Goal" :in-theory (enable fn-auth-install-context
                                     fn-auth-session-peer)))))

; KEYSTONE.  The only way a reader becomes a peer.
;
; No hypothesis about the session or the event beyond the role change
; itself: for ANY session and ANY wire event, if the step's session has a
; peer role and the session it was given had none, then the event was an
; AUTHINFO PASS command line, sent on a well-formed, non-handshaking,
; unauthenticated connection whose channel the policy accepts, after a
; USER, whose one-token secret checks against the cached name's stored
; verifier; the step installed that credential's principal as the subject;
; the role it bound is fn-auth-principal-match of that principal under the
; configuration pinned into the connection -- the one peer whose record says
; (:principal HEX) and the only auth-principal row naming HEX -- and the role
; is principal-derived, so the next keystone's STARTTLS clears it.
;
; Consequences read straight off it: a principal with no matching row
; (mismatch) or two (duplicate) never gains a role on any step, since the
; match is then nil; a protected-only connection without TLS never gains
; one; a delegated reader command, a CAPABILITIES, a USER, a failed PASS, a
; STARTTLS and the handshake re-entry never do.
;
; Two hypotheses, each with a violating value in
; tests/acl2/nntp-auth-teeth-tests.lisp.
(defthm fn-auth-step-binds-a-peer-role-only-by-a-principal-login
  (implies (and (not (fn-auth-session-peer as))
                (fn-auth-session-peer
                 (fn-post-result-session
                  (fn-auth-step as archive config observation injection
                                wire-event fn-arena)))
                ; The other way in is SASL's, the next keystone.
                (not (fn-auth-sasl-waitingp as))
                (not (fn-nntp-keywordp (cadr (fn-nntp-tokenize (cadr wire-event)))
                                       "SASL")))
           (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (not (fn-auth-session-subject as))
                (not (and (fn-auth-config-protected-onlyp
                           (fn-auth-session-config as))
                          (not (fn-auth-session-tlsp as))))
                (equal (car wire-event) :command)
                (fn-nntp-keywordp (car (fn-nntp-tokenize (cadr wire-event)))
                                  "AUTHINFO")
                (fn-nntp-keywordp (cadr (fn-nntp-tokenize (cadr wire-event)))
                                  "PASS")
                (fn-auth-token-argp (cddr (fn-nntp-tokenize (cadr wire-event))))
                (fn-auth-session-pending as)
                (fn-auth-checkp
                 (fn-auth-find-cred (fn-auth-session-pending as)
                                    (fn-auth-config-creds
                                     (fn-auth-session-config as)))
                 (caddr (fn-nntp-tokenize (cadr wire-event))))
                (equal (fn-auth-session-subject
                        (fn-post-result-session
                         (fn-auth-step as archive config observation injection
                                       wire-event fn-arena)))
                       (fn-auth-cred-principal
                        (fn-auth-find-cred (fn-auth-session-pending as)
                                           (fn-auth-config-creds
                                            (fn-auth-session-config as)))))
                (equal (fn-auth-session-peer
                        (fn-post-result-session
                         (fn-auth-step as archive config observation injection
                                       wire-event fn-arena)))
                       (fn-auth-principal-match
                        (fn-auth-cred-principal
                         (fn-auth-find-cred (fn-auth-session-pending as)
                                            (fn-auth-config-creds
                                             (fn-auth-session-config as))))
                        (fn-peer-session-cfg (fn-auth-session-base as))))
                (fn-auth-principal-rolep
                 (fn-post-result-session
                  (fn-auth-step as archive config observation injection
                                wire-event fn-arena)))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step fn-auth-command fn-auth-tls-eventp fn-auth-session-peer-folds
                            fn-auth-tls-established)
                           (fn-auth-restricted-keywordp fn-auth-restricted-keyword-is-a-keyword-token
                            fn-auth-upcase-keeps-a-keyword-token
                            fn-peer-step fn-auth-delegate fn-auth-single
                            fn-auth-authinfo fn-auth-starttls
                            fn-auth-sessionp fn-auth-session-peer
                            fn-auth-principal-rolep fn-auth-principal-match
                            fn-auth-gatedp fn-auth-postingp
                            fn-auth-find-cred fn-auth-checkp
                            fn-auth-capability-lines-for-peer
                            fn-auth-peer-record fn-nntp-multi
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-keyword-tokenp fn-nntp-keywordp
                            fn-nntp-command-arguments-at-mostp
                            fn-auth-sasl-waitingp fn-auth-sasl-continue
                            fn-auth-install-context
                            fn-auth-authinfo-binds-only-on-an-accepted-pass))
           :use ((:instance fn-auth-authinfo-binds-only-on-an-accepted-pass
                            (args (cdr (fn-nntp-tokenize
                                        (cadr wire-event)))))))))

(local (defthm fn-auth-find-cred-finds-its-name
  (implies (fn-auth-find-cred name creds)
           (equal (fn-auth-cred-name (fn-auth-find-cred name creds)) name))
  :hints (("Goal" :in-theory (enable fn-auth-find-cred)))))

(local (defthm fn-auth-find-cred-of-a-found-name
  (implies (fn-auth-find-cred name creds)
           (equal (fn-auth-find-cred (fn-auth-cred-name
                                      (fn-auth-find-cred name creds))
                                     creds)
                  (fn-auth-find-cred name creds)))
  :hints (("Goal" :in-theory (disable fn-auth-find-cred)))))

(local (defthm fn-auth-sasl-finish-binds-a-found-credential
  (implies (and (not (fn-auth-session-peer as))
                (fn-auth-session-peer
                 (fn-post-result-session (fn-auth-sasl-finish as st response))))
           (let* ((creds (fn-auth-config-creds (fn-auth-session-config as)))
                  (next (fn-post-result-session
                         (fn-auth-sasl-finish as st response)))
                  (cred (fn-auth-find-cred (fn-auth-session-pending next) creds)))
             (and (consp cred)
                  (equal (fn-auth-session-subject next)
                         (fn-auth-cred-principal cred))
                  (equal (fn-auth-session-peer next)
                         (fn-auth-principal-match
                          (fn-auth-session-subject next)
                          (fn-peer-session-cfg (fn-auth-session-base as))))
                  (fn-auth-principal-rolep next))))
  :hints (("Goal" :use ((:instance fn-auth-sasl-finish-binds-only-on-success))
           :in-theory (disable fn-auth-sasl-finish-binds-only-on-success
                               fn-auth-sasl-finish fn-auth-find-cred
                               fn-auth-principal-rolep fn-auth-session-peer
                               fn-auth-principal-match fn-sasl-step
                               fn-sasl-response-login)))))

(local (defthm fn-auth-sasl-continue-binds-only-through-finish
  (implies (and (not (fn-auth-session-peer as))
                (fn-auth-session-peer
                 (fn-post-result-session (fn-auth-sasl-continue as line))))
           (and (not (fn-auth-session-subject as))
                (not (and (fn-auth-config-protected-onlyp
                           (fn-auth-session-config as))
                          (not (fn-auth-session-tlsp as))))
                (equal (fn-post-result-session (fn-auth-sasl-continue as line))
                       (fn-post-result-session
                        (fn-auth-sasl-finish
                         as (fn-auth-session-pending as)
                         (mv-nth 1 (fn-auth-sasl-decode line)))))))
  :hints (("Goal" :in-theory (e/d (fn-auth-sasl-continue fn-auth-sasl-refuse
                                   fn-auth-session-peer)
                                  (fn-auth-sasl-finish fn-auth-sasl-decode
                                   fn-auth-single))))))

(local (defthm fn-auth-sasl-is-not-user-or-pass
  (implies (fn-nntp-keywordp keyword "SASL")
           (and (not (fn-nntp-keywordp keyword "USER"))
                (not (fn-nntp-keywordp keyword "PASS"))))
  :hints (("Goal" :in-theory (enable fn-nntp-keywordp)))))

(local (defthm fn-auth-authinfo-sasl-binds-only-through-finish
  (implies (and (not (fn-auth-session-peer as))
                (fn-auth-session-peer
                 (fn-post-result-session (fn-auth-authinfo as args)))
                (fn-nntp-keywordp (car args) "SASL"))
           (and (not (fn-auth-session-subject as))
                (not (and (fn-auth-config-protected-onlyp
                           (fn-auth-session-config as))
                          (not (fn-auth-session-tlsp as))))
                (equal (fn-post-result-session (fn-auth-authinfo as args))
                       (fn-post-result-session
                        (fn-auth-sasl-finish
                         as (fn-sasl-initial-state (fn-sasl-mech (cadr args)))
                         (mv-nth 1 (fn-auth-sasl-decode (caddr args))))))))
  :hints (("Goal" :in-theory (e/d (fn-auth-authinfo fn-auth-sasl-command
                                   fn-auth-sasl-refuse fn-auth-session-peer)
                                  (fn-auth-sasl-finish fn-auth-sasl-decode
                                   fn-auth-single fn-sasl-mech
                                   fn-sasl-offeredp fn-sasl-initial-state
                                   fn-nntp-keywordp fn-auth-token-argp
                                   fn-auth-find-cred fn-auth-checkp
                                   fn-auth-bind-principal-peer))))))

; KEYSTONE (NNT-056).  The SASL way a reader becomes a peer.  If a step that
; begins an AUTHINFO SASL exchange or answers a kept one gives a reader a
; peer role, the connection was well formed, not handshaking, not
; authenticated, on a channel the policy accepts, and the step installed as
; subject the principal of the credential the snapshot holds under the login
; it now keeps, bound the role fn-auth-principal-match of that principal
; under the pinned configuration, and the role is principal-derived (so
; STARTTLS clears it).  That the exchange succeeded is
; fn-auth-sasl-finish-binds-only-on-success: the credential's verifier passed
; books/sasl.lisp's check.  Together with the previous keystone: AUTHINFO
; PASS and AUTHINFO SASL are the only two ways in.
(defthm fn-auth-step-binds-a-peer-role-by-sasl-only-to-a-found-credential
  (implies (and (not (fn-auth-session-peer as))
                (fn-auth-session-peer
                 (fn-post-result-session
                  (fn-auth-step as archive config observation injection
                                wire-event fn-arena)))
                (or (fn-auth-sasl-waitingp as)
                    (fn-nntp-keywordp (cadr (fn-nntp-tokenize (cadr wire-event)))
                                      "SASL")))
           (let* ((next (fn-post-result-session
                         (fn-auth-step as archive config observation injection
                                       wire-event fn-arena)))
                  (cred (fn-auth-find-cred
                         (fn-auth-session-pending next)
                         (fn-auth-config-creds (fn-auth-session-config as)))))
             (and (fn-auth-sessionp as)
                  (not (fn-auth-session-handshakingp as))
                  (not (fn-auth-session-subject as))
                  (not (and (fn-auth-config-protected-onlyp
                             (fn-auth-session-config as))
                            (not (fn-auth-session-tlsp as))))
                  (equal (car wire-event) :command)
                  (consp cred)
                  (equal (fn-auth-session-subject next)
                         (fn-auth-cred-principal cred))
                  (equal (fn-auth-session-peer next)
                         (fn-auth-principal-match
                          (fn-auth-session-subject next)
                          (fn-peer-session-cfg (fn-auth-session-base as))))
                  (fn-auth-principal-rolep next))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :cases ((fn-auth-sasl-waitingp as))
           :in-theory (e/d (fn-auth-step fn-auth-command fn-auth-tls-eventp
                            fn-auth-session-peer-folds fn-auth-tls-established)
                           (fn-peer-step fn-auth-delegate fn-auth-single
                            fn-auth-authinfo fn-auth-starttls fn-auth-xredeem
                            fn-auth-sessionp fn-auth-session-peer
                            fn-auth-principal-rolep fn-auth-principal-match
                            fn-auth-gatedp fn-auth-postingp
                            fn-auth-find-cred fn-auth-checkp
                            fn-auth-capability-lines-for-peer
                            fn-auth-peer-record fn-nntp-multi
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-keyword-tokenp fn-nntp-keywordp
                            fn-nntp-command-arguments-at-mostp
                            fn-auth-sasl-continue fn-auth-sasl-finish
                            fn-auth-sasl-decode fn-auth-install-context
                            fn-auth-restricted-keywordp
                            fn-auth-restricted-keyword-is-a-keyword-token
                            fn-auth-upcase-keeps-a-keyword-token
                            fn-sasl-mech fn-sasl-initial-state
                            fn-auth-sasl-waitingp)))
          ("Subgoal 2"
           :use ((:instance fn-auth-authinfo-sasl-binds-only-through-finish
                            (args (cdr (fn-nntp-tokenize (cadr wire-event)))))
                 (:instance fn-auth-sasl-finish-binds-a-found-credential
                            (st (fn-sasl-initial-state
                                 (fn-sasl-mech (cadr (cdr (fn-nntp-tokenize
                                                           (cadr wire-event)))))))
                            (response (mv-nth 1 (fn-auth-sasl-decode
                                                 (caddr (cdr (fn-nntp-tokenize
                                                              (cadr wire-event))))))))))
          ("Subgoal 1"
           :use ((:instance fn-auth-sasl-continue-binds-only-through-finish
                            (line (cadr wire-event)))
                 (:instance fn-auth-sasl-finish-binds-a-found-credential
                            (st (fn-auth-session-pending as))
                            (response (mv-nth 1 (fn-auth-sasl-decode
                                                 (cadr wire-event)))))))))

; The line-length fact the next keystone needs so that it does not carry
; `fn-nntp-command-arguments-at-mostp' as a hypothesis no value could
; violate: a command line inside RFC 3977 section 3.1's 510 octets that
; tokenizes to AUTHINFO PASS <one token> has a secret of at most 496
; octets, inside the 497-octet argument bound.  `fn-auth-token-span' counts
; each token with one separator; the tokenizer consumes at least that.
(local (defun fn-auth-token-span (toks)
  (if (consp toks)
      (+ 1 (len (car toks)) (fn-auth-token-span (cdr toks)))
    0)))

(local (defthm fn-auth-token-span-of-append
  (equal (fn-auth-token-span (append a b))
         (+ (fn-auth-token-span a) (fn-auth-token-span b)))))

(local (defthm fn-auth-token-span-of-rev
  (equal (fn-auth-token-span (rev a)) (fn-auth-token-span a))))

(local (defthm fn-auth-token-span-of-reverse
  (equal (fn-auth-token-span (reverse a)) (fn-auth-token-span a))))

(local (defthm fn-auth-tokenize-aux-span
  (<= (fn-auth-token-span (fn-nntp-tokenize-aux xs word-rev words-rev))
      (+ 1 (len xs) (len word-rev) (fn-auth-token-span words-rev)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-nntp-tokenize-aux xs word-rev words-rev)
           :in-theory (enable fn-nntp-tokenize-aux)))))

(local (defthm fn-auth-tokenize-span
  (<= (fn-auth-token-span (fn-nntp-tokenize line)) (+ 1 (len line)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-nntp-tokenize)))))

(local (defthm fn-auth-len-of-upcase-keyword
  (equal (len (fn-nntp-upcase-keyword x)) (len x))
  :hints (("Goal" :in-theory (enable fn-nntp-upcase-keyword)))))

(local (defthm fn-auth-keyword-len
  (implies (fn-nntp-keywordp k text)
           (equal (len k) (len (fn-nntp-string-octets text))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-nntp-keywordp)
                                  (fn-nntp-upcase-keyword
                                   fn-auth-len-of-upcase-keyword))
           :use ((:instance fn-auth-len-of-upcase-keyword (x k)))))))

(local (defthm fn-auth-cbor-at-mostp-len
  (implies (fn-cbor-at-mostp xs bound) (<= (len xs) (nfix bound)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-cbor-at-mostp)))))

(local (defthmd fn-auth-pass-line-arguments-are-in-bounds
  (implies (and (fn-nntp-command-inputp line)
                (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "AUTHINFO")
                (fn-nntp-keywordp (cadr (fn-nntp-tokenize line)) "PASS")
                (fn-auth-token-argp (cddr (fn-nntp-tokenize line))))
           (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-auth-tokenize-span))
           :expand ((fn-auth-token-span (fn-nntp-tokenize line))
                    (fn-auth-token-span (cdr (fn-nntp-tokenize line)))
                    (fn-auth-token-span (cddr (fn-nntp-tokenize line))))
           :in-theory (e/d (fn-nntp-command-arguments-at-mostp
                            fn-nntp-argument-tokens
                            fn-nntp-each-token-at-mostp
                            fn-nntp-command-inputp fn-auth-token-argp)
                           (fn-nntp-tokenize fn-nntp-keywordp
                            fn-auth-tokenize-span fn-nntp-command-linep
                            fn-nntp-contains-bomp fn-cbor-at-mostp
                            fn-nntp-printable-tokenp))))))

; KEYSTONE.  The way in: an accepted PASS binds exactly the unique match.
;
; On a reader connection that is well-formed, not handshaking,
; unauthenticated and whose channel the policy accepts, an AUTHINFO PASS
; line after a USER whose secret checks is answered 281, installs the
; credential's principal, and leaves the connection with the peer role
; fn-auth-principal-match computes: the configured peer when exactly one
; auth-principal row names the principal's digest and that peer's record
; says (:principal digest), and no role -- a reader, still authenticated --
; when there are none (mismatch) or several (duplicate).  RFC 4643 section
; 2.3.2's 281 is the same in every case: whether the login also names a
; peer is not disclosed on the wire.
;
; Eleven hypotheses, each with a violating value in
; tests/acl2/nntp-auth-teeth-tests.lisp.
(defthm fn-auth-step-principal-login-binds-exactly-the-unique-match
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (not (fn-zc-activep (fn-auth-session-compress as)))
                (not (fn-auth-sasl-waitingp as))
                (not (fn-auth-session-peer as))
                (not (fn-auth-session-subject as))
                (not (and (fn-auth-config-protected-onlyp
                           (fn-auth-session-config as))
                          (not (fn-auth-session-tlsp as))))
                (fn-nntp-command-inputp line)
                (fn-nntp-keywordp (car (fn-nntp-tokenize line)) "AUTHINFO")
                (fn-nntp-keywordp (cadr (fn-nntp-tokenize line)) "PASS")
                (fn-auth-token-argp (cddr (fn-nntp-tokenize line)))
                (fn-auth-session-pending as)
                (fn-auth-checkp
                 (fn-auth-find-cred (fn-auth-session-pending as)
                                    (fn-auth-config-creds
                                     (fn-auth-session-config as)))
                 (caddr (fn-nntp-tokenize line))))
           (and (equal (fn-post-result-effects
                        (fn-auth-step as archive config observation injection
                                      (list :command line) fn-arena))
                       (fn-auth-single as "281 authentication accepted"))
                (equal (fn-auth-session-subject
                        (fn-post-result-session
                         (fn-auth-step as archive config observation injection
                                       (list :command line) fn-arena)))
                       (fn-auth-cred-principal
                        (fn-auth-find-cred (fn-auth-session-pending as)
                                           (fn-auth-config-creds
                                            (fn-auth-session-config as)))))
                (equal (fn-auth-session-peer
                        (fn-post-result-session
                         (fn-auth-step as archive config observation injection
                                       (list :command line) fn-arena)))
                       (fn-auth-principal-match
                        (fn-auth-cred-principal
                         (fn-auth-find-cred (fn-auth-session-pending as)
                                            (fn-auth-config-creds
                                             (fn-auth-session-config as))))
                        (fn-peer-session-cfg (fn-auth-session-base as))))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step fn-auth-command fn-auth-gatedp
                            fn-auth-tls-eventp fn-auth-restricted-keywordp
                            fn-nntp-keywordp)
                           (fn-peer-step fn-auth-delegate fn-auth-single
                            fn-auth-authinfo fn-auth-starttls
                            fn-auth-sessionp fn-auth-session-peer
                            fn-auth-principal-match fn-auth-find-cred
                            fn-auth-checkp fn-auth-token-argp
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp
                            fn-auth-authinfo-accepted-pass-binds-the-match
                            fn-auth-sasl-continue fn-auth-install-context))
           :use ((:instance fn-auth-authinfo-accepted-pass-binds-the-match
                            (args (cdr (fn-nntp-tokenize line))))
                 (:instance fn-auth-pass-line-arguments-are-in-bounds)))))

; KEYSTONE.  The way out: STARTTLS clears a principal-derived role.
;
; For ANY session and ANY wire event: if the step entered the TLS handshake
; (the session was not handshaking and is now), the new session carries no
; subject, no cached name and no principal-derived role, and its peer role
; is the old one exactly when that role was NOT principal-derived.  So a
; peer the operator configured by source address (fn-own-open-peer) keeps
; its role across the handshake, and a role a login bound -- principal-
; derived by the first keystone -- is gone before the first octet of the
; handshake, as RFC 4642 section 2.2.2's reset of the protocol state
; requires.  The (:tls-established) re-entry keeps the base session
; (fn-auth-tls-established), so the connection comes out of the handshake
; a reader, and only a fresh AUTHINFO over TLS can bind again.
;
; Two hypotheses, each with a violating value in
; tests/acl2/nntp-auth-teeth-tests.lisp.
(defthm fn-auth-step-starttls-clears-a-principal-role
  ; PRF-164: the session also holds while the owner publishes an XREDEEM
  ; (fn-auth-redeem-waitp); that hold is the other theorem below
  ; (fn-auth-step-redeem-hold-keeps-the-role), so this one is about the TLS
  ; handshake exactly.
  (implies (and (not (fn-auth-session-handshakingp as))
                (fn-auth-session-handshakingp
                 (fn-post-result-session
                  (fn-auth-step as archive config observation injection
                                wire-event fn-arena)))
                (not (fn-auth-redeem-waitp
                      (fn-post-result-session
                       (fn-auth-step as archive config observation injection
                                     wire-event fn-arena))))
                ; the hold is not a COMPRESS layer's (RFC 8054: 206 keeps
                ; the login; fn-auth-established-starts-the-owed-compression)
                (not (fn-zc-owedp
                      (fn-auth-session-compress
                       (fn-post-result-session
                        (fn-auth-step as archive config observation injection
                                      wire-event fn-arena))))))
           (and (null (fn-auth-session-subject
                       (fn-post-result-session
                        (fn-auth-step as archive config observation injection
                                      wire-event fn-arena))))
                (null (fn-auth-session-pending
                       (fn-post-result-session
                        (fn-auth-step as archive config observation injection
                                      wire-event fn-arena))))
                (not (fn-auth-principal-rolep
                      (fn-post-result-session
                       (fn-auth-step as archive config observation injection
                                     wire-event fn-arena))))
                (equal (fn-auth-session-peer
                        (fn-post-result-session
                         (fn-auth-step as archive config observation injection
                                       wire-event fn-arena)))
                       (if (fn-auth-principal-rolep as)
                           nil
                         (fn-auth-session-peer as)))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step fn-auth-command fn-auth-tls-eventp
                            fn-auth-tls-established)
                           (fn-auth-restricted-keywordp fn-auth-restricted-keyword-is-a-keyword-token
                            fn-auth-upcase-keeps-a-keyword-token
                            fn-peer-step fn-auth-delegate fn-auth-single
                            fn-auth-authinfo fn-auth-starttls
                            fn-auth-sessionp fn-auth-session-peer
                            fn-auth-principal-rolep fn-auth-gatedp
                            fn-auth-postingp fn-auth-find-cred
                            fn-auth-sasl-continue fn-auth-install-context
                            fn-auth-context-eventp fn-auth-sasl-waitingp
                            fn-auth-capability-lines-for-peer
                            fn-auth-peer-record fn-nntp-multi
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-keyword-tokenp fn-nntp-keywordp
                            fn-nntp-command-arguments-at-mostp
                            fn-auth-starttls-handshake-clears-a-principal-role))
           :use ((:instance fn-auth-starttls-handshake-clears-a-principal-role
                            (args (cdr (fn-nntp-tokenize
                                        (cadr wire-event)))))))))


; The other hold (PRF-164).  Whenever a step enters the redemption hold,
; the new session has no subject and keeps the connection's role: holding
; for the owner's publication binds nobody.
(defthm fn-auth-step-redeem-hold-keeps-the-role
  (implies (and (not (fn-auth-session-handshakingp as))
                (fn-auth-session-handshakingp
                 (fn-post-result-session
                  (fn-auth-step as archive config observation injection
                                wire-event fn-arena)))
                (fn-auth-redeem-waitp
                 (fn-post-result-session
                  (fn-auth-step as archive config observation injection
                                wire-event fn-arena)))
                (not (fn-zc-owedp
                      (fn-auth-session-compress
                       (fn-post-result-session
                        (fn-auth-step as archive config observation injection
                                      wire-event fn-arena))))))
           (and (null (fn-auth-session-subject
                       (fn-post-result-session
                        (fn-auth-step as archive config observation injection
                                      wire-event fn-arena))))
                (equal (fn-auth-session-peer
                        (fn-post-result-session
                         (fn-auth-step as archive config observation injection
                                       wire-event fn-arena)))
                       (fn-auth-session-peer as))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step fn-auth-command fn-auth-tls-eventp
                            fn-auth-redeem-waitp
                            fn-auth-tls-established)
                           (fn-auth-restricted-keywordp fn-auth-restricted-keyword-is-a-keyword-token
                            fn-auth-upcase-keeps-a-keyword-token
                            fn-peer-step fn-auth-delegate fn-auth-single
                            fn-auth-authinfo fn-auth-starttls
                            fn-auth-sessionp fn-auth-session-peer
                            fn-auth-principal-rolep fn-auth-gatedp
                            fn-auth-postingp fn-auth-find-cred
                            fn-auth-capability-lines-for-peer
                            fn-auth-peer-record fn-nntp-multi
                            fn-nntp-tokenize fn-nntp-command-inputp
                            fn-nntp-keyword-tokenp fn-nntp-keywordp
                            fn-nntp-command-arguments-at-mostp
                            fn-auth-starttls-handshake-clears-a-principal-role
                            fn-auth-sasl-continue fn-auth-install-context
                            fn-auth-context-eventp fn-auth-sasl-waitingp
                            fn-auth-xredeem-holds-only-to-wait))
           :use ((:instance fn-auth-xredeem-holds-only-to-wait
                            (args (cdr (fn-nntp-tokenize
                                        (cadr wire-event)))))
                 (:instance fn-auth-starttls-handshake-clears-a-principal-role
                            (args (cdr (fn-nntp-tokenize
                                        (cadr wire-event)))))))))


