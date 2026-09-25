; fn: the injecting agent a served POST names.
;
; RFC 5536 section 3.2.8 opens Injection-Info with the <path-identity> of the
; injecting agent, and RFC 5537 section 3.2.1 has the same agent prepend that
; identity to Path; books/injection.lisp writes both from one value,
; fn-inj-config-agent.  fn has ONE slot for a node's <path-identity>: the
; replayed configuration policy `path-identity' (`fn operator CONFIG policy
; set path-identity IDENTITY', admitted by fn-path-identityp in
; books/native-admin.lisp), which peer loop suppression reads too
; (fn-peer-local-identity).  `fn-oag-agent' reads that slot and nothing else.
; fn.toml's `[posting] agent' is not a second slot: a value there could only
; disagree with Path, and the native operator refuses it by name
; (books/native-config.lisp, fn-native-config-unsupported-key).
;
; This was host code (host/owner-host.lisp `fn-owner-agent-of', program
; mode), so no theorem could name the function the host called.  The host
; now calls `fn-oag-post-config' and holds no identity of its own.
;
; The chain, each link a theorem below over the function the next layer (or
; the host) calls:
;
;   host/owner-host.lisp fn-owner-post-config -> fn-oag-post-config: its
;     agent is the path-identity (fn-oag-post-config-agent-is-the-path-identity)
;   host/owner-host.lisp fn-owner-open -> fn-ocfg-open: the new connection
;     pins the owner's installed configuration
;     (fn-oag-open-pins-the-owner-config; composed with the first as
;     fn-oag-configured-open-pins-the-path-identity)
;   host/owner-host.lisp fn-owner-chunk -> fn-ocfg-read-tls-prefix: the
;     submission a read hands the owner names the pinned agent
;     (fn-oag-served-post-names-the-pinned-agent), down through
;     fn-served-step, fn-served-feed, fn-served-dispatch, fn-auth-step,
;     fn-peer-step and fn-nntp-post-step to fn-inj-decide
;     (fn-inj-injected-article-names-the-configured-agent,
;     books/injection-invariants.lisp).

(in-package "ACL2")
(include-book "injection")
(include-book "injection-invariants")
(include-book "config")
(include-book "node-config")
(include-book "owner-tls-prefix")

; -----------------------------------------------------------------------------
; The injecting agent

; A store whose `path-identity' slot is unset injects as this RFC 2606
; `.invalid' name: it names no real host, and it says the node was not told
; who it is.  It was host/owner-host.lisp's `*fn-owner-agent*'.
(defconst *fn-oag-unset-agent*
  '(102 110 46 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100))

(defun fn-oag-identity (cfg)
  "The configured path-identity policy text, or the empty string."
  (declare (xargs :guard t))
  (fn-cfg-policy (fn-cfg-value cfg) "path-identity"))

(defun fn-oag-identity-setp (cfg)
  (declare (xargs :guard t))
  (and (stringp (fn-oag-identity cfg))
       (not (equal (fn-oag-identity cfg) ""))))

(defun fn-oag-agent (cfg)
  (declare (xargs :guard t))
  (if (fn-oag-identity-setp cfg)
      (fn-record-string-octets (fn-oag-identity cfg))
    *fn-oag-unset-agent*))

(defun fn-oag-group-octets (names)
  (declare (xargs :guard t))
  (if (consp names)
      (cons (fn-nntp-string-octets (car names))
            (fn-oag-group-octets (cdr names)))
    nil))

(defun fn-oag-post-config (cfg max-octets)
  "The posting configuration the owner installs for configuration CFG.

The host calls this at host/owner-host.lisp `fn-owner-post-config', which
`fn-owner-recover' and `fn-owner-reconfigure-complete' install with
fn-own-configure.  MAX-OCTETS is the store's payload bound, which the host
supplies as `*fn-record-max-payload*' (books/records-shape.lisp)."
  (declare (xargs :guard t))
  (fn-inj-make-config t (fn-oag-agent cfg)
                      (fn-oag-group-octets (fn-cnode-served-of cfg))
                      max-octets))

(defthm fn-oag-post-config-agent-is-the-path-identity
  (implies (fn-oag-identity-setp cfg)
           (equal (fn-inj-config-agent (fn-oag-post-config cfg max-octets))
                  (fn-record-string-octets (fn-oag-identity cfg))))
  :hints (("Goal" :in-theory (disable fn-oag-identity))))

; -----------------------------------------------------------------------------
; What names an agent
;
; A decision names AGENT when, if it is an injected article, its octets carry
; the Injection-Info line generated from AGENT.  A transit submission and nil
; name every agent vacuously: neither is an injection.

(defun fn-oag-names-agentp (decision agent)
  (declare (xargs :guard t))
  (or (not (fn-inj-injectedp decision))
      (fn-inj-infixp (fn-inj-injection-info-line agent)
                     (fn-inj-decision-octets decision))))

(defthm fn-oag-injected-article-names-the-path-identity
  (implies (and (fn-oag-identity-setp cfg)
                (fn-inj-injectedp
                 (fn-inj-decide source (fn-oag-post-config cfg max-octets)
                                observation)))
           (fn-inj-infixp
            (fn-inj-injection-info-line
             (fn-record-string-octets (fn-oag-identity cfg)))
            (fn-inj-decision-octets
             (fn-inj-decide source (fn-oag-post-config cfg max-octets)
                            observation))))
  :hints (("Goal"
           :use ((:instance fn-inj-injected-article-names-the-configured-agent
                            (config (fn-oag-post-config cfg max-octets))))
           :in-theory (disable fn-inj-injected-article-names-the-configured-agent
                               fn-oag-post-config fn-oag-identity
                               fn-oag-identity-setp fn-inj-decide
                               fn-inj-injectedp fn-inj-injection-info-line
                               fn-inj-infixp))))

; -----------------------------------------------------------------------------
; Two decisions that name every agent: nil, and a transit record (neither is
; an injection).

(defthm fn-oag-nil-names-every-agent
  (fn-oag-names-agentp nil agent))

(defthm fn-oag-transit-record-names-every-agent
  (fn-oag-names-agentp (fn-peer-make-submission peer kind msgid octets) agent)
  :hints (("Goal" :in-theory (enable fn-peer-make-submission fn-inj-injectedp
                                     fn-inj-decision-status fn-inj-nth fn-inj-car))))

; -----------------------------------------------------------------------------
; Up the served stack: fn-nntp-post-step, fn-peer-step, fn-auth-step

(defthm fn-oag-post-step-submission-names-the-configured-agent
  (fn-oag-names-agentp
   (fn-post-result-submission
    (fn-nntp-post-step ps archive config observation injection wire-event))
   (fn-inj-config-agent config))
  :hints (("Goal" :in-theory (e/d (fn-nntp-post-step)
                                  (fn-inj-decide fn-inj-injectedp
                                   fn-inj-injection-info-line
                                   fn-inj-infixp fn-nntp-step
                                   fn-post-offeredp
                                   fn-post-refusal-line)))))

(defthm fn-oag-peer-step-submission-names-the-configured-agent
  (fn-oag-names-agentp
   (fn-post-result-submission
    (fn-peer-step ps archive config observation injection wire-event))
   (fn-inj-config-agent config))
  :hints (("Goal" :in-theory (e/d (fn-peer-step fn-peer-delegate fn-peer-command
                                   fn-peer-transferp fn-peer-msgid-argp)
                                  (fn-nntp-post-step fn-oag-names-agentp
                                   fn-peer-submissionp fn-peer-single
                                   fn-peer-echo-reply fn-peer-decide-offer
                                   fn-peer-decision-kind fn-nntp-keywordp
                                   fn-nntp-keyword-tokenp fn-nntp-multi
                                   fn-peer-capability-lines fn-cfg-peer-find
                                   fn-post-sessionp fn-node-statep fn-cfgp
                                   fn-af-message-idp fn-nntp-printable-tokenp
                                   fn-nntp-command-inputp fn-nntp-tokenize
                                   fn-nntp-command-arguments-at-mostp
                                   fn-post-body-octets fn-nntp-session-openp
                                   fn-peer-ihave-offer-line fn-peer-check-code
                                   fn-oag-post-step-submission-names-the-configured-agent))
           :use ((:instance fn-oag-post-step-submission-names-the-configured-agent
                            (ps (fn-peer-session-base ps)))
                 (:instance fn-oag-post-step-submission-names-the-configured-agent)))))

(defthm fn-oag-auth-step-submission-names-the-configured-agent
  (fn-oag-names-agentp
   (fn-post-result-submission
    (fn-auth-step as archive config observation injection wire-event))
   (fn-inj-config-agent config))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable fn-auth-step fn-peer-step fn-oag-names-agentp
                               fn-oag-peer-step-submission-names-the-configured-agent)
           :cases ((fn-post-result-submission
                    (fn-auth-step as archive config observation injection wire-event)))
           :use ((:instance fn-auth-submission-is-the-delegated-submission)
                 (:instance fn-oag-peer-step-submission-names-the-configured-agent
                            (ps (fn-auth-session-base as)))))))

; -----------------------------------------------------------------------------
; The dispatcher and the byte fold.  fn-served-connp is the carried served
; invariant (books/served.lisp): it types the dispatcher's own effects, so
; the only :submit a dispatch emits is the one fn-auth-step-pinned handed it.

; The pinned reader path does not construct an injection while processing an
; ordinary command.  Its awaiting-body branch calls the original POST step,
; whose injection carries the configured agent.
(defthm fn-oag-post-step-pinned-submission-names-the-configured-agent
  (fn-oag-names-agentp
   (fn-post-result-submission
    (fn-nntp-post-step-pinned ps archive index verdicts config observation
                              injection wire-event))
   (fn-inj-config-agent config))
  :hints (("Goal"
           :in-theory (e/d (fn-nntp-post-step-pinned)
                           (fn-nntp-post-step fn-nntp-step-pinned
                            fn-oag-names-agentp fn-post-offeredp
                            fn-oag-post-step-submission-names-the-configured-agent))
           :use ((:instance fn-oag-post-step-submission-names-the-configured-agent)))))

(defthm fn-oag-peer-step-pinned-submission-names-the-configured-agent
  (fn-oag-names-agentp
   (fn-post-result-submission
    (fn-peer-step-pinned ps archive index verdicts config observation
                         injection wire-event))
   (fn-inj-config-agent config))
  :hints (("Goal"
           :in-theory (e/d (fn-peer-step-pinned fn-peer-delegate-pinned
                            fn-peer-command fn-peer-transferp fn-peer-msgid-argp)
                           (fn-peer-step fn-nntp-post-step-pinned
                            fn-oag-names-agentp fn-peer-submissionp
                            fn-peer-single fn-peer-echo-reply
                            fn-peer-decide-offer fn-peer-decision-kind
                            fn-nntp-keywordp fn-nntp-keyword-tokenp
                            fn-nntp-multi fn-peer-capability-lines
                            fn-cfg-peer-find fn-post-sessionp fn-node-statep
                            fn-cfgp fn-af-message-idp
                            fn-nntp-printable-tokenp fn-nntp-command-inputp
                            fn-nntp-tokenize
                            fn-nntp-command-arguments-at-mostp
                            fn-post-body-octets fn-nntp-session-openp
                            fn-peer-ihave-offer-line fn-peer-check-code))
           :use ((:instance fn-oag-peer-step-submission-names-the-configured-agent)
                 (:instance fn-oag-post-step-pinned-submission-names-the-configured-agent
                            (ps (fn-peer-session-base ps)))))))

(defthm fn-oag-auth-step-pinned-submission-names-the-configured-agent
  (fn-oag-names-agentp
   (fn-post-result-submission
    (fn-auth-step-pinned as archive index verdicts config observation
                         injection wire-event))
   (fn-inj-config-agent config))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable fn-auth-step-pinned fn-peer-step-pinned
                               fn-oag-names-agentp
                               fn-oag-peer-step-pinned-submission-names-the-configured-agent)
           :cases ((fn-post-result-submission
                    (fn-auth-step-pinned as archive index verdicts config
                                         observation injection wire-event)))
           :use ((:instance fn-auth-pinned-submission-is-the-delegated-submission)
                 (:instance fn-oag-peer-step-pinned-submission-names-the-configured-agent
                            (ps (fn-auth-session-base as)))))))

(local
 (defthm fn-oag-auth-effects-carry-no-submission
   (implies (fn-auth-effectsp effects)
            (not (fn-served-submission effects)))
   :hints (("Goal" :induct (fn-served-submission effects)
            :in-theory (e/d (fn-auth-effectsp fn-auth-effectp fn-nntp-effectp
                             fn-served-submission fn-nntp-close-effect
                             fn-nntp-begin-article-effect
                             fn-auth-starttls-effect)
                            (fn-nntp-replyp fn-octet-listp))))))

(defthm fn-oag-dispatch-submission-names-the-configured-agent
  (implies (fn-served-connp conn)
           (fn-oag-names-agentp
            (fn-served-submission
             (fn-served-result-effects (fn-served-dispatch conn event)))
            (fn-inj-config-agent (fn-served-conn-config conn))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-served-dispatch)
                           (fn-auth-step-pinned fn-auth-sessionp fn-served-connp
                            fn-oag-names-agentp fn-auth-effectsp
                            fn-served-connp-is-consistent-session
                            fn-served-connp-is-index-correspondence
                            fn-auth-step-pinned-effects-well-formed
                            fn-oag-auth-step-pinned-submission-names-the-configured-agent
                            fn-post-offeredp
                            fn-wire-begin-article-with-line-limit
                            fn-wire-article-line-limit))
           :use ((:instance fn-served-connp-is-consistent-session (c conn))
                 (:instance fn-served-connp-is-index-correspondence (c conn))
                 (:instance fn-served-connp-is-group-correspondence (c conn))
                 (:instance fn-served-connp-is-pinned-trie-correspondence
                            (c conn))
                 (:instance fn-auth-step-pinned-effects-well-formed
                            (as (fn-served-conn-session conn))
                            (archive (fn-served-conn-archive conn))
                            (index (fn-served-conn-pinned-index conn))
                            (verdicts (fn-served-conn-verdicts conn))
                            (config (fn-served-conn-config conn))
                            (observation (fn-served-conn-observation conn))
                            (injection (fn-served-conn-injection conn))
                            (wire-event event))
                 (:instance fn-oag-auth-step-pinned-submission-names-the-configured-agent
                            (as (fn-served-conn-session conn))
                            (archive (fn-served-conn-archive conn))
                            (index (fn-served-conn-pinned-index conn))
                            (verdicts (fn-served-conn-verdicts conn))
                            (config (fn-served-conn-config conn))
                            (observation (fn-served-conn-observation conn))
                            (injection (fn-served-conn-injection conn))
                            (wire-event event))))))

(defthm fn-oag-dispatch-keeps-the-config
  (equal (fn-served-conn-config
          (fn-served-result-conn (fn-served-dispatch conn event)))
         (fn-served-conn-config conn))
  :hints (("Goal" :in-theory (e/d (fn-served-dispatch)
                                  (fn-auth-step-pinned fn-post-offeredp
                                   fn-wire-begin-article-with-line-limit
                                   fn-wire-article-line-limit)))))

(defthm fn-oag-dispatch-events-keep-the-config
  (equal (fn-served-conn-config
          (fn-served-result-conn (fn-served-dispatch-events conn events)))
         (fn-served-conn-config conn))
  :hints (("Goal" :induct (fn-served-dispatch-events conn events)
           :in-theory (disable fn-served-dispatch))))

(defthm fn-oag-dispatch-events-submission-names-the-configured-agent
  (implies (fn-served-connp conn)
           (fn-oag-names-agentp
            (fn-served-submission
             (fn-served-result-effects (fn-served-dispatch-events conn events)))
            (fn-inj-config-agent (fn-served-conn-config conn))))
  :hints (("Goal" :induct (fn-served-dispatch-events conn events)
           :in-theory (disable fn-served-dispatch fn-served-connp
                               fn-oag-names-agentp fn-served-effectsp
                               fn-served-submission))))

(defthm fn-oag-dispatch-events-submission-names-the-pinned-agent
  (implies (and (fn-served-connp conn)
                (equal agent (fn-inj-config-agent (fn-served-conn-config conn))))
           (fn-oag-names-agentp
            (fn-served-submission
             (fn-served-result-effects (fn-served-dispatch-events conn events)))
            agent))
  :hints (("Goal" :in-theory (disable fn-served-dispatch-events fn-served-connp
                                      fn-oag-names-agentp))))

(local
 (defthm fn-oag-fed-conn-is-a-connection
   (implies (fn-served-connp conn)
            (fn-served-connp
             (fn-served-make-conn-group-indexed
              (fn-wire-result-state
               (fn-wire-feed-byte (fn-served-conn-wire conn) byte))
              (fn-served-conn-session conn)
              (fn-served-conn-archive conn)
              (fn-served-conn-config conn)
              (fn-served-conn-observation conn)
              (fn-served-conn-injection conn)
              (fn-served-conn-verdicts conn)
              (fn-served-conn-index conn)
              (fn-served-conn-group-index conn))))
   :hints (("Goal" :in-theory (e/d (fn-served-connp)
                                   (fn-wire-feed-byte fn-wire-statep
                                    fn-auth-session-consistentp))))))

(defthm fn-oag-feed-keeps-the-config
  (equal (fn-served-conn-config
          (fn-served-result-conn (fn-served-feed conn octets)))
         (fn-served-conn-config conn))
  :hints (("Goal" :induct (fn-served-feed conn octets)
           :in-theory (e/d (fn-served-feed) (fn-served-dispatch-events fn-wire-feed-byte
                               fn-wire-statep)))))

(defthm fn-oag-feed-submission-names-the-configured-agent
  (implies (fn-served-connp conn)
           (fn-oag-names-agentp
            (fn-served-submission
             (fn-served-result-effects (fn-served-feed conn octets)))
            (fn-inj-config-agent (fn-served-conn-config conn))))
  :hints (("Goal" :induct (fn-served-feed conn octets)
           :in-theory (e/d (fn-served-feed) (fn-served-dispatch-events fn-wire-feed-byte
                               fn-wire-statep fn-served-connp
                               fn-oag-names-agentp fn-served-effectsp
                               fn-served-submission)))))

(defthm fn-oag-served-step-submission-names-the-pinned-agent
  (implies (and (fn-served-connp conn)
                (equal agent (fn-inj-config-agent (fn-served-conn-config conn))))
           (fn-oag-names-agentp
            (fn-served-submission
             (fn-served-result-effects (fn-served-step conn octets)))
            agent))
  :hints (("Goal" :in-theory (e/d (fn-served-step)
                                  (fn-served-feed fn-served-connp
                                   fn-oag-names-agentp fn-served-effectsp
                                   fn-served-submission))
           :use ((:instance fn-served-submission-of-append
                            (left (fn-served-result-effects (fn-served-feed conn octets)))
                            (right (list (fn-nntp-close-effect))))))))

; -----------------------------------------------------------------------------
; The owner transitions the host calls

(defthm fn-oag-tls-served-conn-config
  (equal (fn-served-conn-config (fn-own-tls-served-conn o conn))
         (fn-own-conn-config conn))
  :hints (("Goal" :in-theory (enable fn-own-tls-served-conn))))

(defthm fn-oag-read-tls-prefix-submission-names-the-pinned-agent
  (implies (fn-served-connp
            (fn-own-tls-served-conn o (fn-own-find-conn id (fn-own-conns o))))
           (fn-oag-names-agentp
            (fn-served-submission
             (fn-own-tls-result-effects (fn-own-read-tls-prefix o id octets)))
            (fn-inj-config-agent
             (fn-own-conn-config (fn-own-find-conn id (fn-own-conns o))))))
  :hints (("Goal"
           :in-theory (e/d (fn-own-read-tls-prefix fn-own-tls-make-result
                            fn-own-tls-result-effects fn-own-finish-read)
                           (fn-served-step fn-served-step-counted-fast
                            fn-served-step-counted fn-served-connp
                            fn-oag-names-agentp fn-served-submission
                            fn-own-tls-served-conn
                            fn-oag-served-step-submission-names-the-pinned-agent))
           :use ((:instance fn-served-step-counted-fast-is-reference
                            (conn (fn-own-tls-served-conn
                                   o (fn-own-find-conn id (fn-own-conns o)))))
                 (:instance fn-served-step-counted-result-is-step
                            (conn (fn-own-tls-served-conn
                                   o (fn-own-find-conn id (fn-own-conns o)))))
                 (:instance fn-oag-served-step-submission-names-the-pinned-agent
                            (conn (fn-own-tls-served-conn
                                   o (fn-own-find-conn id (fn-own-conns o))))
                            (agent (fn-inj-config-agent
                                    (fn-own-conn-config
                                     (fn-own-find-conn id (fn-own-conns o))))))))))

; KEYSTONE.  The owner transition host/owner-host.lisp `fn-owner-chunk' calls
; for every observed socket region: the submission it hands the owner (the
; one fn-own-finish-read enqueues and `fn-owner-take' later reads the octets
; of) is, when it is an injected article, one whose Injection-Info names the
; agent the connection pinned.  The hypothesis is the served invariant of
; the connection the read runs on; the owner does not carry it
; (books/owner-tls-prefix.lisp, fn-ocfg-read-tls-prefix-is-full-read, and
; PRF-006 record that premise), so this is stated under it rather than
; claimed without it.
(defthm fn-oag-served-post-names-the-pinned-agent
  (let ((conn (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
    (implies (fn-served-connp (fn-own-tls-served-conn (fn-ocfg-owner oc) conn))
             (fn-oag-names-agentp
              (fn-served-submission
               (fn-own-tls-result-effects (fn-ocfg-read-tls-prefix oc id octets)))
              (fn-inj-config-agent (fn-own-conn-config conn)))))
  :hints (("Goal"
           :in-theory (e/d (fn-ocfg-read-tls-prefix fn-own-tls-make-result
                            fn-own-tls-result-effects)
                           (fn-own-read-tls-prefix fn-served-connp
                            fn-oag-names-agentp fn-served-submission
                            fn-own-tls-served-conn
                            fn-oag-read-tls-prefix-submission-names-the-pinned-agent))
           :use ((:instance fn-oag-read-tls-prefix-submission-names-the-pinned-agent
                            (o (fn-ocfg-owner oc)))))))

; What the connection pins.  fn-ocfg-open is what host/owner-host.lisp
; `fn-owner-open' calls: a connection it opens pins the owner's installed
; posting configuration.  The freshness hypothesis is fn-own-relation's
; (fn-own-find-conn-id-below-next): without it an old connection that already
; carries the new identifier is the one found.

(local
 (defthm fn-oag-conns-of-set-conns
   (equal (fn-own-conns (fn-own-set-conns o conns)) conns)
   :hints (("Goal" :in-theory (enable fn-own-set-conns)))))

(local
 (defthm fn-oag-find-conn-has-the-id
   (implies (fn-own-find-conn id conns)
            (equal (fn-own-conn-id (fn-own-find-conn id conns)) id))))

(local
 (defthm fn-oag-find-conn-of-replace-conn-other
   (implies (not (equal (fn-own-conn-id conn) other))
            (equal (fn-own-find-conn other (fn-own-replace-conn conn conns))
                   (fn-own-find-conn other conns)))
   :hints (("Goal" :induct (fn-own-replace-conn conn conns)))))

(local
 (defthm fn-oag-find-conn-of-replace-conn-same-id
   (implies (and (equal (fn-own-conn-id conn) id)
                 (fn-own-find-conn id conns))
            (equal (fn-own-find-conn id (fn-own-replace-conn conn conns))
                   conn))
   :hints (("Goal" :induct (fn-own-replace-conn conn conns)))))

(defthm fn-oag-reader-context-keeps-the-config
  (equal (fn-own-conn-config
          (fn-own-find-conn j (fn-own-conns (fn-own-reader-context o id cfg))))
         (fn-own-conn-config (fn-own-find-conn j (fn-own-conns o))))
  :hints (("Goal" :in-theory (e/d (fn-own-reader-context)
                                  (fn-auth-with-base fn-peer-open-session
                                   fn-own-conn-make-group-indexed))
           :cases ((equal j id)))))

(defthm fn-oag-own-open-pins-the-owner-config
  (implies (not (fn-own-find-conn (fn-own-next-id o) (fn-own-conns o)))
           (equal (fn-own-conn-config
                   (fn-own-find-conn (fn-own-next-id o)
                                     (fn-own-conns (cdr (fn-own-open o acfg)))))
                  (if (fn-own-find-conn (fn-own-next-id o)
                                        (fn-own-conns (cdr (fn-own-open o acfg))))
                      (fn-own-config o)
                    (fn-own-conn-config nil))))
  :hints (("Goal" :in-theory (e/d (fn-own-open)
                                  (fn-served-open fn-own-body-limit
                                   fn-own-conn-make-group-indexed)))))

(defthm fn-oag-open-pins-the-owner-config
  (let* ((o (fn-ocfg-owner oc))
         (id (fn-own-next-id o))
         (conn (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner
                                                    (cdr (fn-ocfg-open oc acfg)))))))
    (implies (and (not (fn-own-find-conn id (fn-own-conns o)))
                  conn)
             (equal (fn-own-conn-config conn) (fn-own-config o))))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-open)
                                  (fn-own-open fn-own-reader-context
                                   fn-oag-own-open-pins-the-owner-config))
           :use ((:instance fn-oag-own-open-pins-the-owner-config
                            (o (fn-ocfg-owner oc)))))))

; The composition: a connection opened on an owner configured with
; fn-oag-post-config of a configuration whose path-identity is set pins that
; path-identity as its agent, so by the keystone above every article it
; submits names it.
(defthm fn-oag-configured-open-pins-the-path-identity
  (let* ((o (fn-ocfg-owner oc))
         (id (fn-own-next-id o))
         (conn (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner
                                                    (cdr (fn-ocfg-open oc acfg)))))))
    (implies (and (fn-oag-identity-setp cfg)
                  (equal (fn-own-config o) (fn-oag-post-config cfg max-octets))
                  (not (fn-own-find-conn id (fn-own-conns o)))
                  conn)
             (equal (fn-inj-config-agent (fn-own-conn-config conn))
                    (fn-record-string-octets (fn-oag-identity cfg)))))
  :hints (("Goal" :in-theory (disable fn-ocfg-open fn-oag-post-config
                                      fn-oag-identity fn-oag-identity-setp))))
