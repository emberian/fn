;; The served Xref overview field over the served step the host runs (R3,
;; PRF-206).
;;
;; Host path (reader): host/native/owner.lisp calls fn-owner-chunk
;; (host/owner-host.lisp), which runs fn-scar-ocfg-read-tls-prefix; the chain
;; recorded in books/owner-verdict-read.lisp and
;; books/owner-list-counts-read.lisp equates that with fn-served-step on the
;; connection, as for books/owner-descriptions-read.lisp's keystones.
;;
;; The server name: host/owner-host.lisp fn-owner-post-config calls
;; books/owner-agent.lisp fn-oag-post-config, whose listing's third element
;; is fn-oag-agent, the node's <path-identity> when one is configured
;; (`fn-oag-listing-server-is-the-path-identity' below); the connection pins
;; that configuration at open (fn-oag-open-pins-the-owner-config).
;; What the field holds: books/nntp-xref.lisp `fn-xref-pairs-exact' and
;; `fn-xref-pair-is-an-index-entry'; the lines:
;; `fn-nov-served-lines-numbered-has-the-article-line'.

(in-package "ACL2")
(include-book "owner-descriptions-read")
(include-book "nntp-xref-invariants")

(local
 (defthm fn-oxr-xref-server-of-reader-env
   (equal (fn-nntp-xref-server (fn-post-reader-env config observation))
          (if (fn-xref-serverp
               (fn-nntp-listing-server (fn-inj-config-listing config)))
              (fn-nntp-listing-server (fn-inj-config-listing config))
            nil))
   :hints (("Goal" :in-theory (e/d (fn-nntp-xref-server)
                                   (fn-xref-serverp fn-nntp-listing-server
                                    fn-post-reader-env))))))

; The dispatcher the served step calls: OVER or XOVER of a range with a
; server name is the served renderer (no earlier arm reads OVER).
(defthm fn-nntp-archive-command-pinned-over-range-served
  (implies (and (or (fn-nntp-keywordp keyword "OVER")
                    (fn-nntp-keywordp keyword "XOVER"))
                (fn-nntp-xref-server env)
                (fn-gidx-pinp index)
                (consp args) (null (cdr args))
                (fn-nntp-range-okp (fn-nntp-parse-range (car args))))
           (equal (fn-nntp-archive-command-pinned
                   session archive index verdicts env keyword args)
                  (fn-nntp-over-range-served
                   session (fn-gidx-pin-buckets index) (fn-gidx-pin-trie index)
                   (car args) (fn-nntp-keywordp keyword "XOVER")
                   (fn-nntp-xref-server env))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-archive-command-pinned fn-nntp-xref-reply
                            fn-nntp-keywordp)
                           (fn-nntp-upcase-keyword fn-nntp-keyword-tokenp
                            fn-nntp-xref-server fn-nntp-over-range-served
                            fn-nntp-list-overview-fmt-served
                            fn-gidx-list-counts-command
                            fn-nntp-number-withdrawn-p fn-nntp-msgid-withdrawn-p
                            fn-nntp-msgid-retrieval-indexed
                            fn-gidx-listgroup-command fn-nntp-parse-range
                            fn-nntp-range-okp fn-gidx-pinp)))))

; KEYSTONE (server).  The server name OVER is handed on a connection pinned
; to the owner's posting configuration of CFG is the node's path-identity.
(defthm fn-oag-listing-server-is-the-path-identity
  (implies (fn-oag-identity-setp cfg)
           (equal (fn-nntp-listing-server
                   (fn-inj-config-listing (fn-oag-post-config cfg max-octets)))
                  (fn-record-string-octets (fn-oag-identity cfg))))
  :hints (("Goal" :in-theory (e/d (fn-oag-post-config fn-oag-listing
                                   fn-oag-agent fn-nntp-listing-server)
                                  (fn-oag-descs fn-cfg-motd-lines
                                   fn-oag-identity fn-oag-identity-setp
                                   fn-cnode-served-of)))))

(local
 (defthm fn-oxr-over-range-served-has-no-offer
   (not (fn-post-offeredp
         (fn-nntp-result-effects
          (fn-nntp-over-range-served session buckets trie token legacyp server))))
   :hints (("Goal" :in-theory (e/d (fn-nntp-over-range-served)
                                   (fn-nov-served-lines-numbered fn-post-offeredp
                                    fn-nntp-index-group-range-numbers
                                    fn-nntp-parse-range
                                    fn-nntp-single fn-nntp-multi))))))

(local
 (defthm fn-oxr-over-range-served-effects-true-listp
   (true-listp (fn-nntp-result-effects
                (fn-nntp-over-range-served session buckets trie token legacyp
                                           server)))
   :hints (("Goal" :in-theory (e/d (fn-nntp-over-range-served
                                    fn-nntp-single fn-nntp-multi
                                    fn-nntp-make-result fn-nntp-result-effects)
                                   (fn-nov-served-lines-numbered
                                    fn-nntp-index-group-range-numbers
                                    fn-nntp-parse-range))))))

(defthm fn-served-dispatch-over-range-served
  (let* ((as (fn-served-conn-session conn))
         (ps (fn-auth-session-base as))
         (pst (fn-peer-session-base ps))
         (ns (fn-post-session-base pst))
         (tokens (fn-nntp-tokenize line)))
    (implies (and (fn-auth-sessionp as)
                  ;; PRF-222: a session without a group-access rule (a
                  ;; restricted one is served the view: books/group-access.lisp).
                  (not (fn-auth-access-restrictedp as (fn-served-conn-config conn)))
                  (not (fn-auth-session-handshakingp as))
                  (not (fn-auth-gatedp as (car tokens)))
                  (fn-peer-sessionp ps)
                  (null (fn-peer-session-peer ps))
                  (fn-post-sessionp pst)
                  (not (fn-post-session-awaiting pst))
                  (fn-nntp-sessionp ns)
                  (equal (fn-nntp-session-openp ns) t)
                  (fn-nntp-session-projected ns)
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp tokens)
                  (consp (cdr tokens))
                  (null (cddr tokens))
                  (fn-nntp-keyword-tokenp (car tokens))
                  (fn-nntp-keywordp (car tokens) "OVER")
                  (fn-nntp-range-okp (fn-nntp-parse-range (cadr tokens)))
                  (fn-gidx-pinp (fn-served-conn-pinned-index conn))
                  (fn-xref-serverp
                   (fn-nntp-listing-server
                    (fn-inj-config-listing (fn-served-conn-config conn)))))
             (and (equal (fn-served-result-effects
                          (fn-served-dispatch conn (list :command line)))
                         (fn-nntp-result-effects
                          (fn-nntp-over-range-served
                           ns (fn-gidx-pin-buckets (fn-served-conn-pinned-index conn))
                           (fn-gidx-pin-trie (fn-served-conn-pinned-index conn))
                           (cadr tokens) nil
                           (fn-nntp-listing-server
                            (fn-inj-config-listing (fn-served-conn-config conn))))))
                  (equal (fn-served-conn-wire
                          (fn-served-result-conn
                           (fn-served-dispatch conn (list :command line))))
                         (fn-served-conn-wire conn)))))
  :hints (("Goal" :in-theory (e/d (fn-served-dispatch fn-auth-step-pinned
                                   fn-auth-command fn-auth-delegate-pinned
                                   fn-peer-step-pinned fn-peer-delegate-pinned
                                   fn-nntp-post-step-pinned fn-nntp-step-pinned
                                   fn-nntp-command-pinned
                                   fn-auth-tls-eventp fn-nntp-keywordp
                                   fn-nntp-archive-keywordp)
                                  (fn-nntp-archive-command-pinned
                                   fn-nntp-list-newsgroups-described fn-nntp-over-range-served
                                   fn-nntp-list-motd fn-nntp-env-listed
                                   fn-olc-buckets-okp fn-served-conn-pinned-index
                                   fn-nntp-projectionp
                                   fn-nntp-tokenize fn-auth-sessionp
                                   fn-peer-sessionp fn-post-sessionp
                                   fn-nntp-sessionp fn-auth-gatedp
                                   fn-nntp-upcase-keyword
                                   fn-nntp-keyword-tokenp fn-nntp-command-inputp
                                   fn-nntp-command-arguments-at-mostp))
           :use ((:instance fn-nntp-archive-command-pinned-over-range-served
                  (session (fn-post-session-base
                            (fn-peer-session-base
                             (fn-auth-session-base (fn-served-conn-session conn)))))
                  (archive (fn-served-conn-archive conn))
                  (index (fn-served-conn-pinned-index conn))
                  (verdicts (fn-served-conn-verdicts conn))
                  (env (fn-post-reader-env (fn-served-conn-config conn)
                                           (fn-served-conn-observation conn)))
                  (keyword (car (fn-nntp-tokenize line)))
                  (args (cdr (fn-nntp-tokenize line))))))))


(defthm fn-served-step-over-range-carries-the-xref
  (let* ((w0 (fn-served-conn-wire conn))
         (w1 (fn-wire-result-state (fn-wire-feed-proper w0 prefix)))
         (w2 (fn-wire-result-state (fn-wire-feed-byte w1 byte)))
         (as (fn-served-conn-session conn))
         (ps (fn-auth-session-base as))
         (pst (fn-peer-session-base ps))
         (ns (fn-post-session-base pst))
         (tokens (fn-nntp-tokenize line)))
    (implies (and (fn-served-conn-shapep conn)
                  (fn-wire-statep w0)
                  (not (equal (fn-wire-state-mode w0) :closed))
                  (not (fn-wire-result-events (fn-wire-feed-proper w0 prefix)))
                  (equal (fn-wire-result-events (fn-wire-feed-byte w1 byte))
                         (list (list :command line)))
                  (not (equal (fn-wire-state-mode w2) :closed))
                  (fn-auth-sessionp as)
                  (not (fn-auth-session-handshakingp as))
                  (not (fn-auth-gatedp as (car tokens)))
                  (fn-peer-sessionp ps)
                  (null (fn-peer-session-peer ps))
                  (fn-post-sessionp pst)
                  (not (fn-post-session-awaiting pst))
                  (fn-nntp-sessionp ns)
                  (equal (fn-nntp-session-openp ns) t)
                  (fn-nntp-session-projected ns)
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp tokens)
                  (consp (cdr tokens))
                  (null (cddr tokens))
                  (fn-nntp-keyword-tokenp (car tokens))
                  (fn-nntp-keywordp (car tokens) "OVER")
                  (fn-nntp-range-okp (fn-nntp-parse-range (cadr tokens)))
                  (fn-gidx-pinp (fn-served-conn-pinned-index conn))
                  (fn-xref-serverp
                   (fn-nntp-listing-server
                    (fn-inj-config-listing (fn-served-conn-config conn)))))
             (equal (fn-served-result-effects
                     (fn-served-step conn (append prefix (list byte))))
                    (fn-nntp-result-effects
                     (fn-nntp-over-range-served
                      ns (fn-gidx-pin-buckets (fn-served-conn-pinned-index conn))
                      (fn-gidx-pin-trie (fn-served-conn-pinned-index conn))
                      (cadr tokens) nil
                      (fn-nntp-listing-server
                       (fn-inj-config-listing (fn-served-conn-config conn))))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-served-step-of-one-framed-event
                  (event (list :command line)))
                 (:instance fn-served-dispatch-over-range-served
                  (conn (fn-ovr-with-wire
                         conn
                         (fn-wire-result-state
                          (fn-wire-feed-byte
                           (fn-wire-result-state
                            (fn-wire-feed-proper (fn-served-conn-wire conn) prefix))
                           byte))))))
           :in-theory (e/d (fn-served-closed-wirep fn-served-tls-handshakingp)
                           (fn-olc-buckets-okp
                            fn-served-step-of-one-framed-event
                            fn-served-dispatch-over-range-served
                            fn-served-step fn-served-dispatch
                            fn-wire-feed-byte fn-wire-feed-proper fn-wire-statep
                            fn-nntp-list-newsgroups-described fn-nntp-list-motd
                            fn-nntp-over-range-served fn-gidx-pinp
                            fn-nntp-env-listed fn-nntp-projectionp
                            fn-midx-correspondencep fn-gidx-build
                            fn-nntp-tokenize fn-auth-sessionp
                            fn-peer-sessionp fn-post-sessionp
                            fn-nntp-sessionp fn-auth-gatedp
                            fn-nntp-keywordp fn-nntp-keyword-tokenp
                            fn-nntp-command-inputp
                            fn-nntp-command-arguments-at-mostp)))))

