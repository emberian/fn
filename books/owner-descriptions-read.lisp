;; LIST NEWSGROUPS and LIST MOTD over the served step the host runs, and
;; the configuration they show (PRF-195, NNT-039).
;;
;; Host path (reader): host/native/owner.lisp calls fn-owner-chunk
;; (host/owner-host.lisp), which runs fn-scar-ocfg-read-tls-prefix; the chain
;; recorded in books/owner-verdict-read.lisp and books/owner-list-counts-read.lisp
;; equates that with fn-served-step on the connection.  The keystones below
;; are over fn-served-step, as LIST COUNTS's are.
;;
;; Where the listing comes from: host/owner-host.lisp fn-owner-post-config
;; calls books/owner-agent.lisp fn-oag-post-config, whose fifth field is
;; fn-oag-listing of the live configuration; fn-ocl-publish installs it after
;; every published record (books/config-owner-publish.lisp) and
;; fn-oag-open-pins-the-owner-config pins the owner's configuration into each
;; new connection.  fn-oag-description-of-the-listing and
;; fn-oag-motd-of-the-listing state what that listing holds;
;; books/config-descriptions.lisp states what a delta does to the slot.
(in-package "ACL2")
(include-book "owner-list-counts-read")
(include-book "owner-agent")
(include-book "config-descriptions")

(local
 (defthm fn-odr-env-listing-of-env-listed
   (equal (fn-nntp-env-listing (fn-nntp-env-listed o f p l)) l)
   :hints (("Goal" :in-theory (enable fn-nntp-env-listing fn-nntp-env-listed)))))

; The served step's environment is books/nntp-post.lisp `fn-post-reader-env'
; (the listing and the closed groups of the pinned configuration, PRF-196);
; LIST MOTD reads only its listing, which is the configuration's.
(local
 (defthm fn-odr-list-motd-of-reader-env
   (equal (fn-nntp-list-motd s (fn-post-reader-env config observation) args)
          (fn-nntp-list-motd s (fn-nntp-env-listed
                                observation nil
                                (and (fn-inj-config-allow config) t)
                                (fn-inj-config-listing config))
                             args))
   :hints (("Goal" :in-theory (e/d (fn-nntp-list-motd) (fn-nntp-motd-lines))))))

; The dispatcher the served step calls: LIST NEWSGROUPS and LIST MOTD are
; the archive command's, with no pinned arm between (neither is COUNTS, a
; retrieval, LISTGROUP, OVER or HDR).
(defthm fn-nntp-archive-command-pinned-list-newsgroups
  (implies (and (fn-nntp-keywordp keyword "LIST")
                (consp args)
                (fn-nntp-keyword-tokenp (car args))
                (fn-nntp-keywordp (car args) "NEWSGROUPS"))
           (equal (fn-nntp-archive-command-pinned
                   session archive index verdicts env keyword args)
                  (fn-nntp-list-newsgroups-described
                   session archive
                   (fn-nntp-listing-descs (fn-nntp-env-listing env))
                   (cdr args))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-archive-command-pinned
                            fn-nntp-archive-command fn-nntp-list-command
                            fn-nntp-keywordp)
                           (fn-nntp-upcase-keyword fn-nntp-keyword-tokenp
                            fn-gidx-list-counts-command
                            fn-nntp-list-counts-command
                            fn-nntp-list-active-times fn-nntp-list-response
                            fn-nntp-list-newsgroups-described fn-nntp-list-motd
                            fn-gidx-build fn-nntp-projectionp
                            fn-nntp-msgid-retrieval-indexed
                            fn-gidx-listgroup-command
                            fn-nntp-over-range-indexed
                            fn-nntp-verdict-hdr-response)))))

(defthm fn-nntp-archive-command-pinned-list-motd
  (implies (and (fn-nntp-keywordp keyword "LIST")
                (consp args)
                (fn-nntp-keyword-tokenp (car args))
                (fn-nntp-keywordp (car args) "MOTD"))
           (equal (fn-nntp-archive-command-pinned
                   session archive index verdicts env keyword args)
                  (fn-nntp-list-motd session env (cdr args))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nntp-archive-command-pinned
                            fn-nntp-archive-command fn-nntp-list-command
                            fn-nntp-keywordp)
                           (fn-nntp-upcase-keyword fn-nntp-keyword-tokenp
                            fn-gidx-list-counts-command
                            fn-nntp-list-counts-command
                            fn-nntp-list-active-times fn-nntp-list-response
                            fn-nntp-list-newsgroups-described fn-nntp-list-motd
                            fn-gidx-build fn-nntp-projectionp
                            fn-nntp-msgid-retrieval-indexed
                            fn-gidx-listgroup-command
                            fn-nntp-over-range-indexed
                            fn-nntp-verdict-hdr-response)))))

(local
 (defthm fn-odr-newsgroups-has-no-offer
   (not (fn-post-offeredp
         (fn-nntp-result-effects
          (fn-nntp-list-newsgroups-described session archive descs args))))
   :hints (("Goal" :in-theory (e/d (fn-nntp-list-newsgroups-described)
                                   (fn-nntp-described-lines fn-post-offeredp
                                    fn-nntp-filter-groups-by-wildmat
                                    fn-wildmat-parse
                                    fn-nntp-single fn-nntp-multi))))))

(local
 (defthm fn-odr-newsgroups-effects-true-listp
   (true-listp (fn-nntp-result-effects
                (fn-nntp-list-newsgroups-described session archive descs args)))
   :hints (("Goal" :in-theory (e/d (fn-nntp-list-newsgroups-described
                                    fn-nntp-single fn-nntp-multi
                                    fn-nntp-make-result fn-nntp-result-effects)
                                   (fn-nntp-described-lines
                                    fn-nntp-filter-groups-by-wildmat
                                    fn-wildmat-parse))))))

(local
 (defthm fn-odr-motd-has-no-offer
   (not (fn-post-offeredp
         (fn-nntp-result-effects (fn-nntp-list-motd session env args))))
   :hints (("Goal" :in-theory (e/d (fn-nntp-list-motd)
                                   (fn-nntp-motd-lines fn-post-offeredp
                                    fn-nntp-single fn-nntp-multi))))))

(local
 (defthm fn-odr-motd-effects-true-listp
   (true-listp (fn-nntp-result-effects (fn-nntp-list-motd session env args)))
   :hints (("Goal" :in-theory (e/d (fn-nntp-list-motd fn-nntp-single
                                    fn-nntp-multi fn-nntp-make-result
                                    fn-nntp-result-effects)
                                   (fn-nntp-motd-lines))))))

;; One framed LIST NEWSGROUPS or LIST MOTD line, through the pinned
;; dispatcher chain.

(defthm fn-served-dispatch-list-newsgroups
  (let* ((as (fn-served-conn-session conn))
         (ps (fn-auth-session-base as))
         (pst (fn-peer-session-base ps))
         (ns (fn-post-session-base pst))
         (tokens (fn-nntp-tokenize line)))
    (implies (and (fn-auth-sessionp as)
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
                  (fn-nntp-keyword-tokenp (car tokens))
                  (fn-nntp-keywordp (car tokens) "LIST")
                  (fn-nntp-keyword-tokenp (cadr tokens))
                  (fn-nntp-keywordp (cadr tokens) "NEWSGROUPS"))
             (and (equal (fn-served-result-effects
                          (fn-served-dispatch conn (list :command line)))
                         (fn-nntp-result-effects
                          (fn-nntp-list-newsgroups-described
                           ns (fn-served-conn-archive conn)
                           (fn-nntp-listing-descs
                            (fn-inj-config-listing (fn-served-conn-config conn)))
                           (cddr tokens))))
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
                                   fn-nntp-list-newsgroups-described
                                   fn-nntp-list-motd fn-nntp-env-listed
                                   fn-olc-buckets-okp fn-served-conn-pinned-index
                                   fn-nntp-projectionp
                                   fn-nntp-tokenize fn-auth-sessionp
                                   fn-peer-sessionp fn-post-sessionp
                                   fn-nntp-sessionp fn-auth-gatedp
                                   fn-nntp-upcase-keyword
                                   fn-nntp-keyword-tokenp fn-nntp-command-inputp
                                   fn-nntp-command-arguments-at-mostp))
           :use ((:instance fn-nntp-archive-command-pinned-list-newsgroups
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

(defthm fn-served-dispatch-list-motd
  (let* ((as (fn-served-conn-session conn))
         (ps (fn-auth-session-base as))
         (pst (fn-peer-session-base ps))
         (ns (fn-post-session-base pst))
         (tokens (fn-nntp-tokenize line)))
    (implies (and (fn-auth-sessionp as)
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
                  (fn-nntp-keyword-tokenp (car tokens))
                  (fn-nntp-keywordp (car tokens) "LIST")
                  (fn-nntp-keyword-tokenp (cadr tokens))
                  (fn-nntp-keywordp (cadr tokens) "MOTD"))
             (and (equal (fn-served-result-effects
                          (fn-served-dispatch conn (list :command line)))
                         (fn-nntp-result-effects
                          (fn-nntp-list-motd
                           ns (fn-nntp-env-listed
                               (fn-served-conn-observation conn) nil
                               (and (fn-inj-config-allow (fn-served-conn-config conn)) t)
                               (fn-inj-config-listing (fn-served-conn-config conn)))
                           (cddr tokens))))
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
                                   fn-nntp-list-newsgroups-described
                                   fn-nntp-list-motd fn-nntp-env-listed
                                   fn-olc-buckets-okp fn-served-conn-pinned-index
                                   fn-nntp-projectionp
                                   fn-nntp-tokenize fn-auth-sessionp
                                   fn-peer-sessionp fn-post-sessionp
                                   fn-nntp-sessionp fn-auth-gatedp
                                   fn-nntp-upcase-keyword
                                   fn-nntp-keyword-tokenp fn-nntp-command-inputp
                                   fn-nntp-command-arguments-at-mostp))
           :use ((:instance fn-nntp-archive-command-pinned-list-motd
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

;; The served step: one read carrying one LIST NEWSGROUPS (or LIST MOTD)
;; line answers the listing the connection's pinned configuration carries.

(defthm fn-served-step-list-newsgroups-is-the-described-listing
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
                  (fn-nntp-keyword-tokenp (car tokens))
                  (fn-nntp-keywordp (car tokens) "LIST")
                  (fn-nntp-keyword-tokenp (cadr tokens))
                  (fn-nntp-keywordp (cadr tokens) "NEWSGROUPS"))
             (equal (fn-served-result-effects
                     (fn-served-step conn (append prefix (list byte))))
                    (fn-nntp-result-effects
                     (fn-nntp-list-newsgroups-described
                      ns (fn-served-conn-archive conn)
                      (fn-nntp-listing-descs
                       (fn-inj-config-listing (fn-served-conn-config conn)))
                      (cddr tokens))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-served-step-of-one-framed-event
                  (event (list :command line)))
                 (:instance fn-served-dispatch-list-newsgroups
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
                            fn-served-dispatch-list-newsgroups
                            fn-served-step fn-served-dispatch
                            fn-wire-feed-byte fn-wire-feed-proper fn-wire-statep
                            fn-nntp-list-newsgroups-described fn-nntp-list-motd
                            fn-nntp-env-listed fn-nntp-projectionp
                            fn-midx-correspondencep fn-gidx-build
                            fn-nntp-tokenize fn-auth-sessionp
                            fn-peer-sessionp fn-post-sessionp
                            fn-nntp-sessionp fn-auth-gatedp
                            fn-nntp-keywordp fn-nntp-keyword-tokenp
                            fn-nntp-command-inputp
                            fn-nntp-command-arguments-at-mostp)))))

(defthm fn-served-step-list-motd-is-the-configured-message
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
                  (fn-nntp-keyword-tokenp (car tokens))
                  (fn-nntp-keywordp (car tokens) "LIST")
                  (fn-nntp-keyword-tokenp (cadr tokens))
                  (fn-nntp-keywordp (cadr tokens) "MOTD"))
             (equal (fn-served-result-effects
                     (fn-served-step conn (append prefix (list byte))))
                    (fn-nntp-result-effects
                     (fn-nntp-list-motd
                      ns (fn-nntp-env-listed
                          (fn-served-conn-observation conn) nil
                          (and (fn-inj-config-allow (fn-served-conn-config conn)) t)
                          (fn-inj-config-listing (fn-served-conn-config conn)))
                      (cddr tokens))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-served-step-of-one-framed-event
                  (event (list :command line)))
                 (:instance fn-served-dispatch-list-motd
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
                            fn-served-dispatch-list-motd
                            fn-served-step fn-served-dispatch
                            fn-wire-feed-byte fn-wire-feed-proper fn-wire-statep
                            fn-nntp-list-newsgroups-described fn-nntp-list-motd
                            fn-nntp-env-listed fn-nntp-projectionp
                            fn-midx-correspondencep fn-gidx-build
                            fn-nntp-tokenize fn-auth-sessionp
                            fn-peer-sessionp fn-post-sessionp
                            fn-nntp-sessionp fn-auth-gatedp
                            fn-nntp-keywordp fn-nntp-keyword-tokenp
                            fn-nntp-command-inputp
                            fn-nntp-command-arguments-at-mostp)))))

;; What the listing holds: each served group's description from the
;; configuration's slot, and the node's message.

(defthm fn-oag-description-of-descs
  (equal (fn-nntp-description-of g (fn-oag-descs names v))
         (if (and (member-equal g names)
                  (consp (fn-cfg-description-octets v g)))
             (fn-cfg-description-octets v g)
           nil))
  :hints (("Goal" :induct (fn-oag-descs names v)
           :in-theory (e/d (fn-oag-descs fn-nntp-description-of)
                           (fn-cfg-description-octets)))))

; KEYSTONE.  The description LIST NEWSGROUPS is handed for G on a
; connection pinned to the owner's posting configuration of CFG is G's
; description in CFG's slot, when G is served and has one.
(defthm fn-oag-description-of-the-listing
  (equal (fn-nntp-description-of
          g (fn-nntp-listing-descs
             (fn-inj-config-listing (fn-oag-post-config cfg max-octets))))
         (if (and (member-equal g (fn-cnode-served-of cfg))
                  (consp (fn-cfg-description-octets (fn-cfg-value cfg) g)))
             (fn-cfg-description-octets (fn-cfg-value cfg) g)
           nil))
  :hints (("Goal" :in-theory (e/d (fn-oag-post-config fn-oag-listing
                                   fn-nntp-listing-descs)
                                  (fn-oag-descs fn-cfg-description-octets
                                   fn-cnode-served-of)))))

; KEYSTONE.  The message LIST MOTD is handed is the node's lines in CFG.
(defthm fn-oag-motd-of-the-listing
  (equal (fn-nntp-listing-motd
          (fn-inj-config-listing (fn-oag-post-config cfg max-octets)))
         (fn-cfg-motd-lines (fn-cfg-value cfg)))
  :hints (("Goal" :in-theory (e/d (fn-oag-post-config fn-oag-listing
                                   fn-nntp-listing-motd)
                                  (fn-oag-descs fn-cfg-motd-lines
                                   fn-cnode-served-of)))))
