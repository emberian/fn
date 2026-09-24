;; LIST COUNTS and the numbered Message-ID answer, stated over the served
;; step the host runs.
;;
;; Host path (reader): host/native/owner.lisp calls fn-owner-chunk
;; (host/owner-host.lisp), which runs fn-scar-ocfg-read-tls-prefix; the chain
;; recorded in books/owner-verdict-read.lisp equates that with fn-own-read on
;; the connection, and fn-own-read-is-served-step-on-pinned-prefix
;; (books/owner-invariants) with fn-served-step over the connection's pinned
;; archive, trie and group buckets.  The keystones below are over
;; fn-served-step; the function-level keystones they carry are in
;; books/nntp-list-counts.lisp.
;;
;; The two relations assumed here are the ones the owner carries for every
;; connection (fn-own-conn-okp in fn-own-relation): the pinned trie is the
;; build of the pinned archive's articles (fn-midx-correspondencep), and the
;; group buckets are either absent or the build of those articles.  Framing
;; is a hypothesis, as in books/owner-verdict-read.lisp.
(in-package "ACL2")
(include-book "owner-verdict-read")
(include-book "nntp-list-counts")

(defun fn-olc-buckets-okp (conn)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-midx-correspondencep
        (fn-served-conn-index conn)
        (fn-state-articles (fn-served-conn-archive conn)))
       (or (null (fn-served-conn-group-index conn))
           (equal (fn-served-conn-group-index conn)
                  (fn-gidx-build
                   (fn-state-articles (fn-served-conn-archive conn)))))))

(local
 (defthm fn-olc-pinned-index-corresponds
   (implies (fn-olc-buckets-okp conn)
            (fn-gidx-pin-correspondencep (fn-served-conn-pinned-index conn)
                                         (fn-served-conn-archive conn)))
   :hints (("Goal" :in-theory (e/d (fn-gidx-pin-correspondencep
                                    fn-served-conn-pinned-index
                                    fn-midx-correspondencep)
                                   (fn-gidx-pinp fn-midx-build fn-gidx-build))))))

(local
 (defthm fn-olc-buckets-okp-gives-trie
   (implies (fn-olc-buckets-okp conn)
            (fn-midx-correspondencep
             (fn-served-conn-index conn)
             (fn-state-articles (fn-served-conn-archive conn))))
   :hints (("Goal" :in-theory (disable fn-midx-correspondencep)))))

(local
 (defthm fn-olc-pin-trie-of-unpinned
   (implies (not (fn-gidx-pinp x))
            (equal (fn-gidx-pin-trie x) x))
   :hints (("Goal" :in-theory (e/d (fn-gidx-pin-trie) (fn-gidx-pinp))))))

(local
 (defthm fn-olc-pinned-trie-is-the-index
   (implies (fn-olc-buckets-okp conn)
            (equal (fn-gidx-pin-trie (fn-served-conn-pinned-index conn))
                   (fn-served-conn-index conn)))
   :hints (("Goal" :in-theory (e/d (fn-served-conn-pinned-index
                                    fn-midx-correspondencep)
                                   (fn-gidx-pin fn-gidx-pin-trie fn-gidx-pinp
                                    fn-midx-build fn-gidx-build))))))

(local
 (defthm fn-olc-list-counts-has-no-offer
   (not (fn-post-offeredp
         (fn-nntp-result-effects
          (fn-nntp-list-counts-command session archive args))))
   :hints (("Goal" :in-theory (e/d (fn-nntp-list-counts-command
                                    fn-nntp-list-counts)
                                   (fn-nntp-counts-lines fn-post-offeredp
                                    fn-nntp-filter-groups-by-wildmat
                                    fn-wildmat-parse
                                    fn-nntp-single fn-nntp-multi))))))

(local
 (defthm fn-olc-list-counts-effects-true-listp
   (true-listp (fn-nntp-result-effects
                (fn-nntp-list-counts-command session archive args)))
   :hints (("Goal" :in-theory (e/d (fn-nntp-list-counts-command
                                    fn-nntp-list-counts fn-nntp-single
                                    fn-nntp-multi fn-nntp-make-result
                                    fn-nntp-result-effects)
                                   (fn-nntp-counts-lines
                                    fn-nntp-filter-groups-by-wildmat
                                    fn-wildmat-parse))))))

;; One framed LIST COUNTS line, through the pinned dispatcher chain.

(defthm fn-served-dispatch-list-counts
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
                  (fn-nntp-projectionp (fn-served-conn-archive conn))
                  (fn-olc-buckets-okp conn)
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp tokens)
                  (consp (cdr tokens))
                  (fn-nntp-keyword-tokenp (car tokens))
                  (fn-nntp-keywordp (car tokens) "LIST")
                  (fn-nntp-keyword-tokenp (cadr tokens))
                  (fn-nntp-keywordp (cadr tokens) "COUNTS"))
             (and (equal (fn-served-result-effects
                          (fn-served-dispatch conn (list :command line)))
                         (fn-nntp-result-effects
                          (fn-nntp-list-counts-command
                           ns (fn-served-conn-archive conn) (cddr tokens))))
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
                                   fn-nntp-list-counts-command
                                   fn-olc-buckets-okp fn-served-conn-pinned-index
                                   fn-nntp-projectionp
                                   fn-nntp-tokenize fn-auth-sessionp
                                   fn-peer-sessionp fn-post-sessionp
                                   fn-nntp-sessionp fn-auth-gatedp
                                   fn-nntp-upcase-keyword
                                   fn-nntp-keyword-tokenp fn-nntp-command-inputp
                                   fn-nntp-command-arguments-at-mostp))
           :use ((:instance fn-nntp-archive-command-pinned-list-counts
                  (session (fn-post-session-base
                            (fn-peer-session-base
                             (fn-auth-session-base (fn-served-conn-session conn)))))
                  (archive (fn-served-conn-archive conn))
                  (index (fn-served-conn-pinned-index conn))
                  (verdicts (fn-served-conn-verdicts conn))
                  (env (fn-nntp-env (fn-served-conn-observation conn) nil
                                    (and (fn-inj-config-allow
                                          (fn-served-conn-config conn)) t)))
                  (keyword (car (fn-nntp-tokenize line)))
                  (args (cdr (fn-nntp-tokenize line))))))))

(defthm fn-olc-buckets-okp-of-with-wire
  (equal (fn-olc-buckets-okp (fn-ovr-with-wire conn w))
         (fn-olc-buckets-okp conn))
  :hints (("Goal" :in-theory (enable fn-ovr-with-wire))))

;; The served step: one read carrying one LIST COUNTS line answers the
;; archive fold's counts list (fn-nntp-list-counts-command), computed from the
;; pinned buckets.

(defthm fn-served-step-list-counts-is-the-archive-counts
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
                  (fn-nntp-projectionp (fn-served-conn-archive conn))
                  (fn-olc-buckets-okp conn)
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp tokens)
                  (consp (cdr tokens))
                  (fn-nntp-keyword-tokenp (car tokens))
                  (fn-nntp-keywordp (car tokens) "LIST")
                  (fn-nntp-keyword-tokenp (cadr tokens))
                  (fn-nntp-keywordp (cadr tokens) "COUNTS"))
             (equal (fn-served-result-effects
                     (fn-served-step conn (append prefix (list byte))))
                    (fn-nntp-result-effects
                     (fn-nntp-list-counts-command
                      ns (fn-served-conn-archive conn) (cddr tokens))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-served-step-of-one-framed-event
                  (event (list :command line)))
                 (:instance fn-served-dispatch-list-counts
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
                            fn-served-dispatch-list-counts
                            fn-served-step fn-served-dispatch
                            fn-wire-feed-byte fn-wire-feed-proper fn-wire-statep
                            fn-nntp-list-counts-command fn-nntp-projectionp
                            fn-midx-correspondencep fn-gidx-build
                            fn-nntp-tokenize fn-auth-sessionp
                            fn-peer-sessionp fn-post-sessionp
                            fn-nntp-sessionp fn-auth-gatedp
                            fn-nntp-keywordp fn-nntp-keyword-tokenp
                            fn-nntp-command-inputp
                            fn-nntp-command-arguments-at-mostp)))))

;; ARTICLE, HEAD, BODY and STAT with a Message-ID argument.

(defun fn-olc-retrieval-kind (keyword)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((fn-nntp-keywordp keyword "ARTICLE") :article)
        ((fn-nntp-keywordp keyword "HEAD") :head)
        ((fn-nntp-keywordp keyword "BODY") :body)
        (t :stat)))

(defun fn-olc-retrieval-keywordp (keyword)
  (declare (xargs :guard t :verify-guards nil))
  (or (fn-nntp-keywordp keyword "ARTICLE")
      (fn-nntp-keywordp keyword "HEAD")
      (fn-nntp-keywordp keyword "BODY")
      (fn-nntp-keywordp keyword "STAT")))

(local
 (defthm fn-olc-msgid-retrieval-has-no-offer
   (not (fn-post-offeredp
         (fn-nntp-result-effects
          (fn-nntp-msgid-retrieval session archive kind token))))
   :hints (("Goal" :in-theory (e/d (fn-nntp-msgid-retrieval
                                    fn-nntp-article-response fn-post-offeredp
                                    fn-nntp-reply-effect)
                                   (fn-nntp-single fn-nntp-stuff-lines
                                    fn-nntp-crlf fn-find-article))))))

(local
 (defthm fn-olc-msgid-retrieval-effects-true-listp
   (true-listp (fn-nntp-result-effects
                (fn-nntp-msgid-retrieval session archive kind token)))
   :hints (("Goal" :in-theory (e/d (fn-nntp-msgid-retrieval
                                    fn-nntp-article-response fn-nntp-single
                                    fn-nntp-make-result fn-nntp-result-effects)
                                   (fn-find-article fn-nntp-stuff-lines))))))

(defthm fn-served-dispatch-msgid-retrieval
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
                  (fn-olc-buckets-okp conn)
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp tokens)
                  (consp (cdr tokens)) (null (cddr tokens))
                  (fn-nntp-keyword-tokenp (car tokens))
                  (fn-olc-retrieval-keywordp (car tokens))
                  (fn-nntp-message-id-tokenp (cadr tokens)))
             (and (equal (fn-served-result-effects
                          (fn-served-dispatch conn (list :command line)))
                         (fn-nntp-result-effects
                          (fn-nntp-msgid-retrieval
                           ns (fn-served-conn-archive conn)
                           (fn-olc-retrieval-kind (car tokens))
                           (cadr tokens))))
                  (equal (fn-served-conn-wire
                          (fn-served-result-conn
                           (fn-served-dispatch conn (list :command line))))
                         (fn-served-conn-wire conn)))))
  :hints (("Goal" :in-theory (e/d (fn-served-dispatch fn-auth-step-pinned
                                   fn-auth-command fn-auth-delegate-pinned
                                   fn-peer-step-pinned fn-peer-delegate-pinned
                                   fn-nntp-post-step-pinned fn-nntp-step-pinned
                                   fn-nntp-command-pinned
                                   fn-nntp-archive-command-pinned
                                   fn-olc-retrieval-kind
                                   fn-olc-retrieval-keywordp
                                   fn-auth-tls-eventp fn-nntp-keywordp
                                   fn-nntp-archive-keywordp)
                                  (fn-nntp-msgid-retrieval-indexed
                                   fn-nntp-msgid-retrieval
                                   fn-olc-buckets-okp fn-served-conn-pinned-index
                                   fn-midx-correspondencep
                                   fn-nntp-tokenize fn-auth-sessionp
                                   fn-peer-sessionp fn-post-sessionp
                                   fn-nntp-sessionp fn-auth-gatedp
                                   fn-nntp-upcase-keyword
                                   fn-nntp-message-id-tokenp
                                   fn-nntp-keyword-tokenp fn-nntp-command-inputp
                                   fn-nntp-command-arguments-at-mostp)))))

;; The served step: one read carrying one ARTICLE/HEAD/BODY/STAT <msgid> line
;; answers the article with its number in the selected group, or 0
;; (fn-nntp-msgid-local-number); fn-nntp-msgid-number-retrieves-the-same-
;; article (books/nntp-list-counts) is why that number may be used.

(defthm fn-served-step-msgid-retrieval-carries-the-local-number
  (let* ((w0 (fn-served-conn-wire conn))
         (w1 (fn-wire-result-state (fn-wire-feed-proper w0 prefix)))
         (w2 (fn-wire-result-state (fn-wire-feed-byte w1 byte)))
         (as (fn-served-conn-session conn))
         (ps (fn-auth-session-base as))
         (pst (fn-peer-session-base ps))
         (ns (fn-post-session-base pst))
         (tokens (fn-nntp-tokenize line))
         (article (fn-find-article (fn-nntp-token-string (cadr tokens))
                                   (fn-state-articles
                                    (fn-served-conn-archive conn)))))
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
                  (fn-olc-buckets-okp conn)
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp tokens)
                  (consp (cdr tokens)) (null (cddr tokens))
                  (fn-nntp-keyword-tokenp (car tokens))
                  (fn-olc-retrieval-keywordp (car tokens))
                  (fn-nntp-message-id-tokenp (cadr tokens))
                  (consp article))
             (equal (fn-served-result-effects
                     (fn-served-step conn (append prefix (list byte))))
                    (fn-nntp-result-effects
                     (fn-nntp-article-response
                      ns article (fn-nntp-msgid-local-number ns article)
                      (fn-olc-retrieval-kind (car tokens)) nil nil)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-served-step-of-one-framed-event
                  (event (list :command line)))
                 (:instance fn-served-dispatch-msgid-retrieval
                  (conn (fn-ovr-with-wire
                         conn
                         (fn-wire-result-state
                          (fn-wire-feed-byte
                           (fn-wire-result-state
                            (fn-wire-feed-proper (fn-served-conn-wire conn) prefix))
                           byte))))))
           :in-theory (e/d (fn-served-closed-wirep fn-served-tls-handshakingp
                            fn-nntp-msgid-retrieval)
                           (fn-olc-buckets-okp
                            fn-served-step-of-one-framed-event
                            fn-served-dispatch-msgid-retrieval
                            fn-served-step fn-served-dispatch
                            fn-wire-feed-byte fn-wire-feed-proper fn-wire-statep
                            fn-nntp-article-response fn-find-article
                            fn-nntp-msgid-local-number
                            fn-olc-retrieval-kind fn-olc-retrieval-keywordp
                            fn-nntp-tokenize fn-auth-sessionp
                            fn-peer-sessionp fn-post-sessionp
                            fn-nntp-sessionp fn-auth-gatedp
                            fn-nntp-message-id-tokenp
                            fn-nntp-keywordp fn-nntp-keyword-tokenp
                            fn-nntp-command-inputp
                            fn-nntp-command-arguments-at-mostp)))))
