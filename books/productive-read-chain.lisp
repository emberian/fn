; W6b READ composition discovery. Actual wire/owner joins and the complete
; numbered host-read theorem are admitted in pcr61; the final weaker theorem
; removes seven redundant premises by proved implications. This remains outside
; qualification roots until complete teeth, Message-ID/absent-read variants and
; matching union/native evidence land. No W6b completion claim.
(in-package "ACL2")
(include-book "productive-read")
(defconst *fn-pcr-article-keyword* '(65 82 84 73 67 76 69))

(defthm fn-pcr-command-article-reaches-the-pinned-archive-by-definition
  (implies (fn-nntp-session-projected session)
           (equal (fn-nntp-command-pinned session archive index verdicts env
                                          (list *fn-pcr-article-keyword* token) fn-arena)
                  (fn-nntp-archive-command-pinned session archive index verdicts env
                                                 *fn-pcr-article-keyword* (list token) fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-command-pinned fn-nntp-archive-keywordp
                                  fn-nntp-keywordp fn-nntp-keyword-tokenp)
                                 (fn-nntp-archive-command-pinned fn-nntp-session-projected
                                  fn-nntp-session-command fn-nntp-single)))))

(defthm fn-pcr-command-line-reaches-the-reader-dispatch-by-definition
  (implies (and (fn-nntp-sessionp session)
                (equal (fn-nntp-session-openp session) t)
                (fn-nntp-command-inputp line)
                (fn-nntp-command-arguments-at-mostp (list *fn-pcr-article-keyword* token))
                (equal (fn-nntp-tokenize line) (list *fn-pcr-article-keyword* token)))
           (equal (fn-nntp-step-pinned session archive index verdicts env
                                       (list :command line) fn-arena)
                  (fn-nntp-command-pinned session archive index verdicts env
                                          (list *fn-pcr-article-keyword* token) fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-step-pinned)
                                 (fn-nntp-sessionp fn-nntp-session-openp fn-nntp-command-inputp
                                  fn-nntp-tokenize fn-nntp-command-pinned fn-nntp-single
                                  fn-nntp-command-arguments-at-mostp)))))

(defthm fn-pcr-post-delegates-a-read-without-offer-by-definition
  (implies (and (fn-post-sessionp ps)
                (not (fn-post-session-awaiting ps))
                (not (fn-post-offeredp
                      (fn-nntp-result-effects
                       (fn-nntp-step-pinned (fn-post-session-base ps) archive index verdicts
                                            (fn-post-reader-env config observation)
                                            event fn-arena)))))
           (let ((r (fn-nntp-step-pinned (fn-post-session-base ps) archive index verdicts
                                         (fn-post-reader-env config observation) event fn-arena))
                 (p (fn-nntp-post-step-pinned ps archive index verdicts config
                                              observation injection event fn-arena)))
             (and (equal (fn-post-result-effects p) (fn-nntp-result-effects r))
                  (null (fn-post-result-submission p))
                  (equal (fn-post-session-base (fn-post-result-session p))
                         (fn-nntp-result-session r)))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-post-step-pinned)
                                 (fn-nntp-step-pinned fn-post-sessionp fn-post-session-awaiting
                                  fn-post-offeredp fn-post-reader-env fn-nntp-result-effects
                                  fn-nntp-result-session fn-post-result-effects fn-post-result-session
                                  fn-post-result-submission fn-post-make-result fn-post-make-session
                                  fn-post-session-base)))))

(defthm fn-pcr-peer-reader-delegates-to-post-by-definition
  (implies (and (fn-peer-sessionp ps) (null (fn-peer-session-peer ps)))
           (let ((r (fn-nntp-post-step-pinned (fn-peer-session-base ps) archive index verdicts
                                               config observation injection event fn-arena))
                 (p (fn-peer-step-pinned ps archive index verdicts config
                                         observation injection event fn-arena)))
             (and (equal (fn-post-result-effects p) (fn-post-result-effects r))
                  (equal (fn-post-result-submission p) (fn-post-result-submission r))
                  (equal (fn-peer-session-base (fn-post-result-session p))
                         (fn-post-result-session r)))))
  :hints (("Goal" :in-theory (e/d (fn-peer-step-pinned fn-peer-delegate-pinned)
                                 (fn-nntp-post-step-pinned fn-peer-sessionp fn-peer-session-peer
                                  fn-post-result-effects fn-post-result-session fn-post-result-submission
                                  fn-post-make-result fn-peer-with-base fn-peer-session-base)))))

(defthm fn-pcr-auth-article-is-not-intercepted-by-definition
  (implies (or (not (fn-auth-config-requiredp (fn-auth-session-config as)))
               (fn-auth-session-subject as))
           (not (fn-auth-command as config *fn-pcr-article-keyword* (list token))))
  :hints (("Goal" :in-theory (e/d (fn-auth-command fn-auth-gatedp fn-auth-compressed-refusedp
                                  fn-nntp-keywordp)
                                 (fn-auth-config-requiredp fn-auth-session-config
                                  fn-auth-session-subject fn-auth-postingp
                                  fn-auth-starttls fn-auth-authinfo fn-auth-compress
                                  fn-auth-xredeem fn-zc-activep)))))

(defthm fn-pcr-auth-reader-delegates-an-authorized-article-by-definition
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (not (fn-auth-sasl-waitingp as))
                (or (not (fn-auth-config-requiredp (fn-auth-session-config as)))
                    (fn-auth-session-subject as))
                (fn-nntp-command-inputp line)
                (fn-nntp-command-arguments-at-mostp (list *fn-pcr-article-keyword* token))
                (equal (fn-nntp-tokenize line) (list *fn-pcr-article-keyword* token)))
           (let ((r (fn-peer-step-pinned
                     (fn-auth-view-session as config) (fn-auth-view-archive as config archive)
                     (fn-auth-view-index as config archive index) verdicts
                     (fn-auth-view-config as (fn-auth-moderation-config as config) archive)
                     observation injection (list :command line) fn-arena))
                 (p (fn-auth-step-pinned as archive index verdicts config observation injection
                                         (list :command line) fn-arena)))
             (and (equal (fn-post-result-effects p) (fn-post-result-effects r))
                  (equal (fn-post-result-submission p) (fn-post-result-submission r))
                  (equal (fn-auth-session-base (fn-post-result-session p))
                         (fn-post-result-session r)))))
  :hints (("Goal" :in-theory (e/d (fn-auth-step-pinned fn-auth-delegate-pinned
                                  fn-auth-tls-eventp fn-auth-redeem-eventp fn-auth-context-eventp
                                  fn-nntp-keyword-tokenp
                                  fn-pcr-auth-article-is-not-intercepted-by-definition fn-auth-with-base)
                                 (fn-auth-sessionp fn-auth-session-handshakingp fn-auth-sasl-waitingp
                                  fn-post-result-effects fn-post-result-session fn-post-result-submission
                                  fn-post-make-result fn-auth-session-base
                                  fn-auth-command fn-auth-view-session fn-auth-view-archive
                                  fn-auth-view-index fn-auth-view-config fn-auth-moderation-config
                                  fn-peer-step-pinned fn-nntp-command-inputp fn-nntp-tokenize
                                  fn-nntp-command-arguments-at-mostp)))))

(defthm fn-pcr-article-keeps-the-pinned-view-by-definition
  (implies (equal (fn-nntp-tokenize line) (list *fn-pcr-article-keyword* token))
           (not (fn-served-advance-eventp (list :command line))))
  :hints (("Goal" :in-theory (e/d (fn-served-advance-eventp fn-nntp-keywordp)
                                 (fn-nntp-tokenize fn-nntp-command-inputp)))))

(defthm fn-pcr-served-reader-dispatch-is-the-auth-answer-by-definition
  (let ((r (fn-auth-step-pinned (fn-served-conn-session conn)
                                (fn-served-conn-archive conn)
                                (fn-served-conn-pinned-index conn)
                                (fn-served-conn-verdicts conn)
                                (fn-served-conn-config conn)
                                (fn-served-conn-observation conn)
                                (fn-served-conn-injection conn)
                                (list :command line) fn-arena))
        (p (fn-served-dispatch conn (list :command line) fn-arena)))
    (implies (and (equal (fn-nntp-tokenize line) (list *fn-pcr-article-keyword* token))
                  (null (fn-post-result-submission r))
                  (true-listp (fn-post-result-effects r)))
             (and (equal (fn-served-result-effects p) (fn-post-result-effects r))
                  (equal (fn-served-conn-session (fn-served-result-conn p))
                         (fn-post-result-session r))
                  (equal (fn-served-conn-pinned (fn-served-result-conn p))
                         (fn-served-conn-pinned conn))
                  (equal (fn-served-conn-archive (fn-served-result-conn p))
                         (fn-served-conn-archive conn))
                  (equal (fn-served-conn-index (fn-served-result-conn p))
                         (fn-served-conn-index conn)))))
  :hints (("Goal" :in-theory (e/d (fn-served-dispatch fn-served-dispatch-core
                                  fn-pcr-article-keeps-the-pinned-view-by-definition)
                                 (fn-auth-step-pinned fn-post-result-submission
                                  fn-post-result-session fn-post-result-effects
                                  fn-post-offeredp fn-served-advance-eventp
                                  fn-served-make-result fn-served-make-conn-live
                                  fn-served-conn-session fn-served-conn-pinned
                                  fn-served-conn-archive fn-served-conn-index
                                  fn-served-result-conn fn-served-result-effects
                                  fn-wire-begin-article-with-line-limit)))))

(defthm fn-pcr-command-line-answers-the-numbered-article
  (let* ((group (fn-nntp-session-group session))
         (number (fn-nntp-decimal-value token))
         (article (fn-nntp-find-group-number group number (fn-state-articles archive)))
         (server (fn-nntp-xref-server env)))
    (implies (and (fn-nntp-sessionp session)
                  (equal (fn-nntp-session-openp session) t)
                  (fn-nntp-session-projected session)
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp (list *fn-pcr-article-keyword* token))
                  (equal (fn-nntp-tokenize line) (list *fn-pcr-article-keyword* token))
                  (fn-arena-p fn-arena)
                  (fn-nntp-number-tokenp token)
                  group (consp article) server
                  (fn-gidx-pinp index)
                  (not (fn-nntp-number-withdrawn-p session archive index token))
                  (fn-nntp-response-okp-of-bytes article (fn-nntp-article-bytes article fn-arena) :article)
                  (fn-nntp-response-okp-of-bytes article (fn-pcr-served-octets server article fn-arena) :article))
             (equal (fn-nntp-step-pinned session archive index verdicts env
                                         (list :command line) fn-arena)
                    (fn-pcr-220-reply session article number group server fn-arena))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-pcr-retrieval-answers-220-with-the-stored-octets
                            (trie (fn-gidx-pin-trie index)) (server (fn-nntp-xref-server env)))
                 (:instance fn-nntp-archive-command-pinned-article-head-is-served
                            (keyword *fn-pcr-article-keyword*) (args (list token))))
           :in-theory (e/d (fn-rcompat-retrieval-kind fn-nntp-keywordp)
                           (fn-nntp-step-pinned fn-nntp-command-pinned
                            fn-nntp-archive-command-pinned fn-rcompat-retrieval
                            fn-gidx-pinp fn-nntp-xref-server fn-pcr-220-reply
                            fn-nntp-number-tokenp fn-nntp-response-okp-of-bytes
                            fn-nntp-article-bytes fn-pcr-served-octets)))))

(defthm fn-pcr-220-is-a-reply-without-an-offer-by-definition
  (let ((r (fn-pcr-220-reply session article number group server fn-arena)))
    (and (true-listp (fn-nntp-result-effects r))
         (not (fn-post-offeredp (fn-nntp-result-effects r)))))
  :hints (("Goal" :in-theory (e/d (fn-pcr-220-reply fn-post-offeredp
                                  fn-nntp-reply-effect fn-nntp-begin-article-effect)
                                 (fn-nntp-retrieval-initial fn-nntp-crlf fn-nntp-stuff-lines
                                  fn-nntp-crlf-lines fn-pcr-served-octets fn-nntp-set-cursor
                                  fn-nntp-make-result)))))

(defthm fn-pcr-post-article-has-the-numbered-reply
  (let* ((session (fn-post-session-base ps))
         (env (fn-post-reader-env config observation))
         (group (fn-nntp-session-group session))
         (number (fn-nntp-decimal-value token))
         (article (fn-nntp-find-group-number group number (fn-state-articles archive)))
         (server (fn-nntp-xref-server env))
         (r (fn-pcr-220-reply session article number group server fn-arena))
         (p (fn-nntp-post-step-pinned ps archive index verdicts config observation
                                     injection (list :command line) fn-arena)))
    (implies (and (fn-post-sessionp ps) (not (fn-post-session-awaiting ps))
                  (fn-nntp-sessionp session) (equal (fn-nntp-session-openp session) t)
                  (fn-nntp-session-projected session)
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp (list *fn-pcr-article-keyword* token))
                  (equal (fn-nntp-tokenize line) (list *fn-pcr-article-keyword* token))
                  (fn-arena-p fn-arena) (fn-nntp-number-tokenp token)
                  group (consp article) server (fn-gidx-pinp index)
                  (not (fn-nntp-number-withdrawn-p session archive index token))
                  (fn-nntp-response-okp-of-bytes article (fn-nntp-article-bytes article fn-arena) :article)
                  (fn-nntp-response-okp-of-bytes article (fn-pcr-served-octets server article fn-arena) :article))
             (and (equal (fn-post-result-effects p) (fn-nntp-result-effects r))
                  (null (fn-post-result-submission p))
                  (equal (fn-post-session-base (fn-post-result-session p))
                         (fn-nntp-result-session r)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-pcr-command-line-answers-the-numbered-article
                            (session (fn-post-session-base ps))
                            (env (fn-post-reader-env config observation)))
                 (:instance fn-pcr-post-delegates-a-read-without-offer-by-definition
                            (event (list :command line))))
           :in-theory (disable fn-nntp-post-step-pinned fn-nntp-step-pinned
                               fn-post-sessionp fn-post-session-awaiting fn-post-session-base
                               fn-post-reader-env fn-post-result-effects fn-post-result-session
                               fn-post-result-submission fn-nntp-result-effects fn-nntp-result-session
                               fn-pcr-220-reply fn-post-offeredp
                               fn-nntp-sessionp fn-nntp-session-openp fn-nntp-session-projected
                               fn-nntp-command-inputp fn-nntp-tokenize
                               fn-nntp-command-arguments-at-mostp fn-gidx-pinp
                               fn-nntp-number-tokenp fn-nntp-xref-server
                               fn-nntp-response-okp-of-bytes fn-nntp-article-bytes
                               fn-pcr-served-octets))))

(defthm fn-pcr-peer-article-has-the-numbered-reply
  (let* ((ps (fn-peer-session-base peer))
         (session (fn-post-session-base ps))
         (env (fn-post-reader-env config observation))
         (group (fn-nntp-session-group session))
         (number (fn-nntp-decimal-value token))
         (article (fn-nntp-find-group-number group number (fn-state-articles archive)))
         (server (fn-nntp-xref-server env))
         (r (fn-pcr-220-reply session article number group server fn-arena))
         (p (fn-peer-step-pinned peer archive index verdicts config observation
                                     injection (list :command line) fn-arena)))
    (implies (and (fn-peer-sessionp peer) (null (fn-peer-session-peer peer))
                  (fn-post-sessionp ps) (not (fn-post-session-awaiting ps))
                  (fn-nntp-sessionp session) (equal (fn-nntp-session-openp session) t)
                  (fn-nntp-session-projected session)
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp (list *fn-pcr-article-keyword* token))
                  (equal (fn-nntp-tokenize line) (list *fn-pcr-article-keyword* token))
                  (fn-arena-p fn-arena) (fn-nntp-number-tokenp token)
                  group (consp article) server (fn-gidx-pinp index)
                  (not (fn-nntp-number-withdrawn-p session archive index token))
                  (fn-nntp-response-okp-of-bytes article (fn-nntp-article-bytes article fn-arena) :article)
                  (fn-nntp-response-okp-of-bytes article (fn-pcr-served-octets server article fn-arena) :article))
             (and (equal (fn-post-result-effects p) (fn-nntp-result-effects r))
                  (null (fn-post-result-submission p))
                  (equal (fn-post-session-base (fn-peer-session-base (fn-post-result-session p)))
                         (fn-nntp-result-session r)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-pcr-post-article-has-the-numbered-reply
                            (ps (fn-peer-session-base peer)))
                 (:instance fn-pcr-peer-reader-delegates-to-post-by-definition
                            (ps peer) (event (list :command line))))
           :in-theory (theory 'minimal-theory))))

(defthm fn-pcr-auth-article-has-the-numbered-reply
  (let* ((peer (fn-auth-view-session as config))
         (viewarchive (fn-auth-view-archive as config archive))
         (viewindex (fn-auth-view-index as config archive index))
         (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
         (ps (fn-peer-session-base peer))
         (session (fn-post-session-base ps))
         (env (fn-post-reader-env viewconfig observation))
         (group (fn-nntp-session-group session))
         (number (fn-nntp-decimal-value token))
         (article (fn-nntp-find-group-number group number (fn-state-articles viewarchive)))
         (server (fn-nntp-xref-server env))
         (r (fn-pcr-220-reply session article number group server fn-arena))
         (p (fn-auth-step-pinned as archive index verdicts config observation
                                     injection (list :command line) fn-arena)))
    (implies (and (fn-auth-sessionp as)
                  (not (fn-auth-session-handshakingp as))
                  (not (fn-auth-sasl-waitingp as))
                  (or (not (fn-auth-config-requiredp (fn-auth-session-config as)))
                      (fn-auth-session-subject as))
                  (fn-peer-sessionp peer) (null (fn-peer-session-peer peer))
                  (fn-post-sessionp ps) (not (fn-post-session-awaiting ps))
                  (fn-nntp-sessionp session) (equal (fn-nntp-session-openp session) t)
                  (fn-nntp-session-projected session)
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp (list *fn-pcr-article-keyword* token))
                  (equal (fn-nntp-tokenize line) (list *fn-pcr-article-keyword* token))
                  (fn-arena-p fn-arena) (fn-nntp-number-tokenp token)
                  group (consp article) server (fn-gidx-pinp viewindex)
                  (not (fn-nntp-number-withdrawn-p session viewarchive viewindex token))
                  (fn-nntp-response-okp-of-bytes article (fn-nntp-article-bytes article fn-arena) :article)
                  (fn-nntp-response-okp-of-bytes article (fn-pcr-served-octets server article fn-arena) :article))
             (and (equal (fn-post-result-effects p) (fn-nntp-result-effects r))
                  (null (fn-post-result-submission p))
                  (equal (fn-post-session-base (fn-peer-session-base (fn-auth-session-base (fn-post-result-session p))))
                         (fn-nntp-result-session r)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-pcr-peer-article-has-the-numbered-reply
                            (peer (fn-auth-view-session as config))
                            (archive (fn-auth-view-archive as config archive))
                            (index (fn-auth-view-index as config archive index))
                            (config (fn-auth-view-config as (fn-auth-moderation-config as config) archive)))
                 fn-pcr-auth-reader-delegates-an-authorized-article-by-definition)
           :in-theory (theory 'minimal-theory))))

(defthm fn-pcr-served-dispatch-has-the-numbered-reply
  (let* ((as (fn-served-conn-session conn))
         (config (fn-served-conn-config conn))
         (archive (fn-served-conn-archive conn))
         (index (fn-served-conn-pinned-index conn))
         (observation (fn-served-conn-observation conn))
         (peer (fn-auth-view-session as config))
         (viewarchive (fn-auth-view-archive as config archive))
         (viewindex (fn-auth-view-index as config archive index))
         (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
         (ps (fn-peer-session-base peer))
         (session (fn-post-session-base ps))
         (env (fn-post-reader-env viewconfig observation))
         (group (fn-nntp-session-group session))
         (number (fn-nntp-decimal-value token))
         (article (fn-nntp-find-group-number group number (fn-state-articles viewarchive)))
         (server (fn-nntp-xref-server env))
         (r (fn-pcr-220-reply session article number group server fn-arena))
         (p (fn-served-dispatch conn (list :command line) fn-arena)))
    (implies (and (fn-auth-sessionp as)
                  (not (fn-auth-session-handshakingp as))
                  (not (fn-auth-sasl-waitingp as))
                  (or (not (fn-auth-config-requiredp (fn-auth-session-config as)))
                      (fn-auth-session-subject as))
                  (fn-peer-sessionp peer) (null (fn-peer-session-peer peer))
                  (fn-post-sessionp ps) (not (fn-post-session-awaiting ps))
                  (fn-nntp-sessionp session) (equal (fn-nntp-session-openp session) t)
                  (fn-nntp-session-projected session)
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp (list *fn-pcr-article-keyword* token))
                  (equal (fn-nntp-tokenize line) (list *fn-pcr-article-keyword* token))
                  (fn-arena-p fn-arena) (fn-nntp-number-tokenp token)
                  group (consp article) server (fn-gidx-pinp viewindex)
                  (not (fn-nntp-number-withdrawn-p session viewarchive viewindex token))
                  (fn-nntp-response-okp-of-bytes article (fn-nntp-article-bytes article fn-arena) :article)
                  (fn-nntp-response-okp-of-bytes article (fn-pcr-served-octets server article fn-arena) :article))
             (and (equal (fn-served-result-effects p) (fn-nntp-result-effects r))
                  (equal (fn-post-session-base (fn-peer-session-base
                          (fn-auth-session-base
                           (fn-served-conn-session (fn-served-result-conn p)))))
                         (fn-nntp-result-session r))
                  (equal (fn-served-conn-pinned (fn-served-result-conn p))
                         (fn-served-conn-pinned conn))
                  (equal (fn-served-conn-archive (fn-served-result-conn p))
                         (fn-served-conn-archive conn))
                  (equal (fn-served-conn-index (fn-served-result-conn p))
                         (fn-served-conn-index conn)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-pcr-auth-article-has-the-numbered-reply (as (fn-served-conn-session conn)) (config (fn-served-conn-config conn)) (archive (fn-served-conn-archive conn)) (index (fn-served-conn-pinned-index conn)) (verdicts (fn-served-conn-verdicts conn)) (observation (fn-served-conn-observation conn)) (injection (fn-served-conn-injection conn))) fn-pcr-served-reader-dispatch-is-the-auth-answer-by-definition (:instance fn-pcr-220-is-a-reply-without-an-offer-by-definition (session (fn-post-session-base (fn-peer-session-base (fn-auth-view-session (fn-served-conn-session conn) (fn-served-conn-config conn))))) (article (fn-nntp-find-group-number (fn-nntp-session-group (fn-post-session-base (fn-peer-session-base (fn-auth-view-session (fn-served-conn-session conn) (fn-served-conn-config conn))))) (fn-nntp-decimal-value token) (fn-state-articles (fn-auth-view-archive (fn-served-conn-session conn) (fn-served-conn-config conn) (fn-served-conn-archive conn))))) (number (fn-nntp-decimal-value token)) (group (fn-nntp-session-group (fn-post-session-base (fn-peer-session-base (fn-auth-view-session (fn-served-conn-session conn) (fn-served-conn-config conn)))))) (server (fn-nntp-xref-server (fn-post-reader-env (fn-auth-view-config (fn-served-conn-session conn) (fn-auth-moderation-config (fn-served-conn-session conn) (fn-served-conn-config conn)) (fn-served-conn-archive conn)) (fn-served-conn-observation conn)))))) :in-theory (theory 'minimal-theory))))

(local
 (defun fn-pcr-command-induction (xs rev n)
   (declare (xargs :measure (acl2-count xs) :guard t :verify-guards nil))
   (if (consp xs)
       (fn-pcr-command-induction (cdr xs) (cons (car xs) rev) (+ 1 n))
     (list rev n))))

(local
 (defthm fn-pcr-with-wire-overwrite-by-definition
   (equal (fn-served-conn-with-wire (fn-served-conn-with-wire conn w1) w2)
          (fn-served-conn-with-wire conn w2))
   :hints (("Goal" :in-theory (enable fn-served-conn-with-wire)))))

(local
 (defthm fn-pcr-served-feed-reconstructs
   (equal (fn-served-make-result
           (fn-served-result-conn (fn-served-feed conn xs fn-arena))
           (fn-served-result-effects (fn-served-feed conn xs fn-arena)))
          (fn-served-feed conn xs fn-arena))
   :hints (("Goal" :expand ((fn-served-feed conn xs fn-arena))
            :in-theory (disable fn-served-feed-byte fn-served-feed)))))

(defthm fn-pcr-command-content-feed-is-silent
  (implies (and (fn-wire-line-contentp xs)
                (natp n) (natp line-limit)
                (<= (+ n (len xs)) line-limit)
                (not (fn-served-haltedp conn)))
           (equal (fn-served-feed
                   (fn-served-conn-with-wire conn
                    (fn-wire-make-state :command rev n nil nil 0 line-limit body-limit))
                   xs fn-arena)
                  (fn-served-make-result
                   (fn-served-conn-with-wire conn
                    (fn-wire-make-state :command (fn-ag-rev-onto xs rev)
                                        (+ n (len xs)) nil nil 0 line-limit body-limit))
                   nil)))
  :hints (("Goal" :induct (fn-pcr-command-induction xs rev n)
           :expand ((fn-served-feed
                     (fn-served-conn-with-wire conn
                      (fn-wire-make-state :command rev n nil nil 0 line-limit body-limit))
                     xs fn-arena))
           :in-theory (e/d (fn-served-feed fn-served-feed-byte fn-served-dispatch-events
                            fn-wire-feed-byte fn-wire-take-octet fn-wire-line-contentp
                            fn-served-closed-wirep fn-ag-rev-onto)
                           (fn-served-conn-with-wire fn-served-haltedp fn-served-dispatch fn-wire-close
                            fn-wire-statep fn-wire-octetp fn-wire-after-line
                            fn-wire-make-state fn-wire-make-result fn-served-make-result
                            fn-served-make-conn-live)))))

(local
 (defthm fn-pcr-served-dispatch-reconstructs
   (equal (fn-served-make-result
           (fn-served-result-conn (fn-served-dispatch conn event fn-arena))
           (fn-served-result-effects (fn-served-dispatch conn event fn-arena)))
          (fn-served-dispatch conn event fn-arena))
   :hints (("Goal" :in-theory (e/d (fn-served-dispatch fn-served-dispatch-core)
                                  (fn-auth-step-pinned fn-served-advance-eventp
                                   fn-served-selectedp fn-served-repin fn-post-offeredp
                                   fn-served-make-result fn-served-make-conn-live
                                   fn-post-result-effects fn-post-result-session
                                   fn-post-result-submission fn-wire-begin-article-with-line-limit))))))

(defthm fn-pcr-command-crlf-dispatches-the-held-line-by-definition
  (let* ((clear (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit))
         (p (fn-served-dispatch (fn-served-conn-with-wire conn clear)
                                (list :command (fn-wire-reverse-octets rev)) fn-arena)))
    (implies (and (not (fn-served-haltedp conn))
                  (true-listp (fn-served-result-effects p)))
             (equal (fn-served-feed
                     (fn-served-conn-with-wire conn
                      (fn-wire-make-state :command rev n nil nil 0 line-limit body-limit))
                     '(13 10) fn-arena)
                    p)))
  :hints (("Goal"
           :expand ((:free (c) (fn-served-feed c '(13 10) fn-arena))
                    (:free (c) (fn-served-feed c '(10) fn-arena))
                    (:free (c) (fn-served-feed c nil fn-arena)))
           :in-theory (e/d (fn-served-feed-byte fn-wire-feed-byte fn-wire-after-line
                            fn-served-dispatch-events fn-served-closed-wirep fn-wire-command-event)
                           (fn-served-conn-with-wire fn-served-haltedp fn-served-dispatch
                            fn-wire-reverse-octets fn-wire-close fn-wire-make-state
                            fn-wire-make-result fn-served-make-result fn-served-feed)))))

(local
 (defthm fn-pcr-rev-onto-is-revappend
   (equal (fn-ag-rev-onto xs acc) (revappend xs acc))
   :hints (("Goal" :induct (fn-ag-rev-onto xs acc)
            :in-theory (enable fn-ag-rev-onto revappend)))))

(defthm fn-pcr-command-line-feed-reaches-its-dispatch
  (let* ((clear (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit))
         (c (fn-served-conn-with-wire conn clear))
         (p (fn-served-dispatch c (list :command line) fn-arena)))
    (implies (and (fn-wire-line-contentp line) (natp line-limit)
                  (<= (len line) line-limit)
                  (not (fn-served-haltedp conn))
                  (true-listp (fn-served-result-effects p)))
             (equal (fn-served-feed c (append line '(13 10)) fn-arena) p)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-served-feed-of-append
                            (conn (fn-served-conn-with-wire conn
                                    (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit)))
                            (left line) (right '(13 10)))
                 (:instance fn-pcr-command-content-feed-is-silent
                            (xs line) (rev nil) (n 0))
                 (:instance fn-pcr-command-crlf-dispatches-the-held-line-by-definition
                            (rev (fn-ag-rev-onto line nil)) (n (len line))))
           :in-theory (e/d (fn-pcr-rev-onto-is-revappend)
                           (fn-served-feed fn-served-dispatch fn-served-conn-with-wire
                            fn-served-haltedp fn-wire-line-contentp fn-pcr-command-content-feed-is-silent
                            fn-pcr-command-crlf-dispatches-the-held-line-by-definition
                            fn-wire-make-state fn-served-make-result)))))

(local
 (defthm fn-pcr-counted-accessors-of-make-by-definition
   (and (equal (fn-served-counted-consumed (fn-served-counted-make n r)) n)
        (equal (fn-served-counted-result (fn-served-counted-make n r)) r))
   :hints (("Goal" :in-theory (enable fn-served-counted-consumed
                                     fn-served-counted-result fn-served-counted-make)))))

(defthm fn-pcr-command-line-counted-feed-consumes-the-physical-line
  (implies (and (fn-wire-line-contentp xs) (natp n) (natp line-limit)
                (<= (+ n (len xs)) line-limit)
                (not (fn-served-haltedp conn)))
           (equal (fn-served-counted-consumed
                   (fn-served-feed-counted
                    (fn-served-conn-with-wire conn
                     (fn-wire-make-state :command rev n nil nil 0 line-limit body-limit))
                    (append xs '(13 10)) fn-arena))
                  (+ 2 (len xs))))
  :hints (("Goal" :induct (fn-pcr-command-induction xs rev n)
           :expand ((fn-served-feed-counted
                     (fn-served-conn-with-wire conn
                      (fn-wire-make-state :command rev n nil nil 0 line-limit body-limit))
                     (append xs '(13 10)) fn-arena)
                    (:free (byte tail)
                     (fn-served-feed-counted
                      (fn-served-conn-with-wire conn
                       (fn-wire-make-state :command rev n nil nil 0 line-limit body-limit))
                      (cons byte tail) fn-arena))
                    (:free (c) (fn-served-feed-counted c '(13 10) fn-arena))
                    (:free (c) (fn-served-feed-counted c '(10) fn-arena))
                    (:free (c) (fn-served-feed-counted c nil fn-arena)))
           :in-theory (e/d (fn-served-feed-byte fn-wire-feed-byte fn-wire-after-line
                            fn-wire-take-octet fn-served-dispatch-events
                            fn-wire-line-contentp fn-served-closed-wirep)
                           (fn-served-counted-consumed fn-served-counted-result fn-served-counted-make
                            fn-served-feed-counted fn-served-dispatch fn-served-submission
                            fn-served-conn-with-wire fn-served-haltedp fn-wire-reverse-octets
                            fn-wire-close fn-wire-make-state fn-wire-make-result
                            fn-served-make-result fn-served-make-conn-live)))))

(defthm fn-pcr-command-line-counted-step-consumes-the-physical-line
  (implies (and (fn-served-conn-shapep conn)
                (equal (fn-served-conn-wire conn)
                       (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit))
                (fn-wire-statep (fn-served-conn-wire conn))
                (fn-wire-line-contentp line) (natp line-limit)
                (<= (len line) line-limit)
                (not (fn-served-haltedp conn)))
           (equal (fn-served-counted-consumed
                   (fn-served-step-counted-fast conn (append line '(13 10)) fn-arena))
                  (+ 2 (len line))))
  :hints (("Goal"
           :use ((:instance fn-pcr-command-line-counted-feed-consumes-the-physical-line
                            (xs line) (rev nil) (n 0))
                 (:instance fn-served-step-counted-fast-is-reference
                            (octets (append line '(13 10)))))
           :in-theory (e/d (fn-served-step-counted fn-served-step-counted-core)
                           (fn-served-step-counted-fast fn-served-feed-counted
                            fn-served-conn-with-wire fn-served-counted-consumed
                            fn-served-counted-result fn-served-counted-make
                            fn-wire-statep fn-wire-line-contentp fn-served-haltedp)))))

(defthm fn-pcr-article-dispatch-keeps-the-command-wire-by-definition
  (let ((r (fn-auth-step-pinned (fn-served-conn-session conn)
                                (fn-served-conn-archive conn)
                                (fn-served-conn-pinned-index conn)
                                (fn-served-conn-verdicts conn)
                                (fn-served-conn-config conn)
                                (fn-served-conn-observation conn)
                                (fn-served-conn-injection conn)
                                (list :command line) fn-arena)))
    (implies (and (equal (fn-nntp-tokenize line) (list *fn-pcr-article-keyword* token))
                  (not (fn-post-offeredp (fn-post-result-effects r))))
             (equal (fn-served-conn-wire
                     (fn-served-result-conn (fn-served-dispatch conn (list :command line) fn-arena)))
                    (fn-served-conn-wire conn))))
  :hints (("Goal" :in-theory (e/d (fn-served-dispatch fn-served-dispatch-core
                                  fn-pcr-article-keeps-the-pinned-view-by-definition)
                                 (fn-auth-step-pinned fn-served-advance-eventp
                                  fn-post-offeredp fn-post-result-effects fn-post-result-session
                                  fn-post-result-submission fn-served-make-result
                                  fn-served-make-conn-live fn-wire-begin-article-with-line-limit)))))

(local
 (defthm fn-pcr-finish-read-effects-by-definition
   (equal (car (fn-own-finish-read o conn result)) (fn-served-result-effects result))
   :hints (("Goal" :in-theory (union-theories '(fn-own-finish-read car-cons)
                                             (theory 'minimal-theory))))))

(defthm fn-pcr-configured-reader-counted-answer-by-definition
  (let* ((o (fn-ocfg-owner oc))
         (conn (fn-own-find-conn id (fn-own-conns o)))
         (r (fn-served-step-counted-fast (fn-own-tls-served-conn o conn) octets fn-arena))
         (p (fn-ocfg-read-tls-prefix oc id octets fn-arena)))
    (implies conn
             (and (equal (fn-own-tls-result-consumed p) (fn-served-counted-consumed r))
                  (equal (fn-own-tls-result-effects p)
                         (fn-served-result-effects (fn-served-counted-result r))))))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-read-tls-prefix fn-own-read-tls-prefix
                                  fn-own-tls-make-result fn-own-tls-result-consumed
                                  fn-own-tls-result-effects)
                                 (fn-served-step-counted-fast fn-served-counted-consumed
                                  fn-served-counted-result fn-own-tls-served-conn
                                  fn-own-finish-read fn-ocfg-with-read-owner
                                  fn-own-result-repinned fn-own-find-conn fn-own-conns fn-ocfg-owner)))))

(local
 (defthm fn-pcr-true-list-fix-identity
   (implies (true-listp xs) (equal (true-list-fix xs) xs))
   :hints (("Goal" :induct (true-list-fix xs)
            :in-theory (enable true-list-fix)))))

(defthm fn-pcr-served-step-answers-the-numbered-article
(let* ((as (fn-served-conn-session conn)) (config (fn-served-conn-config conn)) (archive (fn-served-conn-archive conn)) (index (fn-served-conn-pinned-index conn)) (observation (fn-served-conn-observation conn)) (peer (fn-auth-view-session as config)) (viewarchive (fn-auth-view-archive as config archive)) (viewindex (fn-auth-view-index as config archive index)) (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive)) (ps (fn-peer-session-base peer)) (session (fn-post-session-base ps)) (env (fn-post-reader-env viewconfig observation)) (group (fn-nntp-session-group session)) (number (fn-nntp-decimal-value token)) (article (fn-nntp-find-group-number group number (fn-state-articles viewarchive))) (server (fn-nntp-xref-server env)) (r (fn-pcr-220-reply session article number group server fn-arena)) (p (fn-served-step conn (append line (quote (13 10))) fn-arena))) (implies (and (fn-served-conn-shapep conn) (equal (fn-served-conn-wire conn) (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit)) (fn-wire-statep (fn-served-conn-wire conn)) (fn-wire-line-contentp line) (natp line-limit) (<= (len line) line-limit) (not (fn-served-haltedp conn)) (fn-auth-sessionp as) (not (fn-auth-session-handshakingp as)) (not (fn-auth-sasl-waitingp as)) (or (not (fn-auth-config-requiredp (fn-auth-session-config as))) (fn-auth-session-subject as)) (fn-peer-sessionp peer) (null (fn-peer-session-peer peer)) (fn-post-sessionp ps) (not (fn-post-session-awaiting ps)) (fn-nntp-sessionp session) (equal (fn-nntp-session-openp session) t) (fn-nntp-session-projected session) (fn-nntp-command-inputp line) (fn-nntp-command-arguments-at-mostp (list *fn-pcr-article-keyword* token)) (equal (fn-nntp-tokenize line) (list *fn-pcr-article-keyword* token)) (fn-arena-p fn-arena) (fn-nntp-number-tokenp token) group (consp article) server (fn-gidx-pinp viewindex) (not (fn-nntp-number-withdrawn-p session viewarchive viewindex token)) (fn-nntp-response-okp-of-bytes article (fn-nntp-article-bytes article fn-arena) :article) (fn-nntp-response-okp-of-bytes article (fn-pcr-served-octets server article fn-arena) :article)) (and (equal (fn-served-result-effects p) (fn-nntp-result-effects r)) (equal (fn-post-session-base (fn-peer-session-base (fn-auth-session-base (fn-served-conn-session (fn-served-result-conn p))))) (fn-nntp-result-session r)) (equal (fn-served-conn-pinned (fn-served-result-conn p)) (fn-served-conn-pinned conn)) (equal (fn-served-conn-archive (fn-served-result-conn p)) (fn-served-conn-archive conn)) (equal (fn-served-conn-index (fn-served-result-conn p)) (fn-served-conn-index conn)))))
  :rule-classes nil
  :hints (("Goal" :use (
 fn-pcr-served-dispatch-has-the-numbered-reply
 (:instance fn-pcr-command-line-feed-reaches-its-dispatch)
 fn-pcr-article-dispatch-keeps-the-command-wire-by-definition
 (:instance fn-pcr-auth-article-has-the-numbered-reply (as (fn-served-conn-session conn)) (config (fn-served-conn-config conn)) (archive (fn-served-conn-archive conn)) (index (fn-served-conn-pinned-index conn)) (observation (fn-served-conn-observation conn)) (verdicts (fn-served-conn-verdicts conn)) (injection (fn-served-conn-injection conn))) (:instance fn-pcr-220-is-a-reply-without-an-offer-by-definition (session (fn-post-session-base (fn-peer-session-base (fn-auth-view-session (fn-served-conn-session conn) (fn-served-conn-config conn))))) (article (fn-nntp-find-group-number (fn-nntp-session-group (fn-post-session-base (fn-peer-session-base (fn-auth-view-session (fn-served-conn-session conn) (fn-served-conn-config conn))))) (fn-nntp-decimal-value token) (fn-state-articles (fn-auth-view-archive (fn-served-conn-session conn) (fn-served-conn-config conn) (fn-served-conn-archive conn))))) (number (fn-nntp-decimal-value token)) (group (fn-nntp-session-group (fn-post-session-base (fn-peer-session-base (fn-auth-view-session (fn-served-conn-session conn) (fn-served-conn-config conn)))))) (server (fn-nntp-xref-server (fn-post-reader-env (fn-auth-view-config (fn-served-conn-session conn) (fn-auth-moderation-config (fn-served-conn-session conn) (fn-served-conn-config conn)) (fn-served-conn-archive conn)) (fn-served-conn-observation conn))))))
 :in-theory (union-theories
 '(fn-served-step fn-served-closed-wirep
   fn-served-conn-with-wire-of-own-wire fn-served-conn-fields-of-with-wire
   fn-served-result-effects-of-fn-served-make-result fn-served-result-conn-of-fn-served-make-result
   fn-wire-state-mode-of-fn-wire-make-state fn-lgt-append-nil fn-pcr-true-list-fix-identity
   car-cons cdr-cons)
 (theory 'minimal-theory)))))

(defthm fn-pcr-mca-is-the-counted-configured-read-by-definition
  (implies (and (equal (car (fn-mcr-resize
                           credits (fn-mca-conn-key id)
                           (fn-mca-need (fn-own-tls-result-owner
                                        (fn-oas-read-span oc views id i end cache s slots
                                                          fn-octets fn-arena fn-cat))
                                        id reserve))) :ok)
                (not (fn-oas-over-p oc (fn-own-tls-result-owner
                                      (fn-otm-read-span oc views id i end cache s
                                                        fn-octets fn-arena fn-cat)) id slots))
                (not (eq (fn-otm-admit-post s) :shed)) (not (consp views))
                (fn-gacc-okp cache) (fn-ocl-relation oc)
                (fn-scar-view-indexedp (fn-ocfg-owner oc))
                (fn-scr-owner-catalogp (fn-ocfg-owner oc) id fn-arena fn-cat)
                (fn-scol-okp fn-arena fn-cat) (natp i) (natp end))
           (equal (car (fn-mca-read-span credits oc views id i end cache s slots reserve
                                         fn-octets fn-arena fn-cat))
                  (fn-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets) fn-arena)))
  :hints (("Goal"
           :use (fn-mca-read-span-within-the-credit-unfolds
                 fn-oas-read-span-when-held-unfolds fn-otm-read-span-when-admitted-unfolds
                 fn-orr-read-span-without-a-capture-is-the-span-read-by-definition
                 fn-scr-ocfg-read-span-is-reference-under-ocl-relation)
           :in-theory (theory 'minimal-theory))))

(local
 (defthm fn-pcr-take-full-list
   (equal (take (len xs) xs) (true-list-fix xs))
   :hints (("Goal" :induct (len xs)
            :in-theory (enable take true-list-fix)))))

(local
 (defthm fn-pcr-take-physical-line
   (equal (take (+ 2 (len line)) (append line '(13 10)))
          (append line '(13 10)))
   :hints (("Goal" :use ((:instance fn-pcr-take-full-list
                                    (xs (append line '(13 10)))))
            :in-theory (e/d (len binary-append true-list-fix)
                            (fn-pcr-take-full-list))))))

(local
 (defthm fn-pcr-tls-served-wire-by-definition
   (equal (fn-served-conn-wire (fn-own-tls-served-conn o conn))
          (fn-own-conn-wire conn))
   :hints (("Goal" :in-theory (enable fn-own-tls-served-conn fn-own-served-conn)))))

(defthm fn-pcr-host-called-read-answers-the-numbered-article
(let* ((o (fn-ocfg-owner oc)) (conn (fn-own-find-conn id (fn-own-conns o))) (sc (fn-own-tls-served-conn o conn)) (as (fn-served-conn-session sc)) (config (fn-served-conn-config sc)) (archive (fn-served-conn-archive sc)) (index (fn-served-conn-pinned-index sc)) (observation (fn-served-conn-observation sc)) (peer (fn-auth-view-session as config)) (viewarchive (fn-auth-view-archive as config archive)) (viewindex (fn-auth-view-index as config archive index)) (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive)) (ps (fn-peer-session-base peer)) (session (fn-post-session-base ps)) (env (fn-post-reader-env viewconfig observation)) (group (fn-nntp-session-group session)) (number (fn-nntp-decimal-value token)) (article (fn-nntp-find-group-number group number (fn-state-articles viewarchive))) (server (fn-nntp-xref-server env)) (r (fn-pcr-220-reply session article number group server fn-arena)) (p (car (fn-mca-read-span credits oc views id i end cache s slots reserve fn-octets fn-arena fn-cat)))) (implies (and (equal (car (fn-mcr-resize credits (fn-mca-conn-key id) (fn-mca-need (fn-own-tls-result-owner (fn-oas-read-span oc views id i end cache s slots fn-octets fn-arena fn-cat)) id reserve))) :ok) (not (fn-oas-over-p oc (fn-own-tls-result-owner (fn-otm-read-span oc views id i end cache s fn-octets fn-arena fn-cat)) id slots)) (not (eq (fn-otm-admit-post s) :shed)) (not (consp views)) (fn-gacc-okp cache) (fn-ocl-relation oc) (fn-scar-view-indexedp (fn-ocfg-owner oc)) (fn-scr-owner-catalogp (fn-ocfg-owner oc) id fn-arena fn-cat) (fn-scol-okp fn-arena fn-cat) (natp i) (natp end) conn completed (equal (fn-oct-slice-list i end fn-octets) (append line (quote (13 10)))) (fn-served-conn-shapep sc) (equal (fn-served-conn-wire sc) (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit)) (fn-wire-statep (fn-served-conn-wire sc)) (fn-wire-line-contentp line) (natp line-limit) (<= (len line) line-limit) (not (fn-served-haltedp sc)) (fn-auth-sessionp as) (not (fn-auth-session-handshakingp as)) (not (fn-auth-sasl-waitingp as)) (or (not (fn-auth-config-requiredp (fn-auth-session-config as))) (fn-auth-session-subject as)) (fn-peer-sessionp peer) (null (fn-peer-session-peer peer)) (fn-post-sessionp ps) (not (fn-post-session-awaiting ps)) (fn-nntp-sessionp session) (equal (fn-nntp-session-openp session) t) (fn-nntp-session-projected session) (fn-nntp-command-inputp line) (fn-nntp-command-arguments-at-mostp (list *fn-pcr-article-keyword* token)) (equal (fn-nntp-tokenize line) (list *fn-pcr-article-keyword* token)) (fn-arena-p fn-arena) (fn-nntp-number-tokenp token) group (consp article) server (fn-gidx-pinp viewindex) (not (fn-nntp-number-withdrawn-p session viewarchive viewindex token)) (fn-nntp-response-okp-of-bytes article (fn-nntp-article-bytes article fn-arena) :article) (fn-nntp-response-okp-of-bytes article (fn-pcr-served-octets server article fn-arena) :article)) (and (equal (fn-otb-dependency-step since now limit completed) :serve) (equal (fn-own-tls-result-consumed p) (+ 2 (len line))) (equal (fn-own-tls-result-effects p) (fn-nntp-result-effects r)) (equal (fn-own-tls-result-owner p) (cdr (fn-ocfg-read oc id (append line (quote (13 10))) fn-arena))))))
  :rule-classes nil
  :hints (("Goal" :use (
 fn-pcr-mca-is-the-counted-configured-read-by-definition
 (:instance fn-pcr-configured-reader-counted-answer-by-definition (octets (append line '(13 10))))
 (:instance fn-pcr-command-line-counted-step-consumes-the-physical-line (conn (fn-own-tls-served-conn (fn-ocfg-owner oc) (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))))
 (:instance fn-served-step-counted-fast-is-reference (conn (fn-own-tls-served-conn (fn-ocfg-owner oc) (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))) (octets (append line '(13 10))))
 (:instance fn-served-step-counted-result-is-step-of-consumed-prefix (conn (fn-own-tls-served-conn (fn-ocfg-owner oc) (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))) (octets (append line '(13 10))))
 (:instance fn-pcr-served-step-answers-the-numbered-article (conn (fn-own-tls-served-conn (fn-ocfg-owner oc) (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))))
 (:instance fn-pcr-served-read-is-the-reference-read)
 fn-otb-a-late-page-is-unavailable-never-absent)
 :in-theory (union-theories
 '(fn-pcr-take-physical-line fn-pcr-tls-served-wire-by-definition)
 (theory 'minimal-theory)))))

(local
 (defthm fn-pcr-valid-peer-has-valid-post
   (implies (fn-peer-sessionp peer) (fn-post-sessionp (fn-peer-session-base peer)))
   :hints (("Goal" :in-theory (e/d (fn-peer-sessionp) (fn-post-sessionp))))))
(local
 (defthm fn-pcr-valid-post-has-valid-reader
   (implies (fn-post-sessionp ps) (fn-nntp-sessionp (fn-post-session-base ps)))
   :hints (("Goal" :in-theory (e/d (fn-post-sessionp) (fn-nntp-sessionp))))))

(local
 (defthm fn-pcr-auth-view-is-a-valid-reader-stack
   (implies (fn-auth-sessionp as)
            (let* ((peer (fn-auth-view-session as config))
                   (ps (fn-peer-session-base peer)))
              (and (fn-peer-sessionp peer)
                   (fn-post-sessionp ps)
                   (fn-nntp-sessionp (fn-post-session-base ps)))))
   :hints (("Goal" :use fn-auth-view-session-is-a-session
            :in-theory (disable fn-auth-sessionp fn-auth-view-session fn-peer-sessionp fn-post-sessionp
                               fn-peer-session-shapep fn-post-session-shapep fn-nntp-sessionp)))))

(local
 (defthm fn-pcr-tls-served-conn-has-shape
   (fn-served-conn-shapep (fn-own-tls-served-conn o conn))
   :hints (("Goal" :in-theory (enable fn-own-tls-served-conn fn-own-served-conn
                                     fn-served-make-conn-live fn-served-conn-shapep)))))

(local
 (defthm fn-pcr-command-wire-limit-is-natural
   (implies (fn-wire-statep (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit))
            (natp line-limit))
   :hints (("Goal" :in-theory (enable fn-wire-statep)))))

(local
 (defthm fn-pcr-open-nonhandshaking-view-is-not-halted
   (implies (and (not (fn-auth-session-handshakingp (fn-served-conn-session conn)))
                 (equal (fn-nntp-session-openp
                         (fn-post-session-base (fn-peer-session-base
                          (fn-auth-view-session (fn-served-conn-session conn)
                                                (fn-served-conn-config conn))))) t))
            (not (fn-served-haltedp conn)))
   :hints (("Goal" :use (:instance fn-auth-view-session-keeps-role
                                  (as (fn-served-conn-session conn))
                                  (config (fn-served-conn-config conn)))
            :in-theory (e/d (fn-served-haltedp fn-served-tls-handshakingp fn-served-quitp)
                            (fn-auth-view-session fn-auth-session-handshakingp
                             fn-nntp-session-openp))))))

(local
 (defthm fn-pcr-command-syntax-is-plain-line
   (implies (fn-nntp-command-linep line) (fn-wire-line-contentp line))
   :hints (("Goal" :induct (fn-nntp-command-linep line)
            :in-theory (enable fn-nntp-command-linep fn-nntp-command-bytep
                               fn-nntp-space-or-tabp fn-wire-line-contentp
                               fn-wire-octetp fn-bch-plain-octetsp fn-bch-octetp)))))

(local
 (defthm fn-pcr-command-input-is-plain-line
   (implies (fn-nntp-command-inputp line) (fn-wire-line-contentp line))
   :hints (("Goal" :use fn-pcr-command-syntax-is-plain-line
            :in-theory (union-theories '(fn-nntp-command-inputp) (theory 'minimal-theory))))))

(defthm
  fn-pcr-host-called-read-produces-the-numbered-article
  (let*
    ((o (fn-ocfg-owner oc))
      (conn (fn-own-find-conn id (fn-own-conns o)))
      (sc (fn-own-tls-served-conn o conn))
      (as (fn-served-conn-session sc))
      (config (fn-served-conn-config sc))
      (archive (fn-served-conn-archive sc))
      (index (fn-served-conn-pinned-index sc))
      (observation (fn-served-conn-observation sc))
      (peer (fn-auth-view-session as config))
      (viewarchive (fn-auth-view-archive as config archive))
      (viewindex (fn-auth-view-index as config archive index))
      (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
      (ps (fn-peer-session-base peer))
      (session (fn-post-session-base ps))
      (env (fn-post-reader-env viewconfig observation))
      (group (fn-nntp-session-group session))
      (number (fn-nntp-decimal-value token))
      (article (fn-nntp-find-group-number group number (fn-state-articles viewarchive)))
      (server (fn-nntp-xref-server env))
      (r (fn-pcr-220-reply session article number group server fn-arena))
      (p
        (car
          (fn-mca-read-span
            credits
            oc
            views
            id
            i
            end
            cache
            s
            slots
            reserve
            fn-octets
            fn-arena
            fn-cat))))
    (implies
      (and
        (equal
          (car
            (fn-mcr-resize
              credits
              (fn-mca-conn-key id)
              (fn-mca-need
                (fn-own-tls-result-owner
                  (fn-oas-read-span oc views id i end cache s slots fn-octets fn-arena fn-cat))
                id
                reserve)))
          :ok)
        (not
          (fn-oas-over-p
            oc
            (fn-own-tls-result-owner
              (fn-otm-read-span oc views id i end cache s fn-octets fn-arena fn-cat))
            id
            slots))
        (not (eq (fn-otm-admit-post s) :shed))
        (not (consp views))
        (fn-gacc-okp cache)
        (fn-ocl-relation oc)
        (fn-scar-view-indexedp (fn-ocfg-owner oc))
        (fn-scr-owner-catalogp (fn-ocfg-owner oc) id fn-arena fn-cat)
        (fn-scol-okp fn-arena fn-cat)
        (natp i)
        (natp end)
        conn
        completed
        (equal (fn-oct-slice-list i end fn-octets) (append line (quote (13 10))))
        (equal
          (fn-served-conn-wire sc)
          (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit))
        (fn-wire-statep (fn-served-conn-wire sc))
        (<= (len line) line-limit)
        (fn-auth-sessionp as)
        (not (fn-auth-session-handshakingp as))
        (not (fn-auth-sasl-waitingp as))
        (or
          (not (fn-auth-config-requiredp (fn-auth-session-config as)))
          (fn-auth-session-subject as))
        (null (fn-peer-session-peer peer))
        (not (fn-post-session-awaiting ps))
        (equal (fn-nntp-session-openp session) t)
        (fn-nntp-session-projected session)
        (fn-nntp-command-inputp line)
        (fn-nntp-command-arguments-at-mostp (list *fn-pcr-article-keyword* token))
        (equal (fn-nntp-tokenize line) (list *fn-pcr-article-keyword* token))
        (fn-nntp-number-tokenp token)
        group
        (consp article)
        server
        (fn-gidx-pinp viewindex)
        (not (fn-nntp-number-withdrawn-p session viewarchive viewindex token))
        (fn-nntp-response-okp-of-bytes article (fn-nntp-article-bytes article fn-arena) :article)
        (fn-nntp-response-okp-of-bytes
          article
          (fn-pcr-served-octets server article fn-arena)
          :article))
      (and
        (equal (fn-otb-dependency-step since now limit completed) :serve)
        (equal (fn-own-tls-result-consumed p) (+ 2 (len line)))
        (equal (fn-own-tls-result-effects p) (fn-nntp-result-effects r))
        (equal
          (fn-own-tls-result-owner p)
          (cdr (fn-ocfg-read oc id (append line (quote (13 10))) fn-arena))))))
  :rule-classes
  nil
  :hints
  (("Goal"
     :use
     (fn-pcr-host-called-read-answers-the-numbered-article
       (:instance
         fn-pcr-auth-view-is-a-valid-reader-stack
         (as
           (fn-served-conn-session
             (fn-own-tls-served-conn
               (fn-ocfg-owner oc)
               (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))))
         (config
           (fn-served-conn-config
             (fn-own-tls-served-conn
               (fn-ocfg-owner oc)
               (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))))
       (:instance
         fn-pcr-tls-served-conn-has-shape
         (o (fn-ocfg-owner oc))
         (conn (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
       fn-pcr-command-wire-limit-is-natural
       (:instance
         fn-pcr-open-nonhandshaking-view-is-not-halted
         (conn
           (fn-own-tls-served-conn
             (fn-ocfg-owner oc)
             (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))))
       fn-pcr-command-input-is-plain-line
       fn-scol-okp-arena-p)
     :in-theory
     (theory (quote minimal-theory)))))
