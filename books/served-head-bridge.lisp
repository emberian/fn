; PKT-772: HEAD effect composition over the host-reached served step.
; PRF-1114: concrete command-wire refinement, with complete literal teeth.
(in-package "ACL2")
(include-book "served")
(include-book "nntp-pinned-msgid")
(include-book "nntp-auth-fold")
(local
 (defthm fn-shd-post-delegates-a-read-without-offer-by-definition
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
                                  fn-post-session-base))))))
(local
 (defthm fn-shd-peer-reader-delegates-to-post-by-definition
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
                                  fn-post-make-result fn-peer-with-base fn-peer-session-base))))))
(local
 (defun fn-shd-command-induction (xs rev n)
   (declare (xargs :measure (acl2-count xs) :guard (acl2-numberp n)))
   (if (consp xs)
       (fn-shd-command-induction (cdr xs) (cons (car xs) rev) (+ 1 n))
     (list rev n))))
(local (verify-guards fn-shd-command-induction))
(local
 (defthm fn-shd-with-wire-overwrite-by-definition
   (equal (fn-served-conn-with-wire (fn-served-conn-with-wire conn w1) w2)
          (fn-served-conn-with-wire conn w2))
   :hints (("Goal" :in-theory (enable fn-served-conn-with-wire)))))
(local
 (defthm fn-shd-served-feed-reconstructs
   (equal (fn-served-make-result
           (fn-served-result-conn (fn-served-feed conn xs fn-arena))
           (fn-served-result-effects (fn-served-feed conn xs fn-arena)))
          (fn-served-feed conn xs fn-arena))
   :hints (("Goal" :expand ((fn-served-feed conn xs fn-arena))
            :in-theory (disable fn-served-feed-byte fn-served-feed)))))
(local
 (defthm fn-shd-command-content-feed-is-silent
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
  :hints (("Goal" :induct (fn-shd-command-induction xs rev n)
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
                            fn-served-make-conn-live))))))
(local
 (defthm fn-shd-served-dispatch-reconstructs
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
(local
 (defthm fn-shd-command-crlf-dispatches-the-held-line-by-definition
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
                            fn-wire-make-result fn-served-make-result fn-served-feed))))))
(local
 (defthm fn-shd-rev-onto-is-revappend
   (equal (fn-ag-rev-onto xs acc) (revappend xs acc))
   :hints (("Goal" :induct (fn-ag-rev-onto xs acc)
            :in-theory (enable fn-ag-rev-onto revappend)))))
(local
 (defthm fn-shd-command-line-feed-reaches-its-dispatch
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
                 (:instance fn-shd-command-content-feed-is-silent
                            (xs line) (rev nil) (n 0))
                 (:instance fn-shd-command-crlf-dispatches-the-held-line-by-definition
                            (rev (fn-ag-rev-onto line nil)) (n (len line))))
           :in-theory (e/d (fn-shd-rev-onto-is-revappend)
                           (fn-served-feed fn-served-dispatch fn-served-conn-with-wire
                            fn-served-haltedp fn-wire-line-contentp fn-shd-command-content-feed-is-silent
                            fn-shd-command-crlf-dispatches-the-held-line-by-definition
                            fn-wire-make-state fn-served-make-result))))))

(defconst *fn-shd-head-keyword* '(72 69 65 68))

(local
 (defthm fn-shd-command-head-reaches-the-pinned-archive-by-definition
  (implies (fn-nntp-session-projected session)
           (equal (fn-nntp-command-pinned session archive index verdicts env
                                          (list *fn-shd-head-keyword* token) fn-arena)
                  (fn-nntp-archive-command-pinned session archive index verdicts env
                                                 *fn-shd-head-keyword* (list token) fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-command-pinned fn-nntp-archive-keywordp
                                  fn-nntp-keywordp fn-nntp-keyword-tokenp)
                                 (fn-nntp-archive-command-pinned fn-nntp-session-projected
                                  fn-nntp-session-command fn-nntp-single))))))

(local
 (defthm fn-shd-command-line-reaches-the-reader-dispatch-by-definition
  (implies (and (fn-nntp-sessionp session)
                (equal (fn-nntp-session-openp session) t)
                (fn-nntp-command-inputp line)
                (fn-nntp-command-arguments-at-mostp (list *fn-shd-head-keyword* token))
                (equal (fn-nntp-tokenize line) (list *fn-shd-head-keyword* token)))
           (equal (fn-nntp-step-pinned session archive index verdicts env
                                       (list :command line) fn-arena)
                  (fn-nntp-command-pinned session archive index verdicts env
                                          (list *fn-shd-head-keyword* token) fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-step-pinned)
                                 (fn-nntp-sessionp fn-nntp-session-openp fn-nntp-command-inputp
                                  fn-nntp-tokenize fn-nntp-command-pinned fn-nntp-single
                                  fn-nntp-command-arguments-at-mostp))))))

(local
 (defthm fn-shd-auth-head-is-not-intercepted-by-definition
  (implies (or (not (fn-auth-config-requiredp (fn-auth-session-config as)))
               (fn-auth-session-subject as))
           (not (fn-auth-command as config *fn-shd-head-keyword* (list token))))
  :hints (("Goal" :in-theory (e/d (fn-auth-command fn-auth-gatedp fn-auth-compressed-refusedp
                                  fn-nntp-keywordp)
                                 (fn-auth-config-requiredp fn-auth-session-config
                                  fn-auth-session-subject fn-auth-postingp
                                  fn-auth-starttls fn-auth-authinfo fn-auth-compress
                                  fn-auth-xredeem fn-zc-activep))))))

(local
 (defthm fn-shd-auth-reader-delegates-an-authorized-head-by-definition (implies (and (fn-auth-sessionp as) (not (fn-auth-session-handshakingp as)) (not (fn-auth-sasl-waitingp as)) (or (not (fn-auth-config-requiredp (fn-auth-session-config as))) (fn-auth-session-subject as)) (fn-nntp-command-inputp line) (equal (fn-nntp-tokenize line) (list *fn-shd-head-keyword* token))) (let ((r (fn-peer-step-pinned (fn-auth-view-session as config) (fn-auth-view-archive as config archive) (fn-auth-view-index as config archive index) verdicts (fn-auth-view-config as (fn-auth-moderation-config as config) archive) observation injection (list :command line) fn-arena)) (p (fn-auth-step-pinned as archive index verdicts config observation injection (list :command line) fn-arena))) (and (equal (fn-post-result-effects p) (fn-post-result-effects r)) (equal (fn-post-result-submission p) (fn-post-result-submission r)) (equal (fn-auth-session-base (fn-post-result-session p)) (fn-post-result-session r))))) :hints (("Goal" :in-theory (e/d (fn-auth-step-pinned fn-auth-delegate-pinned fn-auth-tls-eventp fn-auth-redeem-eventp fn-auth-context-eventp fn-nntp-keyword-tokenp fn-shd-auth-head-is-not-intercepted-by-definition fn-auth-with-base) (fn-auth-sessionp fn-auth-session-handshakingp fn-auth-sasl-waitingp fn-post-result-effects fn-post-result-session fn-post-result-submission fn-post-make-result fn-auth-session-base fn-auth-command fn-auth-view-session fn-auth-view-archive fn-auth-view-index fn-auth-view-config fn-auth-moderation-config fn-peer-step-pinned fn-nntp-command-inputp fn-nntp-tokenize fn-nntp-command-arguments-at-mostp))))))

(local
 (defthm fn-shd-head-keeps-the-pinned-view-by-definition
  (implies (equal (fn-nntp-tokenize line) (list *fn-shd-head-keyword* token))
           (not (fn-served-advance-eventp (list :command line))))
  :hints (("Goal" :in-theory (e/d (fn-served-advance-eventp fn-nntp-keywordp)
                                 (fn-nntp-tokenize fn-nntp-command-inputp))))))

(local
 (defthm fn-shd-served-reader-dispatch-is-the-auth-answer-by-definition
  (let ((r (fn-auth-step-pinned (fn-served-conn-session conn)
                                (fn-served-conn-archive conn)
                                (fn-served-conn-pinned-index conn)
                                (fn-served-conn-verdicts conn)
                                (fn-served-conn-config conn)
                                (fn-served-conn-observation conn)
                                (fn-served-conn-injection conn)
                                (list :command line) fn-arena))
        (p (fn-served-dispatch conn (list :command line) fn-arena)))
    (implies (and (equal (fn-nntp-tokenize line) (list *fn-shd-head-keyword* token))
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
                                  fn-shd-head-keeps-the-pinned-view-by-definition)
                                 (fn-auth-step-pinned fn-post-result-submission
                                  fn-post-result-session fn-post-result-effects
                                  fn-post-offeredp fn-served-advance-eventp
                                  fn-served-make-result fn-served-make-conn-live
                                  fn-served-conn-session fn-served-conn-pinned
                                  fn-served-conn-archive fn-served-conn-index
                                  fn-served-result-conn fn-served-result-effects
                                  fn-wire-begin-article-with-line-limit))))))

(local
 (defthm fn-shd-retrieval-has-no-offer
   (not (fn-post-offeredp
         (fn-nntp-result-effects
          (fn-rcompat-retrieval session archive trie kind args server fn-arena))))
   :hints (("Goal" :in-theory
            (e/d (fn-rcompat-retrieval fn-rcompat-article-reply
                  fn-nntp-article-response fn-post-offeredp fn-nntp-reply-effect)
                 (fn-nntp-single fn-nntp-multi fn-nntp-stuff-lines
                  fn-nntp-crlf fn-rcompat-served-article))))))

(local
 (defthm fn-shd-retrieval-effects-true-listp
   (true-listp
    (fn-nntp-result-effects
     (fn-rcompat-retrieval session archive trie kind args server fn-arena)))
   :hints (("Goal" :in-theory
            (e/d (fn-rcompat-retrieval fn-rcompat-article-reply
                  fn-nntp-article-response fn-nntp-single fn-nntp-multi
                  fn-nntp-make-result fn-nntp-result-effects)
                 (fn-nntp-stuff-lines fn-nntp-crlf fn-rcompat-served-article))))))

(local
 (defthm fn-shd-head-kind
  (and (fn-nntp-keywordp *fn-shd-head-keyword* "HEAD")
       (not (fn-nntp-keywordp *fn-shd-head-keyword* "ARTICLE"))
       (equal (fn-rcompat-retrieval-kind *fn-shd-head-keyword*) :head))
  :hints (("Goal" :in-theory (enable fn-rcompat-retrieval-kind fn-nntp-keywordp)))))

(local
 (defthm fn-shd-overlong-head-token-is-neither-number-nor-message-id
  (implies (not (fn-nntp-command-arguments-at-mostp (list *fn-shd-head-keyword* token)))
           (and (not (fn-nntp-number-tokenp token))
                (not (fn-nntp-message-id-tokenp token))))
  :hints (("Goal" :in-theory
   (e/d (fn-nntp-command-arguments-at-mostp fn-nntp-argument-tokens
         fn-nntp-each-token-at-mostp fn-nntp-number-tokenp fn-nntp-message-id-tokenp)
        (fn-nntp-decimal-tokenp fn-nntp-decimal-value fn-nntp-printable-tokenp
         fn-nntp-message-id-tailp))))))

(local
 (defthm fn-shd-overlong-head-retrieval-is-syntax
  (implies (not (fn-nntp-command-arguments-at-mostp (list *fn-shd-head-keyword* token)))
   (equal (fn-rcompat-retrieval session archive trie :head (list token) server fn-arena)
          (fn-nntp-single session (fn-proto-text * :syntax))))
  :hints (("Goal" :use fn-shd-overlong-head-token-is-neither-number-nor-message-id
   :in-theory (e/d (fn-rcompat-retrieval)
    (fn-nntp-number-tokenp fn-nntp-message-id-tokenp fn-nntp-single
     fn-nntp-command-arguments-at-mostp))))))

(local
 (defthm fn-shd-overlong-reader-step-is-retrieval
  (implies (and (fn-nntp-sessionp session)
                (equal (fn-nntp-session-openp session) t)
                (fn-nntp-command-inputp line)
                (equal (fn-nntp-tokenize line) (list *fn-shd-head-keyword* token))
                (not (fn-nntp-command-arguments-at-mostp (list *fn-shd-head-keyword* token))))
   (equal (fn-nntp-step-pinned session archive index verdicts env (list :command line) fn-arena)
          (fn-rcompat-retrieval session archive (fn-gidx-pin-trie index) :head
                                (list token) (fn-nntp-xref-server env) fn-arena)))
  :hints (("Goal" :use (:instance fn-shd-overlong-head-retrieval-is-syntax
    (trie (fn-gidx-pin-trie index)) (server (fn-nntp-xref-server env)))
   :in-theory (e/d (fn-nntp-step-pinned)
    (fn-nntp-sessionp fn-nntp-session-openp fn-nntp-command-inputp
     fn-nntp-tokenize fn-nntp-command-arguments-at-mostp fn-nntp-single
     fn-rcompat-retrieval fn-nntp-command-pinned))))))

(local
 (defthm fn-shd-reader-step-is-served-retrieval (implies (and (fn-nntp-sessionp session) (equal (fn-nntp-session-openp session) t) (fn-nntp-session-projected session) (fn-nntp-command-inputp line) (equal (fn-nntp-tokenize line) (list *fn-shd-head-keyword* token)) (fn-nntp-xref-server env) (fn-gidx-pinp index) (not (fn-nntp-number-withdrawn-p session archive index token)) (not (and (fn-nntp-message-id-tokenp token) (fn-nntp-msgid-withdrawn-p index token)))) (equal (fn-nntp-step-pinned session archive index verdicts env (list :command line) fn-arena) (fn-rcompat-retrieval session archive (fn-gidx-pin-trie index) :head (list token) (fn-nntp-xref-server env) fn-arena))) :rule-classes nil :hints (("Goal" :use (fn-shd-head-kind fn-shd-command-line-reaches-the-reader-dispatch-by-definition fn-shd-command-head-reaches-the-pinned-archive-by-definition (:instance fn-nntp-archive-command-pinned-article-head-is-served (keyword *fn-shd-head-keyword*) (args (list token))) fn-shd-overlong-reader-step-is-retrieval) :in-theory (union-theories (quote (car-cons cdr-cons)) (theory (quote minimal-theory))) :cases ((fn-nntp-command-arguments-at-mostp (list *fn-shd-head-keyword* token)))))))


(local
 (defthm fn-shd-post-is-served-retrieval (let* ((session (fn-post-session-base ps)) (env (fn-post-reader-env config observation)) (server (fn-nntp-xref-server env)) (r (fn-rcompat-retrieval session archive (fn-gidx-pin-trie index) :head (list token) server fn-arena)) (p (fn-nntp-post-step-pinned ps archive index verdicts config observation injection (list :command line) fn-arena))) (implies (and (fn-post-sessionp ps) (not (fn-post-session-awaiting ps)) (fn-nntp-sessionp session) (equal (fn-nntp-session-openp session) t) (fn-nntp-session-projected session) (fn-nntp-command-inputp line) (equal (fn-nntp-tokenize line) (list *fn-shd-head-keyword* token)) server (fn-gidx-pinp index) (not (fn-nntp-number-withdrawn-p session archive index token)) (not (and (fn-nntp-message-id-tokenp token) (fn-nntp-msgid-withdrawn-p index token)))) (and (equal (fn-post-result-effects p) (fn-nntp-result-effects r)) (null (fn-post-result-submission p)) (equal (fn-post-session-base (fn-post-result-session p)) (fn-nntp-result-session r))))) :rule-classes nil :hints (("Goal" :use ((:instance fn-shd-reader-step-is-served-retrieval (session (fn-post-session-base ps)) (env (fn-post-reader-env config observation))) (:instance fn-shd-post-delegates-a-read-without-offer-by-definition (event (list :command line))) (:instance fn-shd-retrieval-has-no-offer (session (fn-post-session-base ps)) (trie (fn-gidx-pin-trie index)) (kind :head) (args (list token)) (server (fn-nntp-xref-server (fn-post-reader-env config observation))))) :in-theory (theory (quote minimal-theory))))))


(local
 (defthm fn-shd-peer-is-served-retrieval (let* ((ps (fn-peer-session-base peer)) (session (fn-post-session-base ps)) (env (fn-post-reader-env config observation)) (server (fn-nntp-xref-server env)) (r (fn-rcompat-retrieval session archive (fn-gidx-pin-trie index) :head (list token) server fn-arena)) (p (fn-peer-step-pinned peer archive index verdicts config observation injection (list :command line) fn-arena))) (implies (and (fn-peer-sessionp peer) (null (fn-peer-session-peer peer)) (fn-post-sessionp ps) (not (fn-post-session-awaiting ps)) (fn-nntp-sessionp session) (equal (fn-nntp-session-openp session) t) (fn-nntp-session-projected session) (fn-nntp-command-inputp line) (equal (fn-nntp-tokenize line) (list *fn-shd-head-keyword* token)) server (fn-gidx-pinp index) (not (fn-nntp-number-withdrawn-p session archive index token)) (not (and (fn-nntp-message-id-tokenp token) (fn-nntp-msgid-withdrawn-p index token)))) (and (equal (fn-post-result-effects p) (fn-nntp-result-effects r)) (null (fn-post-result-submission p)) (equal (fn-post-session-base (fn-peer-session-base (fn-post-result-session p))) (fn-nntp-result-session r))))) :rule-classes nil :hints (("Goal" :use ((:instance fn-shd-post-is-served-retrieval (ps (fn-peer-session-base peer))) (:instance fn-shd-peer-reader-delegates-to-post-by-definition (ps peer) (event (list :command line)))) :in-theory (theory (quote minimal-theory))))))


(local
 (defthm fn-shd-auth-is-served-retrieval (let* ((peer (fn-auth-view-session as config)) (viewarchive (fn-auth-view-archive as config archive)) (viewindex (fn-auth-view-index as config archive index)) (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive)) (ps (fn-peer-session-base peer)) (session (fn-post-session-base ps)) (env (fn-post-reader-env viewconfig observation)) (server (fn-nntp-xref-server env)) (r (fn-rcompat-retrieval session viewarchive (fn-gidx-pin-trie viewindex) :head (list token) server fn-arena)) (p (fn-auth-step-pinned as archive index verdicts config observation injection (list :command line) fn-arena))) (implies (and (fn-auth-sessionp as) (not (fn-auth-session-handshakingp as)) (not (fn-auth-sasl-waitingp as)) (or (not (fn-auth-config-requiredp (fn-auth-session-config as))) (fn-auth-session-subject as)) (fn-peer-sessionp peer) (null (fn-peer-session-peer peer)) (fn-post-sessionp ps) (not (fn-post-session-awaiting ps)) (fn-nntp-sessionp session) (equal (fn-nntp-session-openp session) t) (fn-nntp-session-projected session) (fn-nntp-command-inputp line) (equal (fn-nntp-tokenize line) (list *fn-shd-head-keyword* token)) server (fn-gidx-pinp viewindex) (not (fn-nntp-number-withdrawn-p session viewarchive viewindex token)) (not (and (fn-nntp-message-id-tokenp token) (fn-nntp-msgid-withdrawn-p viewindex token)))) (and (equal (fn-post-result-effects p) (fn-nntp-result-effects r)) (null (fn-post-result-submission p)) (equal (fn-post-session-base (fn-peer-session-base (fn-auth-session-base (fn-post-result-session p)))) (fn-nntp-result-session r))))) :rule-classes nil :hints (("Goal" :use ((:instance fn-shd-peer-is-served-retrieval (peer (fn-auth-view-session as config)) (archive (fn-auth-view-archive as config archive)) (index (fn-auth-view-index as config archive index)) (config (fn-auth-view-config as (fn-auth-moderation-config as config) archive))) fn-shd-auth-reader-delegates-an-authorized-head-by-definition) :in-theory (theory (quote minimal-theory))))))


(local
 (defthm fn-shd-dispatch-is-served-retrieval (let* ((as (fn-served-conn-session conn)) (config (fn-served-conn-config conn)) (archive (fn-served-conn-archive conn)) (index (fn-served-conn-pinned-index conn)) (observation (fn-served-conn-observation conn)) (peer (fn-auth-view-session as config)) (viewarchive (fn-auth-view-archive as config archive)) (viewindex (fn-auth-view-index as config archive index)) (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive)) (ps (fn-peer-session-base peer)) (session (fn-post-session-base ps)) (env (fn-post-reader-env viewconfig observation)) (server (fn-nntp-xref-server env)) (r (fn-rcompat-retrieval session viewarchive (fn-gidx-pin-trie viewindex) :head (list token) server fn-arena)) (p (fn-served-dispatch conn (list :command line) fn-arena))) (implies (and (fn-auth-sessionp as) (not (fn-auth-session-handshakingp as)) (not (fn-auth-sasl-waitingp as)) (or (not (fn-auth-config-requiredp (fn-auth-session-config as))) (fn-auth-session-subject as)) (fn-peer-sessionp peer) (null (fn-peer-session-peer peer)) (fn-post-sessionp ps) (not (fn-post-session-awaiting ps)) (fn-nntp-sessionp session) (equal (fn-nntp-session-openp session) t) (fn-nntp-session-projected session) (fn-nntp-command-inputp line) (equal (fn-nntp-tokenize line) (list *fn-shd-head-keyword* token)) server (fn-gidx-pinp viewindex) (not (fn-nntp-number-withdrawn-p session viewarchive viewindex token)) (not (and (fn-nntp-message-id-tokenp token) (fn-nntp-msgid-withdrawn-p viewindex token)))) (and (equal (fn-served-result-effects p) (fn-nntp-result-effects r)) (equal (fn-post-session-base (fn-peer-session-base (fn-auth-session-base (fn-served-conn-session (fn-served-result-conn p))))) (fn-nntp-result-session r)) (equal (fn-served-conn-pinned (fn-served-result-conn p)) (fn-served-conn-pinned conn)) (equal (fn-served-conn-archive (fn-served-result-conn p)) (fn-served-conn-archive conn)) (equal (fn-served-conn-index (fn-served-result-conn p)) (fn-served-conn-index conn))))) :rule-classes nil :hints (("Goal" :use ((:instance fn-shd-auth-is-served-retrieval (as (fn-served-conn-session conn)) (config (fn-served-conn-config conn)) (archive (fn-served-conn-archive conn)) (index (fn-served-conn-pinned-index conn)) (verdicts (fn-served-conn-verdicts conn)) (observation (fn-served-conn-observation conn)) (injection (fn-served-conn-injection conn))) fn-shd-served-reader-dispatch-is-the-auth-answer-by-definition (:instance fn-shd-retrieval-effects-true-listp (session (fn-post-session-base (fn-peer-session-base (fn-auth-view-session (fn-served-conn-session conn) (fn-served-conn-config conn))))) (archive (fn-auth-view-archive (fn-served-conn-session conn) (fn-served-conn-config conn) (fn-served-conn-archive conn))) (trie (fn-gidx-pin-trie (fn-auth-view-index (fn-served-conn-session conn) (fn-served-conn-config conn) (fn-served-conn-archive conn) (fn-served-conn-pinned-index conn)))) (kind :head) (args (list token)) (server (fn-nntp-xref-server (fn-post-reader-env (fn-auth-view-config (fn-served-conn-session conn) (fn-auth-moderation-config (fn-served-conn-session conn) (fn-served-conn-config conn)) (fn-served-conn-archive conn)) (fn-served-conn-observation conn)))))) :in-theory (theory (quote minimal-theory))))))

(local
 (defthm fn-shd-head-dispatch-keeps-the-command-wire-by-definition
  (let ((r (fn-auth-step-pinned (fn-served-conn-session conn)
                                (fn-served-conn-archive conn)
                                (fn-served-conn-pinned-index conn)
                                (fn-served-conn-verdicts conn)
                                (fn-served-conn-config conn)
                                (fn-served-conn-observation conn)
                                (fn-served-conn-injection conn)
                                (list :command line) fn-arena)))
    (implies (and (equal (fn-nntp-tokenize line) (list *fn-shd-head-keyword* token))
                  (not (fn-post-offeredp (fn-post-result-effects r))))
             (equal (fn-served-conn-wire
                     (fn-served-result-conn (fn-served-dispatch conn (list :command line) fn-arena)))
                    (fn-served-conn-wire conn))))
  :hints (("Goal" :in-theory (e/d (fn-served-dispatch fn-served-dispatch-core
                                  fn-shd-head-keeps-the-pinned-view-by-definition)
                                 (fn-auth-step-pinned fn-served-advance-eventp
                                  fn-post-offeredp fn-post-result-effects fn-post-result-session
                                  fn-post-result-submission fn-served-make-result
                                  fn-served-make-conn-live fn-wire-begin-article-with-line-limit))))))

(local (defthm fn-shd-append-nil
 (equal (append xs nil) (true-list-fix xs))
 :hints (("Goal" :in-theory (enable binary-append true-list-fix)))))

(local (defthm fn-shd-true-list-fix-identity
 (implies (true-listp xs) (equal (true-list-fix xs) xs))
 :hints (("Goal" :induct (true-list-fix xs) :in-theory (enable true-list-fix)))))


(local
 (defthm
  fn-shd-served-step-is-head-retrieval
  (let*
    ((as (fn-served-conn-session conn))
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
     (server (fn-nntp-xref-server env))
     (r
       (fn-rcompat-retrieval
         session
         viewarchive
         (fn-gidx-pin-trie viewindex)
         :head
         (list token)
         server
         fn-arena))
     (p (fn-served-step conn (append line (quote (13 10))) fn-arena)))
    (implies
      (and
        (fn-served-conn-shapep conn)
        (equal
          (fn-served-conn-wire conn)
          (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit))
        (fn-wire-statep (fn-served-conn-wire conn))
        (fn-wire-line-contentp line)
        (natp line-limit)
        (<= (len line) line-limit)
        (not (fn-served-haltedp conn))
        (fn-auth-sessionp as)
        (not (fn-auth-session-handshakingp as))
        (not (fn-auth-sasl-waitingp as))
        (or
          (not (fn-auth-config-requiredp (fn-auth-session-config as)))
          (fn-auth-session-subject as))
        (fn-peer-sessionp peer)
        (null (fn-peer-session-peer peer))
        (fn-post-sessionp ps)
        (not (fn-post-session-awaiting ps))
        (fn-nntp-sessionp session)
        (equal (fn-nntp-session-openp session) t)
        (fn-nntp-session-projected session)
        (fn-nntp-command-inputp line)
        (equal (fn-nntp-tokenize line) (list *fn-shd-head-keyword* token))
        server
        (fn-gidx-pinp viewindex)
        (not (fn-nntp-number-withdrawn-p session viewarchive viewindex token))
        (not (and (fn-nntp-message-id-tokenp token) (fn-nntp-msgid-withdrawn-p viewindex token))))
      (and
        (equal (fn-served-result-effects p) (fn-nntp-result-effects r))
        (equal
          (fn-post-session-base
            (fn-peer-session-base
              (fn-auth-session-base (fn-served-conn-session (fn-served-result-conn p)))))
          (fn-nntp-result-session r))
        (equal (fn-served-conn-pinned (fn-served-result-conn p)) (fn-served-conn-pinned conn))
        (equal (fn-served-conn-archive (fn-served-result-conn p)) (fn-served-conn-archive conn))
        (equal (fn-served-conn-index (fn-served-result-conn p)) (fn-served-conn-index conn)))))
  :rule-classes
  nil
  :hints
  (("Goal"
     :use
     (fn-shd-dispatch-is-served-retrieval
       fn-shd-command-line-feed-reaches-its-dispatch
       fn-shd-head-dispatch-keeps-the-command-wire-by-definition
       (:instance
         fn-shd-auth-is-served-retrieval
         (as (fn-served-conn-session conn))
         (config (fn-served-conn-config conn))
         (archive (fn-served-conn-archive conn))
         (index (fn-served-conn-pinned-index conn))
         (verdicts (fn-served-conn-verdicts conn))
         (observation (fn-served-conn-observation conn))
         (injection (fn-served-conn-injection conn)))
       (:instance
         fn-shd-retrieval-has-no-offer
         (session
           (fn-post-session-base
             (fn-peer-session-base
               (fn-auth-view-session (fn-served-conn-session conn) (fn-served-conn-config conn)))))
         (archive
           (fn-auth-view-archive
             (fn-served-conn-session conn)
             (fn-served-conn-config conn)
             (fn-served-conn-archive conn)))
         (trie
           (fn-gidx-pin-trie
             (fn-auth-view-index
               (fn-served-conn-session conn)
               (fn-served-conn-config conn)
               (fn-served-conn-archive conn)
               (fn-served-conn-pinned-index conn))))
         (kind :head)
         (args (list token))
         (server
           (fn-nntp-xref-server
             (fn-post-reader-env
               (fn-auth-view-config
                 (fn-served-conn-session conn)
                 (fn-auth-moderation-config
                   (fn-served-conn-session conn)
                   (fn-served-conn-config conn))
                 (fn-served-conn-archive conn))
               (fn-served-conn-observation conn)))))
       (:instance
         fn-shd-retrieval-effects-true-listp
         (session
           (fn-post-session-base
             (fn-peer-session-base
               (fn-auth-view-session (fn-served-conn-session conn) (fn-served-conn-config conn)))))
         (archive
           (fn-auth-view-archive
             (fn-served-conn-session conn)
             (fn-served-conn-config conn)
             (fn-served-conn-archive conn)))
         (trie
           (fn-gidx-pin-trie
             (fn-auth-view-index
               (fn-served-conn-session conn)
               (fn-served-conn-config conn)
               (fn-served-conn-archive conn)
               (fn-served-conn-pinned-index conn))))
         (kind :head)
         (args (list token))
         (server
           (fn-nntp-xref-server
             (fn-post-reader-env
               (fn-auth-view-config
                 (fn-served-conn-session conn)
                 (fn-auth-moderation-config
                   (fn-served-conn-session conn)
                   (fn-served-conn-config conn))
                 (fn-served-conn-archive conn))
               (fn-served-conn-observation conn))))))
     :in-theory
     (union-theories
       (quote
         (fn-served-step
           fn-served-closed-wirep
           fn-served-conn-with-wire-of-own-wire
           fn-served-conn-fields-of-with-wire
           fn-served-result-effects-of-fn-served-make-result
           fn-served-result-conn-of-fn-served-make-result
           fn-wire-state-mode-of-fn-wire-make-state
           fn-shd-append-nil
           fn-shd-true-list-fix-identity
           car-cons
           cdr-cons))
       (theory (quote minimal-theory))))))

)

(local
 (defthm fn-shd-valid-peer-has-valid-post
    (implies (fn-peer-sessionp peer) (fn-post-sessionp (fn-peer-session-base peer)))
    :hints
    (("Goal" :in-theory (e/d (fn-peer-sessionp) (fn-post-sessionp))))))

(local
 (defthm fn-shd-valid-post-has-valid-reader
    (implies (fn-post-sessionp ps) (fn-nntp-sessionp (fn-post-session-base ps)))
    :hints
    (("Goal" :in-theory (e/d (fn-post-sessionp) (fn-nntp-sessionp))))))

(local
 (defthm fn-shd-auth-view-is-a-valid-reader-stack
    (implies
      (fn-auth-sessionp as)
      (let*
        ((peer (fn-auth-view-session as config)) (ps (fn-peer-session-base peer)))
        (and
          (fn-peer-sessionp peer)
          (fn-post-sessionp ps)
          (fn-nntp-sessionp (fn-post-session-base ps)))))
    :hints
    (("Goal" :use fn-auth-view-session-is-a-session :in-theory
       (disable fn-auth-sessionp fn-auth-view-session fn-peer-sessionp fn-post-sessionp
         fn-peer-session-shapep
         fn-post-session-shapep
         fn-nntp-sessionp)))))

(local
 (defthm fn-shd-command-wire-limit-is-natural
    (implies
      (fn-wire-statep (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit))
      (natp line-limit))
    :hints
    (("Goal" :in-theory (enable fn-wire-statep)))))

(local
 (defthm fn-shd-open-nonhandshaking-view-is-not-halted
    (implies
      (and
        (not (fn-auth-session-handshakingp (fn-served-conn-session conn)))
        (equal
          (fn-nntp-session-openp
            (fn-post-session-base
              (fn-peer-session-base
                (fn-auth-view-session (fn-served-conn-session conn) (fn-served-conn-config conn)))))
          t))
      (not (fn-served-haltedp conn)))
    :hints
    (("Goal" :use
       (:instance fn-auth-view-session-keeps-role
         (as (fn-served-conn-session conn))
         (config (fn-served-conn-config conn)))
       :in-theory
       (e/d
         (fn-served-haltedp fn-served-tls-handshakingp fn-served-quitp)
         (fn-auth-view-session fn-auth-session-handshakingp fn-nntp-session-openp))))))

(local
 (defthm fn-shd-command-syntax-is-plain-line
    (implies (fn-nntp-command-linep line) (fn-wire-line-contentp line))
    :hints
    (("Goal" :induct
       (fn-nntp-command-linep line)
       :in-theory
       (enable fn-nntp-command-linep fn-nntp-command-bytep fn-nntp-space-or-tabp
         fn-wire-line-contentp
         fn-wire-octetp
         fn-bch-plain-octetsp
         fn-bch-octetp)))))

(local
 (defthm fn-shd-command-input-is-plain-line
    (implies (fn-nntp-command-inputp line) (fn-wire-line-contentp line))
    :hints
    (("Goal" :use fn-shd-command-syntax-is-plain-line :in-theory
       (union-theories (quote (fn-nntp-command-inputp)) (theory (quote minimal-theory)))))))

; Public keystone: the actual concrete connection representation at a command boundary.
; The constructor discharges shape and empty-wire equalities, not runtime validation.
(local
 (defthm fn-shd-concrete-command-connection-shape-by-definition
  (let ((conn (fn-served-make-conn-live
   (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit)
   auth-session archive-input config-input observation-input injection-input
   verdicts-input index-input buckets-input control-input pinned-input live-input)))
   (and (fn-served-conn-shapep conn)
        (equal (fn-served-conn-wire conn)
               (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit))))
  :hints (("Goal" :in-theory (enable fn-served-conn-shapep
   fn-served-make-conn-live fn-served-conn-wire fn-ag-car)))))

(defthm
  fn-shd-command-wire-head-is-served-retrieval
  (let*
    ((conn
       (fn-served-make-conn-live
         (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit)
         auth-session
         archive-input
         config-input
         observation-input
         injection-input
         verdicts-input
         index-input
         buckets-input
         control-input
         pinned-input
         live-input))
     (as (fn-served-conn-session conn))
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
     (server (fn-nntp-xref-server env))
     (r
       (fn-rcompat-retrieval
         session
         viewarchive
         (fn-gidx-pin-trie viewindex)
         :head
         (list token)
         server
         fn-arena))
     (p (fn-served-step conn (append line (quote (13 10))) fn-arena)))
    (implies
      (and
        (fn-wire-statep (fn-served-conn-wire conn))
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
        (equal (fn-nntp-tokenize line) (list *fn-shd-head-keyword* token))
        server
        (fn-gidx-pinp viewindex)
        (not (fn-nntp-number-withdrawn-p session viewarchive viewindex token))
        (not (and (fn-nntp-message-id-tokenp token) (fn-nntp-msgid-withdrawn-p viewindex token))))
      (and
        (equal (fn-served-result-effects p) (fn-nntp-result-effects r))
        (equal
          (fn-post-session-base
            (fn-peer-session-base
              (fn-auth-session-base (fn-served-conn-session (fn-served-result-conn p)))))
          (fn-nntp-result-session r))
        (equal (fn-served-conn-pinned (fn-served-result-conn p)) (fn-served-conn-pinned conn))
        (equal (fn-served-conn-archive (fn-served-result-conn p)) (fn-served-conn-archive conn))
        (equal (fn-served-conn-index (fn-served-result-conn p)) (fn-served-conn-index conn)))))
  :rule-classes
  nil
  :hints
  (("Goal"
     :use
     (fn-shd-concrete-command-connection-shape-by-definition
       (:instance
         fn-shd-served-step-is-head-retrieval
         (conn
           (fn-served-make-conn-live
             (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit)
             auth-session
             archive-input
             config-input
             observation-input
             injection-input
             verdicts-input
             index-input
             buckets-input
             control-input
             pinned-input
             live-input)))
       (:instance
         fn-shd-auth-view-is-a-valid-reader-stack
         (as
           (fn-served-conn-session
             (fn-served-make-conn-live
               (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit)
               auth-session
               archive-input
               config-input
               observation-input
               injection-input
               verdicts-input
               index-input
               buckets-input
               control-input
               pinned-input
               live-input)))
         (config
           (fn-served-conn-config
             (fn-served-make-conn-live
               (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit)
               auth-session
               archive-input
               config-input
               observation-input
               injection-input
               verdicts-input
               index-input
               buckets-input
               control-input
               pinned-input
               live-input))))
       fn-shd-command-wire-limit-is-natural
       (:instance
         fn-shd-open-nonhandshaking-view-is-not-halted
         (conn
           (fn-served-make-conn-live
             (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit)
             auth-session
             archive-input
             config-input
             observation-input
             injection-input
             verdicts-input
             index-input
             buckets-input
             control-input
             pinned-input
             live-input)))
       fn-shd-command-input-is-plain-line)
     :in-theory
     (theory (quote minimal-theory)))))
