;; P8 / PRF-026: the served HDR :fn-verified reply is the Store's recorded
;; verdict, stated over the functions the host calls.
;;
;; Host path (reader): host/native/owner.lisp calls fn-owner-chunk
;; (host/owner-host.lisp), which runs fn-ocfg-read-tls-prefix; the theorem
;; fn-ocfg-read-tls-prefix-is-full-read (books/owner-tls-prefix) equates that
;; with fn-ocfg-read, which is fn-own-read on the connection.  fn-own-read runs
;; the byte fold fn-served-step (books/served) over the connection's pinned
;; archive and verdict list; the fold hands each framed event to
;; fn-served-dispatch.  The keystone below is over fn-own-read.
;;
;; Framing is a hypothesis, not a theorem, here: the read's octets other than
;; the last frame no event, and the last octet frames exactly one command
;; line.  What the wire does to an arbitrary octet string is the wire book's
;; business; this book says what the served reply is once that line is framed.
(in-package "ACL2")
(include-book "owner")
(include-book "nntp-auth-fold")


;; The HDR :fn-verified reply offers no article and its effects are a list.

(defthm fn-ovr-hdr-msgid-has-no-offer
  (not (fn-post-offeredp
        (fn-nntp-result-effects
         (fn-nntp-verdict-hdr-msgid session archive verdicts token))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-verdict-hdr-msgid)
                                  (fn-nntp-single fn-nntp-multi
                                   fn-post-offeredp)))))

(defthm fn-ovr-hdr-msgid-effects-true-listp
  (true-listp (fn-nntp-result-effects
               (fn-nntp-verdict-hdr-msgid session archive verdicts token)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-verdict-hdr-msgid fn-nntp-single
                                   fn-nntp-multi fn-nntp-make-result
                                   fn-nntp-result-effects)
                                  ()))))

;; One framed command line, through the pinned dispatcher chain the served
;; fold calls: fn-auth-step-pinned, fn-peer-step-pinned,
;; fn-nntp-post-step-pinned, fn-nntp-step-pinned, fn-nntp-command-pinned and
;; fn-nntp-archive-command-pinned, down to fn-nntp-verdict-hdr-msgid.

(defthm fn-served-dispatch-hdr-fn-verified-msgid
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
                  (consp (cddr tokens)) (null (cdddr tokens))
                  (fn-nntp-keyword-tokenp (car tokens))
                  (fn-nntp-keywordp (car tokens) "HDR")
                  (fn-nntp-keywordp (cadr tokens) ":FN-VERIFIED")
                  (fn-nntp-message-id-tokenp (caddr tokens))
                  (not (fn-nntp-range-okp (fn-nntp-parse-range (caddr tokens)))))
             (equal (fn-served-result-effects
                     (fn-served-dispatch conn (list :command line)))
                    (fn-nntp-result-effects
                     (fn-nntp-verdict-hdr-msgid
                      ns (fn-served-conn-archive conn)
                      (fn-served-conn-verdicts conn) (caddr tokens))))))
  :hints (("Goal" :in-theory (e/d (fn-served-dispatch fn-auth-step-pinned
                                   fn-auth-command fn-auth-delegate-pinned
                                   fn-peer-step-pinned fn-peer-delegate-pinned
                                   fn-nntp-post-step-pinned fn-nntp-step-pinned
                                   fn-nntp-command-pinned
                                   fn-nntp-archive-command-pinned
                                   fn-nntp-verdict-hdr-response
                                   fn-auth-tls-eventp fn-nntp-keywordp fn-nntp-archive-keywordp)
                                  (fn-nntp-verdict-hdr-msgid
                                   fn-nntp-tokenize fn-auth-sessionp
                                   fn-peer-sessionp fn-post-sessionp
                                   fn-nntp-sessionp fn-auth-gatedp fn-nntp-upcase-keyword fn-nntp-message-id-tokenp fn-nntp-parse-range fn-nntp-range-okp fn-nntp-keyword-tokenp fn-nntp-command-inputp fn-nntp-command-arguments-at-mostp)))))

(defthm fn-served-dispatch-hdr-fn-verified-keeps-wire
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
                  (consp (cddr tokens)) (null (cdddr tokens))
                  (fn-nntp-keyword-tokenp (car tokens))
                  (fn-nntp-keywordp (car tokens) "HDR")
                  (fn-nntp-keywordp (cadr tokens) ":FN-VERIFIED")
                  (fn-nntp-message-id-tokenp (caddr tokens))
                  (not (fn-nntp-range-okp (fn-nntp-parse-range (caddr tokens)))))
             (equal (fn-served-conn-wire
                     (fn-served-result-conn
                      (fn-served-dispatch conn (list :command line))))
                    (fn-served-conn-wire conn))))
  :hints (("Goal" :in-theory (e/d (fn-served-dispatch fn-auth-step-pinned
                                   fn-auth-command fn-auth-delegate-pinned
                                   fn-peer-step-pinned fn-peer-delegate-pinned
                                   fn-nntp-post-step-pinned fn-nntp-step-pinned
                                   fn-nntp-command-pinned
                                   fn-nntp-archive-command-pinned
                                   fn-nntp-verdict-hdr-response
                                   fn-auth-tls-eventp fn-nntp-keywordp fn-nntp-archive-keywordp)
                                  (fn-nntp-verdict-hdr-msgid
                                   fn-nntp-tokenize fn-auth-sessionp
                                   fn-peer-sessionp fn-post-sessionp
                                   fn-nntp-sessionp fn-auth-gatedp fn-nntp-upcase-keyword fn-nntp-message-id-tokenp fn-nntp-parse-range fn-nntp-range-okp fn-nntp-keyword-tokenp fn-nntp-command-inputp fn-nntp-command-arguments-at-mostp)))))

;; The byte fold over a read whose octets frame nothing until the last.

(defun fn-ovr-with-wire (conn wire)
  (declare (xargs :guard t))
  (fn-served-make-conn-group-indexed
   wire (fn-served-conn-session conn) (fn-served-conn-archive conn)
   (fn-served-conn-config conn) (fn-served-conn-observation conn)
   (fn-served-conn-injection conn) (fn-served-conn-verdicts conn)
   (fn-served-conn-index conn) (fn-served-conn-group-index conn)))
(defthm fn-ovr-feed-byte-silent
  (implies (not (consp (fn-wire-result-events
                 (fn-wire-feed-byte (fn-served-conn-wire conn) byte))))
           (equal (fn-served-feed-byte conn byte)
                  (fn-served-make-result
                   (fn-ovr-with-wire conn (fn-wire-result-state
                                           (fn-wire-feed-byte
                                            (fn-served-conn-wire conn) byte)))
                   nil)))
  :hints (("Goal" :in-theory (e/d (fn-served-feed-byte fn-served-dispatch-events)
                                  (fn-wire-feed-byte)))))
(defthm fn-ovr-with-wire-of-with-wire
  (equal (fn-ovr-with-wire (fn-ovr-with-wire conn w1) w2)
         (fn-ovr-with-wire conn w2)))
(defthm fn-ovr-wire-of-with-wire
  (equal (fn-served-conn-wire (fn-ovr-with-wire conn w)) w))
(defthm fn-ovr-handshaking-of-with-wire
  (equal (fn-served-tls-handshakingp (fn-ovr-with-wire conn w))
         (fn-served-tls-handshakingp conn))
  :hints (("Goal" :in-theory (enable fn-served-tls-handshakingp))))
(defthm fn-ovr-with-own-wire
  (implies (fn-served-conn-shapep conn)
           (equal (fn-ovr-with-wire conn (fn-served-conn-wire conn)) conn))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-served-conn-shapep fn-served-make-conn-group-indexed
                              fn-served-conn-wire fn-served-conn-session
                              fn-served-conn-archive fn-served-conn-config
                              fn-served-conn-observation fn-served-conn-injection
                              fn-served-conn-verdicts fn-served-conn-index
                              fn-served-conn-group-index)
           :expand ((len conn) (len (cdr conn)) (len (cddr conn)) (len (cdddr conn))
                    (len (cddddr conn)) (len (cdr (cddddr conn)))
                    (len (cddr (cddddr conn))) (len (cdddr (cddddr conn)))
                    (len (cddddr (cddddr conn)))
                    (len (cdr (cddddr (cddddr conn))))
                    (true-listp conn) (true-listp (cdr conn)) (true-listp (cddr conn))
                    (true-listp (cdddr conn)) (true-listp (cddddr conn))
                    (true-listp (cdr (cddddr conn))) (true-listp (cddr (cddddr conn)))
                    (true-listp (cdddr (cddddr conn))) (true-listp (cddddr (cddddr conn)))
                    (true-listp (cdr (cddddr (cddddr conn))))))))
(defthm fn-ovr-with-wire-is-shaped
  (fn-served-conn-shapep (fn-ovr-with-wire conn w)))
(in-theory (disable fn-ovr-with-wire))
(defun fn-ovr-induct (conn prefix)
  (if (consp prefix)
      (fn-ovr-induct (fn-ovr-with-wire conn (fn-wire-result-state
                                             (fn-wire-feed-byte
                                              (fn-served-conn-wire conn)
                                              (car prefix))))
                     (cdr prefix))
    conn))
(defthm fn-ovr-feed-silent-prefix
  (implies (and (fn-served-conn-shapep conn)
                (fn-wire-statep (fn-served-conn-wire conn))
                (not (fn-served-closed-wirep (fn-served-conn-wire conn)))
                (not (fn-served-tls-handshakingp conn))
                (not (fn-wire-result-events
                      (fn-wire-feed-proper (fn-served-conn-wire conn) prefix))))
           (and (equal (fn-served-result-effects
                        (fn-served-feed conn (append prefix rest)))
                       (fn-served-result-effects
                        (fn-served-feed
                         (fn-ovr-with-wire
                          conn (fn-wire-result-state
                                (fn-wire-feed-proper (fn-served-conn-wire conn)
                                                     prefix)))
                         rest)))
                (equal (fn-served-result-conn
                        (fn-served-feed conn (append prefix rest)))
                       (fn-served-result-conn
                        (fn-served-feed
                         (fn-ovr-with-wire
                          conn (fn-wire-result-state
                                (fn-wire-feed-proper (fn-served-conn-wire conn)
                                                     prefix)))
                         rest)))))
  :hints (("Goal" :induct (fn-ovr-induct conn prefix)
           :in-theory (e/d (fn-served-closed-wirep)
                           (fn-served-feed-byte fn-wire-feed-byte fn-wire-statep fn-served-feed-of-append
                            fn-served-tls-handshakingp)))
          ("Subgoal *1/1" :expand ((fn-served-feed conn (cons (car prefix) (append (cdr prefix) rest)))
                                   (fn-wire-feed-proper (fn-served-conn-wire conn) prefix))
           :use ((:instance fn-wire-feed-byte-silent-step-stays-open
                  (wire-state (fn-served-conn-wire conn)) (byte (car prefix)))
                 (:instance fn-wire-feed-byte-preserves-statep
                  (wire-state (fn-served-conn-wire conn)) (byte (car prefix)))))))

(defthm fn-ovr-fields-of-with-wire
  (and (equal (fn-served-conn-session (fn-ovr-with-wire conn w))
              (fn-served-conn-session conn))
       (equal (fn-served-conn-archive (fn-ovr-with-wire conn w))
              (fn-served-conn-archive conn))
       (equal (fn-served-conn-verdicts (fn-ovr-with-wire conn w))
              (fn-served-conn-verdicts conn)))
  :hints (("Goal" :in-theory (enable fn-ovr-with-wire))))

(defthm fn-ovr-dispatch-effects-true-listp
  (true-listp (fn-served-result-effects (fn-served-dispatch conn event)))
  :hints (("Goal" :in-theory (e/d (fn-served-dispatch)
                                  (fn-auth-step-pinned fn-post-offeredp
                                   fn-wire-begin-article-with-line-limit)))))

(defthm fn-ovr-feed-effects-true-listp
  (true-listp (fn-served-result-effects (fn-served-feed conn octets)))
  :hints (("Goal" :induct (fn-served-feed conn octets)
           :in-theory (e/d (fn-served-feed) (fn-served-feed-byte fn-served-feed-of-append)))))

(defthm fn-ovr-wire-feed-proper-silent-stays-open
  (implies (and (fn-wire-statep w)
                (not (equal (fn-wire-state-mode w) :closed))
                (not (fn-wire-result-events (fn-wire-feed-proper w prefix))))
           (not (equal (fn-wire-state-mode
                        (fn-wire-result-state (fn-wire-feed-proper w prefix)))
                       :closed)))
  :hints (("Goal" :induct (fn-wire-feed-proper w prefix)
           :in-theory (e/d (fn-wire-feed-proper)
                           (fn-wire-feed-byte fn-wire-statep)))
          ("Subgoal *1/2" :use ((:instance fn-wire-feed-byte-silent-step-stays-open
                                 (wire-state w) (byte (car prefix)))
                                (:instance fn-wire-feed-byte-preserves-statep
                                 (wire-state w) (byte (car prefix)))))))

(defthm fn-ovr-feed-one-framing-byte
  (implies (and (not (fn-served-closed-wirep (fn-served-conn-wire c)))
                (not (fn-served-tls-handshakingp c))
                (equal (fn-wire-result-events
                        (fn-wire-feed-byte (fn-served-conn-wire c) byte))
                       (list event)))
           (let ((here (fn-served-dispatch
                        (fn-ovr-with-wire
                         c (fn-wire-result-state
                            (fn-wire-feed-byte (fn-served-conn-wire c) byte)))
                        event)))
             (and (equal (fn-served-result-effects (fn-served-feed c (list byte)))
                         (fn-served-result-effects here))
                  (equal (fn-served-result-conn (fn-served-feed c (list byte)))
                         (fn-served-result-conn here)))))
  :hints (("Goal" :do-not-induct t
           :expand ((fn-served-feed c (list byte))
                    (:free (x) (fn-served-dispatch-events x (list event)))
                    (:free (x) (fn-served-dispatch-events x nil))
                    (:free (x) (fn-served-feed x nil)))
           :in-theory (e/d (fn-served-feed-byte fn-ovr-with-wire)
                           (fn-served-dispatch fn-wire-feed-byte
                            fn-served-feed fn-served-dispatch-events)))))

(defthm fn-served-step-of-one-framed-event
  (let* ((w0 (fn-served-conn-wire conn))
         (w1 (fn-wire-result-state (fn-wire-feed-proper w0 prefix)))
         (w2 (fn-wire-result-state (fn-wire-feed-byte w1 byte)))
         (here (fn-served-dispatch (fn-ovr-with-wire conn w2) event)))
    (implies (and (fn-served-conn-shapep conn)
                  (fn-wire-statep w0)
                  (not (fn-served-closed-wirep w0))
                  (not (fn-served-tls-handshakingp conn))
                  (not (fn-wire-result-events (fn-wire-feed-proper w0 prefix)))
                  (equal (fn-wire-result-events (fn-wire-feed-byte w1 byte))
                         (list event))
                  (not (fn-served-closed-wirep
                        (fn-served-conn-wire (fn-served-result-conn here)))))
             (equal (fn-served-result-effects
                     (fn-served-step conn (append prefix (list byte))))
                    (fn-served-result-effects here))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-ovr-feed-silent-prefix (rest (list byte)))
                 (:instance fn-ovr-wire-feed-proper-silent-stays-open
                  (w (fn-served-conn-wire conn)))
                 (:instance fn-ovr-feed-one-framing-byte
                  (c (fn-ovr-with-wire conn (fn-wire-result-state
                                             (fn-wire-feed-proper
                                              (fn-served-conn-wire conn) prefix))))))
           :in-theory (e/d (fn-served-step fn-served-closed-wirep)
                           (fn-ovr-feed-silent-prefix fn-served-dispatch
                            fn-ovr-feed-one-framing-byte
                            fn-ovr-wire-feed-proper-silent-stays-open
                            fn-wire-feed-byte fn-wire-feed-proper fn-wire-statep
                            fn-served-feed fn-served-feed-of-append
                            fn-served-dispatch-events)))))

;; The served step: one read carrying one HDR :fn-verified <msgid> line answers
;; the verdict the connection pinned, selected by the article's Message-ID.

(defthm fn-served-step-hdr-fn-verified-is-the-pinned-verdict
  (let* ((w0 (fn-served-conn-wire conn))
         (w1 (fn-wire-result-state (fn-wire-feed-proper w0 prefix)))
         (w2 (fn-wire-result-state (fn-wire-feed-byte w1 byte)))
         (as (fn-served-conn-session conn))
         (ps (fn-auth-session-base as))
         (pst (fn-peer-session-base ps))
         (ns (fn-post-session-base pst))
         (tokens (fn-nntp-tokenize line))
         (article (fn-find-article (fn-nntp-token-string (caddr tokens))
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
                  (fn-nntp-command-inputp line)
                  (fn-nntp-command-arguments-at-mostp tokens)
                  (consp (cddr tokens)) (null (cdddr tokens))
                  (fn-nntp-keyword-tokenp (car tokens))
                  (fn-nntp-keywordp (car tokens) "HDR")
                  (fn-nntp-keywordp (cadr tokens) ":FN-VERIFIED")
                  (fn-nntp-message-id-tokenp (caddr tokens))
                  (not (fn-nntp-range-okp (fn-nntp-parse-range (caddr tokens))))
                  (consp article))
             (equal (fn-served-result-effects
                     (fn-served-step conn (append prefix (list byte))))
                    (fn-nntp-result-effects
                     (fn-nntp-multi
                      ns (fn-nntp-hdr-initial nil)
                      (list (fn-nntp-hdr-line
                             (fn-nntp-decimal-field 0)
                             (fn-stx-reader-item
                              (fn-stx-reader-lookup
                               (fn-article-msgid article)
                               (fn-served-conn-verdicts conn))))))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-served-step-of-one-framed-event
                  (event (list :command line)))
                 (:instance fn-served-dispatch-hdr-fn-verified-msgid
                  (conn (fn-ovr-with-wire
                         conn
                         (fn-wire-result-state
                          (fn-wire-feed-byte
                           (fn-wire-result-state
                            (fn-wire-feed-proper (fn-served-conn-wire conn) prefix))
                           byte)))))
                 (:instance fn-served-dispatch-hdr-fn-verified-keeps-wire
                  (conn (fn-ovr-with-wire
                         conn
                         (fn-wire-result-state
                          (fn-wire-feed-byte
                           (fn-wire-result-state
                            (fn-wire-feed-proper (fn-served-conn-wire conn) prefix))
                           byte)))))
                 (:instance fn-nntp-verdict-hdr-msgid-is-recorded
                  (session (fn-post-session-base
                            (fn-peer-session-base
                             (fn-auth-session-base (fn-served-conn-session conn)))))
                  (archive (fn-served-conn-archive conn))
                  (verdicts (fn-served-conn-verdicts conn))
                  (token (caddr (fn-nntp-tokenize line)))))
           :in-theory (e/d (fn-served-closed-wirep fn-served-tls-handshakingp)
                           (fn-served-step-of-one-framed-event
                            fn-served-dispatch-hdr-fn-verified-msgid
                            fn-served-dispatch-hdr-fn-verified-keeps-wire
                            fn-nntp-verdict-hdr-msgid-is-recorded
                            fn-served-step fn-served-dispatch
                            fn-wire-feed-byte fn-wire-feed-proper fn-wire-statep
                            fn-nntp-verdict-hdr-msgid fn-nntp-multi
                            fn-auth-sessionp fn-peer-sessionp fn-post-sessionp
                            fn-nntp-sessionp fn-nntp-tokenize fn-auth-gatedp
                            fn-nntp-keywordp fn-nntp-message-id-tokenp
                            fn-nntp-command-inputp fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp fn-stx-reader-item fn-stx-reader-lookup
                            fn-find-article fn-nntp-hdr-line)))))

;; PRF-026 keystone over the host-called reader port.  host/native/owner.lisp
;; (fnn-owner-action 'fn-owner-chunk ...) runs host/owner-host.lisp
;; fn-owner-chunk, that is fn-ocfg-read-tls-prefix, equal to fn-ocfg-read by
;; fn-ocfg-read-tls-prefix-is-full-read, whose reply is (car (fn-own-read ...)).
;; The reply's verdict field is the connection's pinned verdict for the
;; retrieved article's Message-ID; no keyring or current Store is consulted.
;; Uses fn-nntp-verdict-hdr-msgid-is-recorded (books/nntp-verdict) as a lemma.
(defthm fn-own-read-hdr-fn-verified-is-the-pinned-verdict
  (let* ((conn (fn-own-find-conn id (fn-own-conns o)))
         (w0 (fn-own-conn-wire conn))
         (w1 (fn-wire-result-state (fn-wire-feed-proper w0 prefix)))
         (w2 (fn-wire-result-state (fn-wire-feed-byte w1 byte)))
         (as (fn-own-conn-live-session o conn))
         (ps (fn-auth-session-base as))
         (pst (fn-peer-session-base ps))
         (ns (fn-post-session-base pst))
         (tokens (fn-nntp-tokenize line))
         (article (fn-find-article (fn-nntp-token-string (caddr tokens))
                                   (fn-state-articles
                                    (fn-own-conn-archive conn)))))
    (implies (and conn
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
                  (consp (cddr tokens)) (null (cdddr tokens))
                  (fn-nntp-keyword-tokenp (car tokens))
                  (fn-nntp-keywordp (car tokens) "HDR")
                  (fn-nntp-keywordp (cadr tokens) ":FN-VERIFIED")
                  (fn-nntp-message-id-tokenp (caddr tokens))
                  (not (fn-nntp-range-okp (fn-nntp-parse-range (caddr tokens))))
                  (consp article))
             (equal (car (fn-own-read o id (append prefix (list byte))))
                    (fn-nntp-result-effects
                     (fn-nntp-multi
                      ns (fn-nntp-hdr-initial nil)
                      (list (fn-nntp-hdr-line
                             (fn-nntp-decimal-field 0)
                             (fn-stx-reader-item
                              (fn-stx-reader-lookup
                               (fn-article-msgid article)
                               (fn-own-conn-verdicts conn))))))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-served-step-hdr-fn-verified-is-the-pinned-verdict
                  (conn (fn-served-make-conn-group-indexed
                         (fn-own-conn-wire (fn-own-find-conn id (fn-own-conns o)))
                         (fn-own-conn-live-session o (fn-own-find-conn id (fn-own-conns o)))
                         (fn-own-conn-archive (fn-own-find-conn id (fn-own-conns o)))
                         (fn-own-conn-config (fn-own-find-conn id (fn-own-conns o)))
                         (fn-own-conn-observation (fn-own-find-conn id (fn-own-conns o)))
                         (fn-own-clock o)
                         (fn-own-conn-verdicts (fn-own-find-conn id (fn-own-conns o)))
                         (fn-own-conn-index (fn-own-find-conn id (fn-own-conns o)))
                         (fn-own-conn-group-index (fn-own-find-conn id (fn-own-conns o)))))))
           :in-theory (e/d (fn-own-read fn-own-finish-read)
                           (fn-served-step-hdr-fn-verified-is-the-pinned-verdict
                            fn-served-step fn-own-conn-live-session
                            fn-own-conn-wire fn-own-conn-archive fn-own-conn-config
                            fn-own-conn-observation fn-own-conn-verdicts
                            fn-own-conn-index fn-own-conn-group-index
                            fn-own-conn-session fn-own-find-conn
                            fn-wire-feed-byte fn-wire-feed-proper fn-wire-statep
                            fn-nntp-multi fn-stx-reader-item fn-stx-reader-lookup
                            fn-auth-sessionp fn-peer-sessionp fn-post-sessionp
                            fn-nntp-sessionp fn-nntp-tokenize fn-auth-gatedp
                            fn-nntp-keywordp fn-nntp-message-id-tokenp
                            fn-nntp-command-inputp fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp fn-find-article
                            fn-own-conn-boundedp fn-own-set-conns fn-own-enqueue
                            fn-own-replace-conn fn-own-remove-conn)))))

;; A reader opened after the owner's (:complete) event pins exactly the
;; verdict list fn-sn-finish produced.  With
;; fn-sn-finish-of-a-kind-4-acceptance-records-its-verdict
;; (books/hybrid-lifecycle-store-invariants) this closes the chain from a
;; durable kind-4 publication to the served HDR :fn-verified field.
;; Host lines: host/owner-host.lisp fn-owner-finish runs
;; (fn-owner-step (list :complete) state); fn-owner-open runs fn-ocfg-open.
(defthm fn-own-reader-opened-after-completion-pins-the-finished-verdicts
  (implies (and (fn-sn-completion-enabledp (fn-own-store o))
                (< (len (fn-own-conns o)) (nfix (fn-own-max-conns o))))
           (let* ((o2 (cdr (fn-own-open (fn-own-step o '(:complete)) acfg)))
                  (conn (fn-own-find-conn (fn-own-next-id o) (fn-own-conns o2))))
             (and conn
                  (equal (fn-own-conn-verdicts conn)
                         (fn-sn-verdicts (fn-sn-finish (fn-own-store o)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-snt-finish-image (s (fn-own-store o))))
           :in-theory (e/d (fn-own-step fn-own-complete fn-own-refresh
                            fn-own-open fn-own-store-idlep fn-snt-idle-phasep)
                           (fn-snt-finish-image fn-sn-finish fn-sn-completion-enabledp fn-own-view-make-group-indexed fn-own-conn-make-group-indexed
                            fn-served-open-group-indexed fn-midx-refresh
                            fn-gidx-build)))))
