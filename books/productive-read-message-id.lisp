; Productive Message-ID READ composition discovery; not a qualification root.
; This variant preserves the reader's cursor and uses its local number when
; the selected group contains the article (RFC 3977 section 6.2.1.2).
; Actual composed host Message-ID theorem admitted in pcr63; full positive
; and completion/credit removals admitted. Fresh scoped replay, remaining teeth,
; absence variants and qualification remain open.
(in-package "ACL2")

(include-book "productive-read-chain")

(defun fn-pcr-msgid-220-reply
  (session article server fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (fn-nntp-make-result session
    (list
      (fn-nntp-reply-effect
        (append
          (fn-nntp-crlf
            (fn-nntp-retrieval-initial :article
              (fn-nntp-msgid-local-number session article)
              article))
          (fn-nntp-stuff-lines
            (car (cdr (fn-nntp-crlf-lines (fn-pcr-served-octets server article fn-arena)))))
          (quote (46 13 10)))))))

; Expansion cannot disguise this ARTICLE-specific reply.
(local
  (defthm
    fn-pcr-msgid-220-result-has-220-prefix-by-definition
    (equal
      (fn-nntp-result-effects (fn-pcr-msgid-220-reply session article server fn-arena))
      (list
        (fn-nntp-reply-effect
          (append
            (quote (50 50 48))
            (cdr
              (cdr
                (cdr
                  (car
                    (cdr
                      (car
                        (fn-nntp-result-effects
                          (fn-pcr-msgid-220-reply session article server fn-arena))))))))))))
    :rule-classes
    nil
    :hints
    (("Goal"
       :in-theory
       (e/d
         (fn-pcr-msgid-220-reply fn-nntp-reply-effect fn-nntp-retrieval-initial fn-nntp-result-effects
           fn-nntp-make-result
           fn-nntp-append-pieces
           fn-nntp-crlf)
         (fn-nntp-decimal-field
           fn-article-msgid
           fn-pcr-served-octets
           fn-nntp-stuff-lines
           fn-nntp-crlf-lines
           fn-nntp-set-cursor
           fn-nntp-msgid-local-number))))))

(defthm
  fn-pcr-expanded-message-id-220-is-the-raw-reply
  (implies
    (equal
      (fn-ovw-expand effects fn-arena fn-cat)
      (fn-ovw-expand
        (fn-nntp-result-effects (fn-pcr-msgid-220-reply session article server fn-arena))
        fn-arena
        fn-cat))
    (equal
      effects
      (fn-nntp-result-effects (fn-pcr-msgid-220-reply session article server fn-arena))))
  :rule-classes
  nil
  :hints
  (("Goal"
     :use
     (fn-pcr-msgid-220-result-has-220-prefix-by-definition
       (:instance
         fn-pcr-expand-inverts-220-reply
         (tail
           (cdr
             (cdr
               (cdr
                 (car
                   (cdr
                     (car
                       (fn-nntp-result-effects
                         (fn-pcr-msgid-220-reply session article server fn-arena)))))))))))
     :in-theory
     (union-theories
       (quote (fn-ovw-expand-of-reply-cons fn-ovw-expand-of-nil))
       (theory (quote minimal-theory))))))

(defthm fn-pcr-msgid-retrieval-answers-220-without-moving-the-cursor
  (let
    ((article (fn-midx-lookup (fn-nntp-token-string token) trie)))
    (implies
      (and
        (fn-arena-p fn-arena)
        (fn-nntp-message-id-tokenp token)
        (fn-octet-listp token)
        (consp article)
        (fn-nntp-response-okp-of-bytes article (fn-nntp-article-bytes article fn-arena) :article)
        (fn-nntp-response-okp-of-bytes article
          (fn-pcr-served-octets server article fn-arena)
          :article))
      (equal
        (fn-rcompat-retrieval session archive trie :article (list token) server fn-arena)
        (fn-pcr-msgid-220-reply session article server fn-arena))))
  :rule-classes
  nil
  :hints
  (("Goal" :use
     ((:instance fn-rcompat-article-reply-exec-is-the-reply
        (article (fn-midx-lookup (fn-nntp-token-string token) trie))
        (number
          (fn-nntp-msgid-local-number session (fn-midx-lookup (fn-nntp-token-string token) trie)))
        (kind :article)
        (updatep nil)
        (group nil))
      (:instance fn-nntp-response-of-bytes-session
        (article (fn-midx-lookup (fn-nntp-token-string token) trie))
        (number
          (fn-nntp-msgid-local-number session (fn-midx-lookup (fn-nntp-token-string token) trie)))
        (kind :article)
        (updatep nil)
        (group nil)
        (bytes
          (fn-pcr-served-octets server (fn-midx-lookup (fn-nntp-token-string token) trie) fn-arena))))
     :in-theory
     (e/d
       (fn-rcompat-retrieval fn-rcompat-article-reply-exec
         fn-nntp-article-response-of-bytes
         fn-nntp-response-okp-of-bytes
         fn-nntp-section-of-bytes
         fn-pcr-served-octets
         fn-pcr-msgid-220-reply)
       (fn-rcompat-article-reply fn-rcompat-article-reply-exec-is-the-reply
         fn-nntp-response-of-bytes-session
         fn-rcompat-served-payload-of-bytes
         fn-nntp-article-bytes
         fn-nntp-crlf-lines
         fn-nntp-stuff-lines
         fn-nntp-retrieval-initial
         fn-nntp-make-result
         fn-nntp-reply-effect
         fn-midx-lookup
         fn-nntp-token-string
         fn-nntp-msgid-local-number
         fn-nntp-single
         fn-nntp-framed-of-bytes
         fn-rcl-tombstonep
         fn-nntp-article-idp
         fn-nntp-message-id-tokenp
         fn-nntp-number-tokenp
         fn-octet-listp)))))

(defthm fn-pcr-command-line-answers-the-message-id-article
  (let*
    ((article (fn-midx-lookup (fn-nntp-token-string token) (fn-gidx-pin-trie index)))
     (server (fn-nntp-xref-server env)))
    (implies
      (and
        (fn-nntp-sessionp session)
        (equal (fn-nntp-session-openp session) t)
        (fn-nntp-session-projected session)
        (fn-nntp-command-inputp line)
        (fn-nntp-command-arguments-at-mostp (list *fn-pcr-article-keyword* token))
        (equal (fn-nntp-tokenize line) (list *fn-pcr-article-keyword* token))
        (fn-arena-p fn-arena)
        (and (fn-nntp-message-id-tokenp token) (fn-octet-listp token))
        (consp article)
        server
        (fn-gidx-pinp index)
        (and
          (not (fn-nntp-number-withdrawn-p session archive index token))
          (not (fn-nntp-msgid-withdrawn-p index token)))
        (fn-nntp-response-okp-of-bytes article (fn-nntp-article-bytes article fn-arena) :article)
        (fn-nntp-response-okp-of-bytes article
          (fn-pcr-served-octets server article fn-arena)
          :article))
      (equal
        (fn-nntp-step-pinned session archive index verdicts env (list :command line) fn-arena)
        (fn-pcr-msgid-220-reply session article server fn-arena))))
  :rule-classes
  nil
  :hints
  (("Goal" :use
     ((:instance fn-pcr-msgid-retrieval-answers-220-without-moving-the-cursor
        (trie (fn-gidx-pin-trie index))
        (server (fn-nntp-xref-server env)))
      (:instance fn-nntp-archive-command-pinned-article-head-is-served
        (keyword *fn-pcr-article-keyword*)
        (args (list token))))
     :in-theory
     (e/d
       (fn-rcompat-retrieval-kind fn-nntp-keywordp)
       (fn-nntp-step-pinned fn-nntp-command-pinned fn-nntp-archive-command-pinned
         fn-rcompat-retrieval
         fn-gidx-pinp
         fn-nntp-xref-server
         fn-pcr-msgid-220-reply
         fn-nntp-number-tokenp
         fn-nntp-response-okp-of-bytes
         fn-nntp-article-bytes
         fn-pcr-served-octets)))))

(defthm fn-pcr-msgid-220-is-a-reply-without-an-offer-by-definition
  (let
    ((r (fn-pcr-msgid-220-reply session article server fn-arena)))
    (and
      (true-listp (fn-nntp-result-effects r))
      (not (fn-post-offeredp (fn-nntp-result-effects r)))))
  :hints
  (("Goal" :in-theory
     (e/d
       (fn-pcr-msgid-220-reply fn-post-offeredp fn-nntp-reply-effect fn-nntp-begin-article-effect)
       (fn-nntp-retrieval-initial fn-nntp-crlf fn-nntp-stuff-lines fn-nntp-crlf-lines
         fn-pcr-served-octets
         fn-nntp-set-cursor
         fn-nntp-make-result)))))

(defthm fn-pcr-post-article-has-the-message-id-reply
  (let*
    ((session (fn-post-session-base ps))
     (env (fn-post-reader-env config observation))
     (article (fn-midx-lookup (fn-nntp-token-string token) (fn-gidx-pin-trie index)))
     (server (fn-nntp-xref-server env))
     (r (fn-pcr-msgid-220-reply session article server fn-arena))
     (p
       (fn-nntp-post-step-pinned ps archive index verdicts config observation injection
         (list :command line)
         fn-arena)))
    (implies
      (and
        (fn-post-sessionp ps)
        (not (fn-post-session-awaiting ps))
        (fn-nntp-sessionp session)
        (equal (fn-nntp-session-openp session) t)
        (fn-nntp-session-projected session)
        (fn-nntp-command-inputp line)
        (fn-nntp-command-arguments-at-mostp (list *fn-pcr-article-keyword* token))
        (equal (fn-nntp-tokenize line) (list *fn-pcr-article-keyword* token))
        (fn-arena-p fn-arena)
        (and (fn-nntp-message-id-tokenp token) (fn-octet-listp token))
        (consp article)
        server
        (fn-gidx-pinp index)
        (and
          (not (fn-nntp-number-withdrawn-p session archive index token))
          (not (fn-nntp-msgid-withdrawn-p index token)))
        (fn-nntp-response-okp-of-bytes article (fn-nntp-article-bytes article fn-arena) :article)
        (fn-nntp-response-okp-of-bytes article
          (fn-pcr-served-octets server article fn-arena)
          :article))
      (and
        (equal (fn-post-result-effects p) (fn-nntp-result-effects r))
        (null (fn-post-result-submission p))
        (equal (fn-post-session-base (fn-post-result-session p)) (fn-nntp-result-session r)))))
  :rule-classes
  nil
  :hints
  (("Goal" :use
     ((:instance fn-pcr-command-line-answers-the-message-id-article
        (session (fn-post-session-base ps))
        (env (fn-post-reader-env config observation)))
      (:instance fn-pcr-post-delegates-a-read-without-offer-by-definition
        (event (list :command line)))
      (:instance fn-pcr-msgid-220-is-a-reply-without-an-offer-by-definition
        (session (fn-post-session-base ps))
        (article (fn-midx-lookup (fn-nntp-token-string token) (fn-gidx-pin-trie index)))
        (server (fn-nntp-xref-server (fn-post-reader-env config observation)))))
     :in-theory
     (theory (quote minimal-theory)))))

(defthm fn-pcr-peer-article-has-the-message-id-reply
  (let*
    ((ps (fn-peer-session-base peer))
     (session (fn-post-session-base ps))
     (env (fn-post-reader-env config observation))
     (article (fn-midx-lookup (fn-nntp-token-string token) (fn-gidx-pin-trie index)))
     (server (fn-nntp-xref-server env))
     (r (fn-pcr-msgid-220-reply session article server fn-arena))
     (p
       (fn-peer-step-pinned peer archive index verdicts config observation injection
         (list :command line)
         fn-arena)))
    (implies
      (and
        (fn-peer-sessionp peer)
        (null (fn-peer-session-peer peer))
        (fn-post-sessionp ps)
        (not (fn-post-session-awaiting ps))
        (fn-nntp-sessionp session)
        (equal (fn-nntp-session-openp session) t)
        (fn-nntp-session-projected session)
        (fn-nntp-command-inputp line)
        (fn-nntp-command-arguments-at-mostp (list *fn-pcr-article-keyword* token))
        (equal (fn-nntp-tokenize line) (list *fn-pcr-article-keyword* token))
        (fn-arena-p fn-arena)
        (and (fn-nntp-message-id-tokenp token) (fn-octet-listp token))
        (consp article)
        server
        (fn-gidx-pinp index)
        (and
          (not (fn-nntp-number-withdrawn-p session archive index token))
          (not (fn-nntp-msgid-withdrawn-p index token)))
        (fn-nntp-response-okp-of-bytes article (fn-nntp-article-bytes article fn-arena) :article)
        (fn-nntp-response-okp-of-bytes article
          (fn-pcr-served-octets server article fn-arena)
          :article))
      (and
        (equal (fn-post-result-effects p) (fn-nntp-result-effects r))
        (null (fn-post-result-submission p))
        (equal
          (fn-post-session-base (fn-peer-session-base (fn-post-result-session p)))
          (fn-nntp-result-session r)))))
  :rule-classes
  nil
  :hints
  (("Goal" :use
     ((:instance fn-pcr-post-article-has-the-message-id-reply (ps (fn-peer-session-base peer)))
      (:instance fn-pcr-peer-reader-delegates-to-post-by-definition
        (ps peer)
        (event (list :command line))))
     :in-theory
     (theory (quote minimal-theory)))))

(defthm fn-pcr-auth-article-has-the-message-id-reply
  (let*
    ((peer (fn-auth-view-session as config))
     (viewarchive (fn-auth-view-archive as config archive))
     (viewindex (fn-auth-view-index as config archive index))
     (viewconfig (fn-auth-view-config as (fn-auth-moderation-config as config) archive))
     (ps (fn-peer-session-base peer))
     (session (fn-post-session-base ps))
     (env (fn-post-reader-env viewconfig observation))
     (article (fn-midx-lookup (fn-nntp-token-string token) (fn-gidx-pin-trie viewindex)))
     (server (fn-nntp-xref-server env))
     (r (fn-pcr-msgid-220-reply session article server fn-arena))
     (p
       (fn-auth-step-pinned as archive index verdicts config observation injection
         (list :command line)
         fn-arena)))
    (implies
      (and
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
        (fn-nntp-command-arguments-at-mostp (list *fn-pcr-article-keyword* token))
        (equal (fn-nntp-tokenize line) (list *fn-pcr-article-keyword* token))
        (fn-arena-p fn-arena)
        (and (fn-nntp-message-id-tokenp token) (fn-octet-listp token))
        (consp article)
        server
        (fn-gidx-pinp viewindex)
        (and
          (not (fn-nntp-number-withdrawn-p session viewarchive viewindex token))
          (not (fn-nntp-msgid-withdrawn-p viewindex token)))
        (fn-nntp-response-okp-of-bytes article (fn-nntp-article-bytes article fn-arena) :article)
        (fn-nntp-response-okp-of-bytes article
          (fn-pcr-served-octets server article fn-arena)
          :article))
      (and
        (equal (fn-post-result-effects p) (fn-nntp-result-effects r))
        (null (fn-post-result-submission p))
        (equal
          (fn-post-session-base
            (fn-peer-session-base (fn-auth-session-base (fn-post-result-session p))))
          (fn-nntp-result-session r)))))
  :rule-classes
  nil
  :hints
  (("Goal" :use
     ((:instance fn-pcr-peer-article-has-the-message-id-reply
        (peer (fn-auth-view-session as config))
        (archive (fn-auth-view-archive as config archive))
        (index (fn-auth-view-index as config archive index))
        (config (fn-auth-view-config as (fn-auth-moderation-config as config) archive)))
      fn-pcr-auth-reader-delegates-an-authorized-article-by-definition)
     :in-theory
     (theory (quote minimal-theory)))))

(defthm fn-pcr-served-dispatch-has-the-message-id-reply
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
     (article (fn-midx-lookup (fn-nntp-token-string token) (fn-gidx-pin-trie viewindex)))
     (server (fn-nntp-xref-server env))
     (r (fn-pcr-msgid-220-reply session article server fn-arena))
     (p (fn-served-dispatch conn (list :command line) fn-arena)))
    (implies
      (and
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
        (fn-nntp-command-arguments-at-mostp (list *fn-pcr-article-keyword* token))
        (equal (fn-nntp-tokenize line) (list *fn-pcr-article-keyword* token))
        (fn-arena-p fn-arena)
        (and (fn-nntp-message-id-tokenp token) (fn-octet-listp token))
        (consp article)
        server
        (fn-gidx-pinp viewindex)
        (and
          (not (fn-nntp-number-withdrawn-p session viewarchive viewindex token))
          (not (fn-nntp-msgid-withdrawn-p viewindex token)))
        (fn-nntp-response-okp-of-bytes article (fn-nntp-article-bytes article fn-arena) :article)
        (fn-nntp-response-okp-of-bytes article
          (fn-pcr-served-octets server article fn-arena)
          :article))
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
  (("Goal" :use
     ((:instance fn-pcr-auth-article-has-the-message-id-reply
        (as (fn-served-conn-session conn))
        (config (fn-served-conn-config conn))
        (archive (fn-served-conn-archive conn))
        (index (fn-served-conn-pinned-index conn))
        (verdicts (fn-served-conn-verdicts conn))
        (observation (fn-served-conn-observation conn))
        (injection (fn-served-conn-injection conn)))
      fn-pcr-served-reader-dispatch-is-the-auth-answer-by-definition
      (:instance fn-pcr-msgid-220-is-a-reply-without-an-offer-by-definition
        (session
          (fn-post-session-base
            (fn-peer-session-base
              (fn-auth-view-session (fn-served-conn-session conn) (fn-served-conn-config conn)))))
        (article
          (fn-midx-lookup
            (fn-nntp-token-string token)
            (fn-gidx-pin-trie
              (fn-auth-view-index
                (fn-served-conn-session conn)
                (fn-served-conn-config conn)
                (fn-served-conn-archive conn)
                (fn-served-conn-pinned-index conn)))))
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
     (theory (quote minimal-theory)))))

(local
  (defthm fn-pcr-true-list-fix-identity
    (implies (true-listp xs) (equal (true-list-fix xs) xs))
    :hints
    (("Goal" :induct (true-list-fix xs) :in-theory (enable true-list-fix)))))

(defthm fn-pcr-served-step-answers-the-message-id-article
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
     (article (fn-midx-lookup (fn-nntp-token-string token) (fn-gidx-pin-trie viewindex)))
     (server (fn-nntp-xref-server env))
     (r (fn-pcr-msgid-220-reply session article server fn-arena))
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
        (fn-nntp-command-arguments-at-mostp (list *fn-pcr-article-keyword* token))
        (equal (fn-nntp-tokenize line) (list *fn-pcr-article-keyword* token))
        (fn-arena-p fn-arena)
        (and (fn-nntp-message-id-tokenp token) (fn-octet-listp token))
        (consp article)
        server
        (fn-gidx-pinp viewindex)
        (and
          (not (fn-nntp-number-withdrawn-p session viewarchive viewindex token))
          (not (fn-nntp-msgid-withdrawn-p viewindex token)))
        (fn-nntp-response-okp-of-bytes article (fn-nntp-article-bytes article fn-arena) :article)
        (fn-nntp-response-okp-of-bytes article
          (fn-pcr-served-octets server article fn-arena)
          :article))
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
  (("Goal" :use
     (fn-pcr-served-dispatch-has-the-message-id-reply
       (:instance fn-pcr-command-line-feed-reaches-its-dispatch)
       fn-pcr-article-dispatch-keeps-the-command-wire-by-definition
       (:instance fn-pcr-auth-article-has-the-message-id-reply
         (as (fn-served-conn-session conn))
         (config (fn-served-conn-config conn))
         (archive (fn-served-conn-archive conn))
         (index (fn-served-conn-pinned-index conn))
         (observation (fn-served-conn-observation conn))
         (verdicts (fn-served-conn-verdicts conn))
         (injection (fn-served-conn-injection conn)))
       (:instance fn-pcr-msgid-220-is-a-reply-without-an-offer-by-definition
         (session
           (fn-post-session-base
             (fn-peer-session-base
               (fn-auth-view-session (fn-served-conn-session conn) (fn-served-conn-config conn)))))
         (article
           (fn-midx-lookup
             (fn-nntp-token-string token)
             (fn-gidx-pin-trie
               (fn-auth-view-index
                 (fn-served-conn-session conn)
                 (fn-served-conn-config conn)
                 (fn-served-conn-archive conn)
                 (fn-served-conn-pinned-index conn)))))
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
         (fn-served-step fn-served-closed-wirep fn-served-conn-with-wire-of-own-wire
           fn-served-conn-fields-of-with-wire
           fn-served-result-effects-of-fn-served-make-result
           fn-served-result-conn-of-fn-served-make-result
           fn-wire-state-mode-of-fn-wire-make-state
           fn-lgt-append-nil
           fn-pcr-true-list-fix-identity
           car-cons
           cdr-cons))
       (theory (quote minimal-theory))))))

(local
  (defthm fn-pcr-take-full-list
    (equal (take (len xs) xs) (true-list-fix xs))
    :hints
    (("Goal" :induct (len xs) :in-theory (enable take true-list-fix)))))

(local
  (defthm fn-pcr-take-physical-line
    (equal (take (+ 2 (len line)) (append line (quote (13 10)))) (append line (quote (13 10))))
    :hints
    (("Goal" :use
       ((:instance fn-pcr-take-full-list (xs (append line (quote (13 10))))))
       :in-theory
       (e/d (len binary-append true-list-fix) (fn-pcr-take-full-list))))))

(local
  (defthm fn-pcr-tls-served-wire-by-definition
    (equal (fn-served-conn-wire (fn-own-tls-served-conn o conn)) (fn-own-conn-wire conn))
    :hints
    (("Goal" :in-theory (enable fn-own-tls-served-conn fn-own-served-conn)))))

(defthm
  fn-pcr-host-called-read-answers-the-message-id-article
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
      (article (fn-midx-lookup (fn-nntp-token-string token) (fn-gidx-pin-trie viewindex)))
      (server (fn-nntp-xref-server env))
      (r (fn-pcr-msgid-220-reply session article server fn-arena))
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
        (fn-served-conn-shapep sc)
        (equal
          (fn-served-conn-wire sc)
          (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit))
        (fn-wire-statep (fn-served-conn-wire sc))
        (fn-wire-line-contentp line)
        (natp line-limit)
        (<= (len line) line-limit)
        (not (fn-served-haltedp sc))
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
        (fn-nntp-command-arguments-at-mostp (list *fn-pcr-article-keyword* token))
        (equal (fn-nntp-tokenize line) (list *fn-pcr-article-keyword* token))
        (fn-arena-p fn-arena)
        (and (fn-nntp-message-id-tokenp token) (fn-octet-listp token))
        (consp article)
        server
        (fn-gidx-pinp viewindex)
        (and
          (not (fn-nntp-number-withdrawn-p session viewarchive viewindex token))
          (not (fn-nntp-msgid-withdrawn-p viewindex token)))
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
     (fn-pcr-mca-is-the-counted-configured-read-by-definition
       (:instance
         fn-pcr-configured-reader-counted-answer-by-definition
         (octets (append line (quote (13 10)))))
       (:instance
         fn-pcr-command-line-counted-step-consumes-the-physical-line
         (conn
           (fn-own-tls-served-conn
             (fn-ocfg-owner oc)
             (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))))
       (:instance
         fn-served-step-counted-fast-is-reference
         (conn
           (fn-own-tls-served-conn
             (fn-ocfg-owner oc)
             (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
         (octets (append line (quote (13 10)))))
       (:instance
         fn-served-step-counted-result-is-step-of-consumed-prefix
         (conn
           (fn-own-tls-served-conn
             (fn-ocfg-owner oc)
             (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
         (octets (append line (quote (13 10)))))
       (:instance
         fn-pcr-served-step-answers-the-message-id-article
         (conn
           (fn-own-tls-served-conn
             (fn-ocfg-owner oc)
             (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))))
       (:instance fn-pcr-served-read-is-the-reference-read)
       fn-otb-a-late-page-is-unavailable-never-absent
       (:instance
         fn-pcr-expanded-message-id-220-is-the-raw-reply
         (effects
           (fn-own-tls-result-effects
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
         (session
           (fn-post-session-base
             (fn-peer-session-base
               (fn-auth-view-session
                 (fn-served-conn-session
                   (fn-own-tls-served-conn
                     (fn-ocfg-owner oc)
                     (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
                 (fn-served-conn-config
                   (fn-own-tls-served-conn
                     (fn-ocfg-owner oc)
                     (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))))))
         (article
           (fn-midx-lookup
             (fn-nntp-token-string token)
             (fn-gidx-pin-trie
               (fn-auth-view-index
                 (fn-served-conn-session
                   (fn-own-tls-served-conn
                     (fn-ocfg-owner oc)
                     (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
                 (fn-served-conn-config
                   (fn-own-tls-served-conn
                     (fn-ocfg-owner oc)
                     (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
                 (fn-served-conn-archive
                   (fn-own-tls-served-conn
                     (fn-ocfg-owner oc)
                     (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
                 (fn-served-conn-pinned-index
                   (fn-own-tls-served-conn
                     (fn-ocfg-owner oc)
                     (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))))))
         (server
           (fn-nntp-xref-server
             (fn-post-reader-env
               (fn-auth-view-config
                 (fn-served-conn-session
                   (fn-own-tls-served-conn
                     (fn-ocfg-owner oc)
                     (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
                 (fn-auth-moderation-config
                   (fn-served-conn-session
                     (fn-own-tls-served-conn
                       (fn-ocfg-owner oc)
                       (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
                   (fn-served-conn-config
                     (fn-own-tls-served-conn
                       (fn-ocfg-owner oc)
                       (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))))
                 (fn-served-conn-archive
                   (fn-own-tls-served-conn
                     (fn-ocfg-owner oc)
                     (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))))
               (fn-served-conn-observation
                 (fn-own-tls-served-conn
                   (fn-ocfg-owner oc)
                   (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))))))
         (fn-arena fn-arena)))
     :in-theory
     (union-theories
       (quote (fn-pcr-take-physical-line fn-pcr-tls-served-wire-by-definition))
       (theory (quote minimal-theory))))))

(local
  (defthm fn-pcr-valid-peer-has-valid-post
    (implies (fn-peer-sessionp peer) (fn-post-sessionp (fn-peer-session-base peer)))
    :hints
    (("Goal" :in-theory (e/d (fn-peer-sessionp) (fn-post-sessionp))))))

(local
  (defthm fn-pcr-valid-post-has-valid-reader
    (implies (fn-post-sessionp ps) (fn-nntp-sessionp (fn-post-session-base ps)))
    :hints
    (("Goal" :in-theory (e/d (fn-post-sessionp) (fn-nntp-sessionp))))))

(local
  (defthm fn-pcr-auth-view-is-a-valid-reader-stack
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
  (defthm fn-pcr-tls-served-conn-has-shape
    (fn-served-conn-shapep (fn-own-tls-served-conn o conn))
    :hints
    (("Goal" :in-theory
       (enable fn-own-tls-served-conn fn-own-served-conn fn-served-make-conn-live
         fn-served-conn-shapep)))))

(local
  (defthm fn-pcr-command-wire-limit-is-natural
    (implies
      (fn-wire-statep (fn-wire-make-state :command nil 0 nil nil 0 line-limit body-limit))
      (natp line-limit))
    :hints
    (("Goal" :in-theory (enable fn-wire-statep)))))

(local
  (defthm fn-pcr-open-nonhandshaking-view-is-not-halted
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
  (defthm fn-pcr-command-syntax-is-plain-line
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
  (defthm fn-pcr-command-input-is-plain-line
    (implies (fn-nntp-command-inputp line) (fn-wire-line-contentp line))
    :hints
    (("Goal" :use fn-pcr-command-syntax-is-plain-line :in-theory
       (union-theories (quote (fn-nntp-command-inputp)) (theory (quote minimal-theory)))))))

(defthm
  fn-pcr-host-called-read-produces-the-message-id-article
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
      (article (fn-midx-lookup (fn-nntp-token-string token) (fn-gidx-pin-trie viewindex)))
      (server (fn-nntp-xref-server env))
      (r (fn-pcr-msgid-220-reply session article server fn-arena))
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
        (equal (fn-nntp-tokenize line) (list *fn-pcr-article-keyword* token))
        (fn-nntp-message-id-tokenp token)
        (consp article)
        server
        (fn-gidx-pinp viewindex)
        (and
          (not (fn-nntp-number-withdrawn-p session viewarchive viewindex token))
          (not (fn-nntp-msgid-withdrawn-p viewindex token)))
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
     (fn-pcr-host-called-read-answers-the-message-id-article
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
       fn-scol-okp-arena-p
       fn-pcr-command-slice-has-natural-bounds
       fn-pcr-article-token-fits-command-argument
       (:instance
         fn-pcr-authenticated-reader-has-an-owner-connection
         (o (fn-ocfg-owner oc))
         (conn (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))
       fn-pcr-message-id-token-is-octets)
     :in-theory
     (theory (quote minimal-theory)))))

; Keep the logical response constructor closed outside this proof book.
(in-theory (disable fn-pcr-msgid-220-reply))
