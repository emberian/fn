; fn: the served reader's compatibility arms (PRF-243, NNT-052; lane
; reader-compat, 2026-09-27; packets PKT-665 to PKT-668 of lane
; reader-clients-2, measured with slrn 1.0.3 and pan 0.162).
;
; books/nntp.lisp `fn-nntp-archive-command-pinned' asks `fn-rcompat-reply'
; after the withdrawn arms, on the served path only: every arm requires the
; environment's server name (`fn-nntp-xref-server'), which the served
; environment always carries (the node's path-identity, or the `.invalid'
; agent; books/owner-xref-read.lisp).  A blind environment is answered as
; before (`fn-rcompat-reply-without-a-server').
;
;   NEWGROUPS (RFC 3977 section 7.3) and LIST ACTIVE.TIMES (RFC 6048
;     section 2.3, RFC 2980 section 2.1.3): the generic responses over the
;     environment's creation facts HELD by the served view: a fact is listed
;     only when its group is a group of the view (`fn-state-groups'), so a
;     retired group, and a group a restricted view (lane group-access)
;     excludes, is never named.  The facts come from the configuration
;     records that created the groups (books/owner-agent.lisp
;     `fn-oag-group-facts', PKT-665).
;   LIST SUBSCRIPTIONS [wildmat] (RFC 6048 section 2.6; PKT-666, decided by
;     the coordinator 2026-09-27): 215 and the operator's configured default
;     list (books/config.lisp `fn-cfg-default-subscriptions', code 25) cut to
;     the view's groups, in the configured order; with none configured, the
;     view's groups.  Never a group the view does not hold (section 2.6.2:
;     "SHOULD contain only newsgroups the news server carries").
;   ARTICLE and HEAD (RFC 3977 sections 6.2.1, 6.2.2; PKT-668): of an
;     article this node numbers, the served representation carries this
;     node's Xref field (RFC 5536 section 3.2.14), the one OVER carries, as
;     the last line of the header block.  It is generated like
;     Injection-Info's path-identity, outside the authored source: the
;     stored octets and the article's identity are unchanged (D25; the
;     signed source excludes Xref, specs/nntp.md).  BODY and STAT are
;     unchanged.
;   HDR and XHDR Xref (RFC 3977 section 8.5, RFC 2980 section 2.6;
;     PKT-668): the value of that same field.
;
; The OVERVIEW.FMT arm (PKT-667) is books/nntp-xref.lisp's: its sixth and
; seventh lines are RFC 3977 section 8.4.2's compatibility form "Bytes:" and
; "Lines:".
;
; Keystones (subjects are the functions the dispatcher calls):
;   fn-rcompat-newgroups-names-member          a name is listed exactly when
;                                              the view holds its group and
;                                              a fact dates it at or after
;                                              the threshold
;   fn-rcompat-subscription-names-member       a listed name is a view group,
;                                              and exactly the configured ones
;                                              the view holds when configured
;   fn-rcompat-served-payload-inserts-one-line the served ARTICLE/HEAD octets
;                                              are the stored octets with the
;                                              Xref line inserted before the
;                                              header/body separator, and
;                                              nothing else changed
;   fn-rcompat-hdr-value-is-the-field-value    HDR Xref answers the value of
;                                              the field OVER and HEAD carry

(in-package "ACL2")
(include-book "nntp-xref")

; -----------------------------------------------------------------------------
; NEWGROUPS and LIST ACTIVE.TIMES over the facts the view holds

; The facts whose group is one of GROUPS.
(defun fn-rcompat-facts-held (groups facts)
  (declare (xargs :guard t))
  (if (consp facts)
      (if (and (consp (car facts)) (consp (cdr (car facts)))
               (member-equal (cadr (car facts)) (true-list-fix groups)))
          (cons (car facts) (fn-rcompat-facts-held groups (cdr facts)))
        (fn-rcompat-facts-held groups (cdr facts)))
    nil))

(defun fn-rcompat-held-env (env groups)
  (declare (xargs :guard t))
  (fn-nntp-env-full (fn-nntp-env-observation env)
                    (fn-rcompat-facts-held groups (fn-nntp-env-facts env))
                    (fn-nntp-env-posting env)
                    (fn-nntp-env-listing env)
                    (fn-nntp-env-closed env)))

(defun fn-rcompat-newgroups (session archive env args)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-newgroups-response
   session archive (fn-rcompat-held-env env (fn-state-groups archive)) args))

(defun fn-rcompat-active-times (session archive env args)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-list-active-times
   session (fn-rcompat-held-env env (fn-state-groups archive)) args))

; The names NEWGROUPS lists for THRESHOLD, and when a name is among them.
(defun fn-rcompat-newgroups-names (threshold groups facts)
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-fact-names
   (fn-nntp-facts-since threshold (fn-rcompat-facts-held groups facts))))

(defun fn-rcompat-created-since-p (name threshold facts)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp facts)
      (or (and (fn-nntp-group-factp (car facts))
               (equal (fn-nntp-fact-name (car facts)) name)
               (<= threshold (fn-nntp-fact-created (car facts))))
          (fn-rcompat-created-since-p name threshold (cdr facts)))
    nil))

(local
 (defthm fn-rcompat-names-since-member
   (iff (member-equal name (fn-nntp-fact-names
                            (fn-nntp-facts-since threshold facts)))
        (fn-rcompat-created-since-p name threshold facts))
   :hints (("Goal" :in-theory (enable fn-nntp-fact-names fn-nntp-facts-since
                                      fn-ng-less-equal-is-less-equal)))))

(local
 (defthm fn-rcompat-created-since-held
   (iff (fn-rcompat-created-since-p name threshold
                                    (fn-rcompat-facts-held groups facts))
        (and (member-equal name (true-list-fix groups))
             (fn-rcompat-created-since-p name threshold facts)))
   :hints (("Goal" :induct (fn-rcompat-facts-held groups facts)
            :in-theory (enable fn-nntp-fact-name fn-nntp-group-factp)))))

(defthm fn-rcompat-newgroups-names-member
  (iff (member-equal name (fn-rcompat-newgroups-names threshold groups facts))
       (and (member-equal name (true-list-fix groups))
            (fn-rcompat-created-since-p name threshold facts))))

; The served NEWGROUPS reply is the generic reply's multi-line form over
; exactly those names (RFC 3977 section 7.3.2: LIST ACTIVE's format).
(defthm fn-rcompat-newgroups-unfolds
  (equal (fn-rcompat-newgroups session archive env args)
         (fn-nntp-newgroups-response
          session archive (fn-rcompat-held-env env (fn-state-groups archive))
          args)))

(defthm fn-rcompat-held-env-facts
  (equal (fn-nntp-env-facts (fn-rcompat-held-env env groups))
         (fn-rcompat-facts-held groups (fn-nntp-env-facts env)))
  :hints (("Goal" :in-theory (enable fn-nntp-env-full fn-nntp-env-facts))))

(defthm fn-rcompat-held-env-observation
  (equal (fn-nntp-env-observation (fn-rcompat-held-env env groups))
         (fn-nntp-env-observation env))
  :hints (("Goal" :in-theory (enable fn-nntp-env-full fn-nntp-env-observation))))

; -----------------------------------------------------------------------------
; LIST SUBSCRIPTIONS

; The sixth element of the reader listing: the configured default list
; (PKT-666), projected by books/owner-agent.lisp `fn-oag-listing'.
(defun fn-nntp-listing-subscriptions (listing)
  (declare (xargs :guard t))
  (if (and (consp listing) (consp (cdr listing)) (consp (cddr listing))
           (consp (cdddr listing)) (consp (cddddr listing))
           (consp (cdr (cddddr listing))))
      (car (cdr (cddddr listing)))
    nil))

(defun fn-rcompat-names-held (groups names)
  (declare (xargs :guard t))
  (if (consp names)
      (if (member-equal (car names) (true-list-fix groups))
          (cons (car names) (fn-rcompat-names-held groups (cdr names)))
        (fn-rcompat-names-held groups (cdr names)))
    nil))

(defun fn-rcompat-subscription-names (configured groups)
  (declare (xargs :guard t))
  (if (consp configured)
      (fn-rcompat-names-held groups configured)
    (true-list-fix groups)))

(local
 (defthm fn-rcompat-names-held-member
   (iff (member-equal name (fn-rcompat-names-held groups names))
        (and (member-equal name (true-list-fix groups))
             (member-equal name names)))))

(defthm fn-rcompat-subscription-names-member
  (iff (member-equal name (fn-rcompat-subscription-names configured groups))
       (and (member-equal name (true-list-fix groups))
            (or (not (consp configured))
                (member-equal name configured)))))

; In the configured order: the served list is the configured list with the
; names the view does not hold removed, and nothing reordered.
(defthm fn-rcompat-subscription-names-keep-the-configured-order
  (implies (consp configured)
           (equal (fn-rcompat-subscription-names configured groups)
                  (fn-rcompat-names-held groups configured))))

(defun fn-rcompat-name-lines (names)
  (declare (xargs :guard t))
  (if (consp names)
      (if (fn-nntp-safe-group-namep (car names))
          (cons (fn-nntp-string-octets (car names))
                (fn-rcompat-name-lines (cdr names)))
        (fn-rcompat-name-lines (cdr names)))
    nil))

(defconst *fn-rcompat-subscriptions-initial*
  "215 list of recommended newsgroups follows")

(defun fn-rcompat-subscriptions (session archive env args)
  (declare (xargs :guard t :verify-guards nil))
  (let ((names (fn-rcompat-subscription-names
                (fn-nntp-listing-subscriptions (fn-nntp-env-listing env))
                (fn-state-groups archive))))
    (if (null args)
        (fn-nntp-multi session *fn-rcompat-subscriptions-initial*
                       (fn-rcompat-name-lines names))
      (if (and (consp args) (null (cdr args)))
          (let ((parsed (fn-wildmat-parse (car args))))
            (if (fn-wildmat-result-okp parsed)
                (fn-nntp-multi session *fn-rcompat-subscriptions-initial*
                               (fn-rcompat-name-lines
                                (fn-nntp-filter-groups-by-wildmat
                                 (fn-wildmat-result-value parsed) names)))
              (fn-nntp-single session "501 syntax error")))
        (fn-nntp-single session "501 syntax error")))))

; -----------------------------------------------------------------------------
; The Xref field of ARTICLE, HEAD, HDR and XHDR

; The field's value: SERVER and the locations, exactly what follows
; "Xref: " in the field OVER renders (`fn-xref-field').
(defun fn-rcompat-xref-value (server article)
  (declare (xargs :guard t :verify-guards nil))
  (append (if (true-listp server) server nil)
          (fn-xref-locations (fn-xref-pairs article))))

(defthmd fn-rcompat-hdr-value-is-the-field-value
  (equal (fn-xref-field server (fn-xref-pairs article))
         (append *fn-xref-name* (fn-rcompat-xref-value server article)))
  :hints (("Goal" :in-theory (enable fn-xref-field))))

; The served payload: the stored octets with the Xref line appended to the
; header block, when the article is numbered here, is not reclaimed (a
; tombstone is answered 423/430 from its stored octets) and its octets split
; into header and body; otherwise the stored octets.
(defun fn-rcompat-served-payload (server article)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((payload (fn-article-payload article))
         (split (fn-nntp-split-article payload)))
    (if (and (consp (fn-xref-pairs article))
             (not (fn-rcl-tombstonep payload))
             (fn-nntp-split-okp split))
        (append (fn-nntp-split-head split)
                (fn-xref-field server (fn-xref-pairs article))
                (list 13 10 13 10)
                (fn-nntp-split-body split))
      payload)))

(local
 (defthm fn-rcompat-split-aux-head-true-listp
   (true-listp (fn-nntp-split-head (fn-nntp-split-article-aux bytes rev)))
   :hints (("Goal" :induct (fn-nntp-split-article-aux bytes rev)
            :in-theory (enable fn-nntp-split-article-aux fn-nntp-split-head)))))

(defthm fn-rcompat-split-head-true-listp
  (true-listp (fn-nntp-split-head (fn-nntp-split-article bytes)))
  :hints (("Goal" :in-theory (enable fn-nntp-split-article)
           :use ((:instance fn-rcompat-split-aux-head-true-listp (rev nil))))))

(defun fn-rcompat-served-article (server article)
  (declare (xargs :guard t :verify-guards nil))
  (fn-make-article (fn-article-msgid article)
                   (fn-rcompat-served-payload server article)
                   (fn-article-groups article)
                   (fn-article-memberships article)
                   (fn-article-pin article)
                   (fn-article-stamp article)))

(local
 (defthm fn-rcompat-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-rcompat-split-aux-reassembles
   (implies (fn-nntp-split-okp (fn-nntp-split-article-aux bytes rev))
            (equal (append (fn-nntp-split-head (fn-nntp-split-article-aux bytes rev))
                           (list 13 10)
                           (fn-nntp-split-body (fn-nntp-split-article-aux bytes rev)))
                   (append (reverse rev) bytes)))
   :hints (("Goal" :induct (fn-nntp-split-article-aux bytes rev)
            :in-theory (enable fn-nntp-split-article-aux fn-nntp-split-okp
                               fn-nntp-split-head fn-nntp-split-body)))))

; KEYSTONE.  Where the Xref line is added, the stored octets are HEAD, CRLF,
; BODY and the served octets are HEAD, the Xref line with its CRLF, CRLF,
; BODY: one line inserted at the end of the header block, nothing else
; changed.  Where it is not, the served octets are the stored ones.
(defthm fn-rcompat-served-payload-inserts-one-line
  (let ((split (fn-nntp-split-article (fn-article-payload article))))
    (if (and (consp (fn-xref-pairs article))
             (not (fn-rcl-tombstonep (fn-article-payload article)))
             (fn-nntp-split-okp split))
        (and (equal (fn-article-payload article)
                    (append (fn-nntp-split-head split) (list 13 10)
                            (fn-nntp-split-body split)))
             (equal (fn-rcompat-served-payload server article)
                    (append (fn-nntp-split-head split)
                            (fn-xref-field server (fn-xref-pairs article))
                            (list 13 10)
                            (list 13 10)
                            (fn-nntp-split-body split))))
      (equal (fn-rcompat-served-payload server article)
             (fn-article-payload article))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-split-article)
                                  (fn-xref-field fn-xref-pairs
                                   fn-rcl-tombstonep))
           :use ((:instance fn-rcompat-split-aux-reassembles
                            (bytes (fn-article-payload article)) (rev nil))))))

(defun fn-rcompat-retrieval-kind (keyword)
  (declare (xargs :guard t))
  (if (fn-nntp-keywordp keyword "ARTICLE") :article :head))

; The reply for one found article: the generic reply over its served
; representation, whose session is the generic reply's over the stored
; octets.  The two sessions agree whenever the served octets frame as the
; stored ones do; where they would not, the stored octets are served, so the
; cursor never depends on the Xref line.
(defun fn-rcompat-article-reply (session article number kind updatep group
                                         server)
  (declare (xargs :guard t :verify-guards nil))
  (let ((stored (fn-nntp-article-response session article number kind
                                          updatep group))
        (served (fn-nntp-article-response
                 session (fn-rcompat-served-article server article)
                 number kind updatep group)))
    (if (equal (fn-nntp-result-session served)
               (fn-nntp-result-session stored))
        served
      stored)))

(defthm fn-rcompat-article-reply-session
  (equal (fn-nntp-result-session
          (fn-rcompat-article-reply session article number kind updatep
                                    group server))
         (fn-nntp-result-session
          (fn-nntp-article-response session article number kind updatep
                                    group))))

; ARTICLE/HEAD with no argument, a number or a Message-ID: the article the
; generic arms find (the scan for the current article and a number, as
; `fn-nntp-current-retrieval' and `fn-nntp-number-retrieval'; the pinned
; trie for a Message-ID, as `fn-nntp-msgid-retrieval-indexed'), answered
; over its served representation.
(defun fn-rcompat-retrieval (session archive trie kind args server)
  (declare (xargs :guard t :verify-guards nil))
  (if (null args)
      (let ((group (fn-nntp-session-group session))
            (current (fn-nntp-session-current session)))
        (if (null group)
            (fn-nntp-single session "412 no newsgroup selected")
          (if (null current)
              (fn-nntp-single session "420 no current article")
            (let ((article (fn-nntp-available-article
                            group current (fn-state-articles archive))))
              (if (consp article)
                  (fn-rcompat-article-reply session article current kind t
                                            group server)
                (fn-nntp-single session "420 no current article"))))))
    (let ((token (and (consp args) (car args))))
      (if (fn-nntp-number-tokenp token)
          (let ((group (fn-nntp-session-group session))
                (number (fn-nntp-decimal-value token)))
            (if (null group)
                (fn-nntp-single session "412 no newsgroup selected")
              (let ((article (fn-nntp-find-group-number
                              group number (fn-state-articles archive))))
                (if (consp article)
                    (fn-rcompat-article-reply session article number kind t
                                              group server)
                  (fn-nntp-single session "423 no article with that number")))))
        (if (not (and (fn-nntp-message-id-tokenp token) (fn-octet-listp token)))
            (fn-nntp-single session "501 syntax error")
          (let ((article (fn-midx-lookup (fn-nntp-token-string token) trie)))
            (if (consp article)
                (fn-rcompat-article-reply
                 session article (fn-nntp-msgid-local-number session article)
                 kind nil nil server)
              (fn-nntp-single session
                              "430 no article with that message-id"))))))))

(defthm fn-rcompat-single-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-single session text)) session)
  :hints (("Goal" :in-theory (enable fn-nntp-single fn-nntp-result-session
                                     fn-nntp-make-result))))

(defthm fn-rcompat-multi-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-multi session initial lines))
         session)
  :hints (("Goal" :in-theory (enable fn-nntp-multi fn-nntp-result-session
                                     fn-nntp-make-result))))

; The session of every served ARTICLE/HEAD is the generic retrieval's: the
; cursor rule of RFC 3977 section 6.2.1 is untouched by the Xref line.
(defthm fn-rcompat-retrieval-session-is-the-generic-session
  (implies (or (null args) (and (consp args) (null (cdr args))))
           (equal (fn-nntp-result-session
                   (fn-rcompat-retrieval session archive trie kind args server))
                  (fn-nntp-result-session
                   (fn-nntp-retrieval session archive kind args))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-retrieval fn-nntp-current-retrieval
                                   fn-nntp-number-retrieval)
                                  (fn-nntp-article-response
                                   fn-nntp-msgid-retrieval
                                   fn-rcompat-article-reply
                                   fn-rcompat-served-article))
           :use ((:instance fn-nntp-msgid-preserves-session (token (car args)))))))

; HDR/XHDR Xref: the value for each article, the generic HDR shape.
(defun fn-rcompat-xref-content (server article)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp article)
           (not (fn-rcl-tombstonep (fn-article-payload article))))
      (list :ok (fn-rcompat-xref-value server article))
    (list :error)))

(defun fn-rcompat-hdr-lines (group numbers articles server)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp numbers)
      (let ((content (fn-rcompat-xref-content
                      server (fn-nntp-available-article group (car numbers)
                                                        articles))))
        (if (fn-nntp-hdr-okp content)
            (cons (fn-nntp-hdr-line (fn-nntp-decimal-field (car numbers))
                                    (fn-nntp-hdr-octets content))
                  (fn-rcompat-hdr-lines group (cdr numbers) articles server))
          (fn-rcompat-hdr-lines group (cdr numbers) articles server)))
    nil))

(defun fn-rcompat-hdr (session archive trie args legacyp server)
  ; ARGS is (FIELD) or (FIELD RANGE-OR-MESSAGE-ID); FIELD is Xref.
  (declare (xargs :guard t :verify-guards nil))
  (let ((rest (and (consp args) (cdr args))))
    (if (null rest)
        (let ((group (fn-nntp-session-group session))
              (current (fn-nntp-session-current session)))
          (if (null group)
              (fn-nntp-single session "412 no newsgroup selected")
            (if (null current)
                (fn-nntp-single session "420 no current article")
              (let ((article (fn-nntp-available-article
                              group current (fn-state-articles archive))))
                (if (not (consp article))
                    (fn-nntp-single session "420 no current article")
                  (let ((content (fn-rcompat-xref-content server article)))
                    (if (fn-nntp-hdr-okp content)
                        (fn-nntp-multi
                         session (fn-nntp-hdr-initial legacyp)
                         (list (fn-nntp-hdr-line
                                (fn-nntp-decimal-field current)
                                (fn-nntp-hdr-octets content))))
                      (fn-nntp-single session "423 article reclaimed"))))))))
      (if (not (and (consp rest) (null (cdr rest))))
          (fn-nntp-single session "501 syntax error")
        (let ((token (car rest)))
          (if (fn-nntp-range-okp (fn-nntp-parse-range token))
              (let ((group (fn-nntp-session-group session))
                    (range (fn-nntp-parse-range token)))
                (if (null group)
                    (fn-nntp-single session "412 no newsgroup selected")
                  (let ((lines (fn-rcompat-hdr-lines
                                group
                                (fn-nntp-group-range-numbers
                                 group (fn-nntp-range-low range)
                                 (fn-nntp-range-high range)
                                 (fn-state-articles archive))
                                (fn-state-articles archive) server)))
                    (if (consp lines)
                        (fn-nntp-multi session (fn-nntp-hdr-initial legacyp)
                                       lines)
                      (fn-nntp-single session
                                      (if legacyp "420 no article(s) selected"
                                        "423 no articles in that range"))))))
            (if (not (and (fn-nntp-message-id-tokenp token)
                          (fn-octet-listp token)))
                (fn-nntp-single session "501 syntax error")
              (let* ((article (fn-midx-lookup (fn-nntp-token-string token) trie))
                     (content (fn-rcompat-xref-content server article)))
                (if (not (consp article))
                    (fn-nntp-single session "430 no article with that message-id")
                  (if (fn-nntp-hdr-okp content)
                      (fn-nntp-multi
                       session (fn-nntp-hdr-initial legacyp)
                       (list (fn-nntp-hdr-line
                              (if legacyp (fn-nov-scrub token)
                                (fn-nntp-decimal-field 0))
                              (fn-nntp-hdr-octets content))))
                    (fn-nntp-single session "430 article reclaimed")))))))))))

; -----------------------------------------------------------------------------
; The dispatcher's call

(defun fn-rcompat-list-keywordp (args keyword)
  (declare (xargs :guard t))
  (and (consp args)
       (fn-nntp-keyword-tokenp (car args))
       (fn-nntp-keywordp (car args) keyword)))

(defun fn-rcompat-reply (session archive index env keyword args)
  (declare (xargs :guard t :verify-guards nil))
  (let ((server (fn-nntp-xref-server env)))
    (cond
     ((not server) nil)
     ((fn-nntp-keywordp keyword "NEWGROUPS")
      (fn-rcompat-newgroups session archive env args))
     ((and (fn-nntp-keywordp keyword "LIST")
           (fn-rcompat-list-keywordp args "ACTIVE.TIMES"))
      (fn-rcompat-active-times session archive env (cdr args)))
     ((and (fn-nntp-keywordp keyword "LIST")
           (fn-rcompat-list-keywordp args "SUBSCRIPTIONS"))
      (fn-rcompat-subscriptions session archive env (cdr args)))
     ((and (or (fn-nntp-keywordp keyword "ARTICLE")
               (fn-nntp-keywordp keyword "HEAD"))
           (fn-gidx-pinp index)
           (or (null args) (and (consp args) (null (cdr args)))))
      (fn-rcompat-retrieval session archive (fn-gidx-pin-trie index)
                            (fn-rcompat-retrieval-kind keyword) args server))
     ((and (or (fn-nntp-keywordp keyword "HDR")
               (fn-nntp-keywordp keyword "XHDR"))
           (fn-gidx-pinp index)
           (consp args)
           (fn-nntp-keywordp (car args) "XREF"))
      (fn-rcompat-hdr session archive (fn-gidx-pin-trie index) args
                      (fn-nntp-keywordp keyword "XHDR") server))
     (t nil))))

(defthm fn-rcompat-reply-without-a-server
  (implies (not (fn-nntp-xref-server env))
           (not (fn-rcompat-reply session archive index env keyword args))))

(defthm fn-rcompat-reply-only-for-its-commands
  (implies (and (not (fn-nntp-keywordp keyword "NEWGROUPS"))
                (not (fn-nntp-keywordp keyword "LIST"))
                (not (fn-nntp-keywordp keyword "ARTICLE"))
                (not (fn-nntp-keywordp keyword "HEAD"))
                (not (fn-nntp-keywordp keyword "HDR"))
                (not (fn-nntp-keywordp keyword "XHDR")))
           (not (fn-rcompat-reply session archive index env keyword args)))
  :hints (("Goal" :in-theory (disable fn-nntp-keywordp fn-nntp-xref-server))))

; HDR and XHDR reach it only for the Xref field.
(defthm fn-rcompat-reply-hdr-only-for-xref
  (implies (and (not (fn-nntp-keywordp keyword "NEWGROUPS"))
                (not (fn-nntp-keywordp keyword "LIST"))
                (not (fn-nntp-keywordp keyword "ARTICLE"))
                (not (fn-nntp-keywordp keyword "HEAD"))
                (not (and (consp args) (fn-nntp-keywordp (car args) "XREF"))))
           (not (fn-rcompat-reply session archive index env keyword args)))
  :hints (("Goal" :in-theory (disable fn-nntp-keywordp fn-nntp-xref-server))))

(defthm fn-rcompat-reply-list-only-for-its-variants
  (implies (and (fn-nntp-keywordp keyword "LIST")
                (not (fn-rcompat-list-keywordp args "ACTIVE.TIMES"))
                (not (fn-rcompat-list-keywordp args "SUBSCRIPTIONS"))
                (not (fn-nntp-keywordp keyword "NEWGROUPS"))
                (not (fn-nntp-keywordp keyword "ARTICLE"))
                (not (fn-nntp-keywordp keyword "HEAD"))
                (not (fn-nntp-keywordp keyword "HDR"))
                (not (fn-nntp-keywordp keyword "XHDR")))
           (not (fn-rcompat-reply session archive index env keyword args)))
  :hints (("Goal" :in-theory (disable fn-nntp-keywordp fn-nntp-xref-server
                                      fn-rcompat-list-keywordp))))

; The session every arm leaves: the command's own for ARTICLE and HEAD (the
; generic retrieval's), and the given session for every other arm.
(defthmd fn-rcompat-reply-session
  (implies (fn-rcompat-reply session archive index env keyword args)
           (equal (fn-nntp-result-session
                   (fn-rcompat-reply session archive index env keyword args))
                  (if (and (not (fn-nntp-keywordp keyword "NEWGROUPS"))
                           (not (and (fn-nntp-keywordp keyword "LIST")
                                     (fn-rcompat-list-keywordp
                                      args "ACTIVE.TIMES")))
                           (not (and (fn-nntp-keywordp keyword "LIST")
                                     (fn-rcompat-list-keywordp
                                      args "SUBSCRIPTIONS")))
                           (or (fn-nntp-keywordp keyword "ARTICLE")
                               (fn-nntp-keywordp keyword "HEAD"))
                           (fn-gidx-pinp index)
                           (or (null args)
                               (and (consp args) (null (cdr args)))))
                      (fn-nntp-result-session
                       (fn-nntp-retrieval session archive
                                          (fn-rcompat-retrieval-kind keyword)
                                          args))
                    session)))
  :hints (("Goal" :in-theory (e/d (fn-rcompat-newgroups fn-rcompat-active-times
                                   fn-rcompat-subscriptions fn-rcompat-hdr
                                   fn-nntp-newgroups-response
                                   fn-nntp-list-active-times)
                                  (fn-nntp-keywordp fn-nntp-xref-server
                                   fn-rcompat-list-keywordp fn-gidx-pinp
                                   fn-rcompat-retrieval fn-nntp-retrieval
                                   fn-nntp-single fn-nntp-multi)))))

(defthm fn-rcompat-reply-effects-true-listp
  (true-listp (fn-nntp-result-effects
               (fn-rcompat-reply session archive index env keyword args)))
  :hints (("Goal" :in-theory (enable fn-rcompat-newgroups fn-rcompat-active-times
                                     fn-rcompat-subscriptions fn-rcompat-retrieval
                                     fn-rcompat-article-reply fn-rcompat-hdr
                                     fn-nntp-newgroups-response
                                     fn-nntp-list-active-times
                                     fn-nntp-article-response
                                     fn-nntp-single fn-nntp-multi
                                     fn-nntp-make-result fn-nntp-result-effects))))

(verify-guards fn-rcompat-newgroups)
(verify-guards fn-rcompat-active-times)
(verify-guards fn-rcompat-subscriptions)
(verify-guards fn-rcompat-xref-value)
(verify-guards fn-rcompat-served-payload)
(verify-guards fn-rcompat-served-article)
(verify-guards fn-rcompat-article-reply)
(verify-guards fn-rcompat-retrieval)
(verify-guards fn-rcompat-xref-content)
(verify-guards fn-rcompat-hdr-lines)
(verify-guards fn-rcompat-hdr)
(verify-guards fn-rcompat-reply)

(in-theory (disable fn-rcompat-newgroups fn-rcompat-active-times
                    fn-rcompat-subscriptions fn-rcompat-retrieval
                    fn-rcompat-hdr fn-rcompat-reply))
