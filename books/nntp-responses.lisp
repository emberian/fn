; fn NNTP reader session core: per-command response builders.
;
; Split out of books/nntp.lisp (2026-09-19).

(in-package "ACL2")
(include-book "nntp-projection")
; -----------------------------------------------------------------------------
; Command responses

(defun fn-nntp-retrieval-initial (kind number article)
  (fn-nntp-append-pieces
   (list (cond ((equal kind :article) (fn-nntp-string-octets "220 "))
               ((equal kind :head) (fn-nntp-string-octets "221 "))
               ((equal kind :body) (fn-nntp-string-octets "222 "))
               (t (fn-nntp-string-octets "223 ")))
         (fn-nntp-decimal-field number) '(32)
         (fn-nntp-string-octets (fn-article-msgid article))
         (cond ((equal kind :article) (fn-nntp-string-octets " article follows"))
               ((equal kind :head) (fn-nntp-string-octets " headers follow"))
               ((equal kind :body) (fn-nntp-string-octets " body follows"))
               (t (fn-nntp-string-octets " retrieved"))))))
; A stored article that cannot be projected degrades only itself, and it says
; which of the two reasons applies.  RFC 3977 section 3.2.1 assigns 503 to a
; recognized command whose legitimate case the server handles only in part.
; The cursor moves only on a success; every refusal returns `session`.
;
; The first branch is defensive.  fn-nntp-available-article never returns an
; article that fails fn-nntp-article-idp, and a Message-ID retrieval matched the
; stored identifier against a token that is itself at most 250 printable
; octets, so no composed path reaches it; it is not the subject of any theorem.
(defun fn-nntp-article-response (session article number kind updatep group)
  (if (not (fn-nntp-article-idp article))
      (fn-nntp-single session "503 stored article identifier unavailable")
    (let ((next-session (if updatep
                            (fn-nntp-set-cursor session group number)
                          session)))
      (if (equal kind :stat)
          (fn-nntp-make-result
           next-session
           (list (fn-nntp-reply-effect
                  (fn-nntp-crlf (fn-nntp-retrieval-initial kind number article)))))
        (let ((section (fn-nntp-article-section article kind)))
          (if (and (fn-nntp-article-framedp article)
                   (equal (car section) :ok))
              (fn-nntp-make-result
               next-session
               (list (fn-nntp-reply-effect
                      (append (fn-nntp-crlf (fn-nntp-retrieval-initial kind number article))
                              (fn-nntp-stuff-lines (car (cdr section)))
                              '(46 13 10)))))
            (fn-nntp-single session "503 stored article framing unavailable")))))))

(defun fn-nntp-current-retrieval (session archive kind)
  (let ((group (fn-nntp-session-group session))
        (current (fn-nntp-session-current session)))
    (if (null group)
        (fn-nntp-single session "412 no newsgroup selected")
      (if (null current)
          (fn-nntp-single session "420 no current article")
        (let ((article (fn-nntp-available-article group current
                                                  (fn-state-articles archive))))
          (if (consp article)
              (fn-nntp-article-response session article current kind t group)
            (fn-nntp-single session "420 no current article")))))))

(defun fn-nntp-number-retrieval (session archive kind token)
  (if (not (fn-nntp-number-tokenp token))
      (fn-nntp-single session "501 syntax error")
    (let ((group (fn-nntp-session-group session))
          (number (fn-nntp-decimal-value token)))
      (if (null group)
          (fn-nntp-single session "412 no newsgroup selected")
        (let ((article (fn-nntp-find-group-number group number
                                                  (fn-state-articles archive))))
          (if (consp article)
              (fn-nntp-article-response session article number kind t group)
            (fn-nntp-single session "423 no article with that number")))))))

(defun fn-nntp-msgid-retrieval (session archive kind token)
  (if (not (fn-nntp-message-id-tokenp token))
      (fn-nntp-single session "501 syntax error")
    (let ((article (fn-find-article (fn-nntp-token-string token)
                                    (fn-state-articles archive))))
      (if (consp article)
          ; RFC 3977 permits zero for a message-id retrieval.  It deliberately
          ; does not alter either selected group or current article number.
          (fn-nntp-article-response session article 0 kind nil nil)
        (fn-nntp-single session "430 no article with that message-id")))))

(defthm fn-nntp-msgid-preserves-session
  (equal (fn-nntp-result-session
          (fn-nntp-msgid-retrieval session archive kind token))
         session))

(defun fn-nntp-retrieval (session archive kind args)
  (mbe :logic
       (if (null args)
           (fn-nntp-current-retrieval session archive kind)
         (if (null (cdr args))
             (let ((token (car args)))
               (if (fn-nntp-number-tokenp token)
                   (fn-nntp-number-retrieval session archive kind token)
                 (fn-nntp-msgid-retrieval session archive kind token)))
           (fn-nntp-single session "501 syntax error")))
       :exec
       (if (null args)
           (fn-nntp-current-retrieval session archive kind)
         (if (null (fn-ag-cdr args))
             (let ((token (fn-ag-car args)))
               (if (fn-nntp-number-tokenp token)
                   (fn-nntp-number-retrieval session archive kind token)
                 (fn-nntp-msgid-retrieval session archive kind token)))
           (fn-nntp-single session "501 syntax error")))))

(defun fn-nntp-next-or-last (session archive direction)
  (let ((group (fn-nntp-session-group session))
        (current (fn-nntp-session-current session)))
    (if (null group)
        (fn-nntp-single session "412 no newsgroup selected")
      (if (null current)
          (fn-nntp-single session "420 no current article")
        (let ((number (if (equal direction :next)
                          (fn-nntp-group-next-number
                           group current (fn-state-articles archive))
                        (fn-nntp-group-last-number
                         group current (fn-state-articles archive)))))
          (if (posp number)
              (let ((article (fn-nntp-available-article
                              group number (fn-state-articles archive))))
                (fn-nntp-article-response session article number :stat t group))
            (if (equal direction :next)
                (fn-nntp-single session "421 no next article")
              (fn-nntp-single session "422 no previous article"))))))))

(defun fn-nntp-active-line (archive group)
  (let ((summary (fn-nntp-group-summary archive group)))
    (fn-nntp-append-pieces
     (list (fn-nntp-string-octets group) '(32)
           (fn-nntp-decimal-field (fn-nntp-summary-high summary)) '(32)
           (fn-nntp-decimal-field (fn-nntp-summary-low summary))
           (fn-nntp-string-octets " y")))))

(defun fn-nntp-active-lines (archive groups)
  (if (consp groups)
      (cons (fn-nntp-active-line archive (car groups))
            (fn-nntp-active-lines archive (cdr groups)))
    nil))

(defun fn-nntp-newsgroup-lines (groups)
  (if (consp groups)
      (cons (fn-nntp-append-pieces
             (list (fn-nntp-string-octets (car groups))
                   (fn-nntp-string-octets " fn experimental group")))
            (fn-nntp-newsgroup-lines (cdr groups)))
    nil))
; `patterns` is an internal successful `fn-wildmat-parse` result, never an
; externally supplied representation.  Group names are projection-guarded
; printable ASCII and no longer than the local wildmat target cap, so their
; UTF-8 decoding is exact and bounded before the DP match is called.
(defun fn-nntp-group-matches-parsed-wildmatp (patterns group)
  (let ((decoded (fn-wildmat-decode (fn-nntp-string-octets group))))
    (and (fn-wildmat-result-okp decoded)
         (mbe :logic
              (fn-wildmat-match-codepoints patterns
                                           (fn-wildmat-result-value decoded))
              :exec
              (ec-call
               (fn-wildmat-match-codepoints
                patterns (fn-wildmat-result-value decoded)))))))

(defun fn-nntp-filter-groups-by-wildmat (patterns groups)
  (if (consp groups)
      (if (fn-nntp-group-matches-parsed-wildmatp patterns (car groups))
          (cons (car groups)
                (fn-nntp-filter-groups-by-wildmat patterns (cdr groups)))
        (fn-nntp-filter-groups-by-wildmat patterns (cdr groups)))
    nil))

(defun fn-nntp-list-active (session archive groups)
  (fn-nntp-multi session "215 list of active newsgroups follows"
                 (fn-nntp-active-lines archive groups)))

(defun fn-nntp-list-newsgroups (session groups)
  (fn-nntp-multi session "215 list of newsgroups follows"
                 (fn-nntp-newsgroup-lines groups)))

(defun fn-nntp-list-filtered-response (session archive kind wildmat)
  ; Parse once per LIST command, then reuse that parsed value for every group.
  (let ((parsed (fn-wildmat-parse wildmat)))
    (if (fn-wildmat-result-okp parsed)
        (let ((groups (fn-nntp-filter-groups-by-wildmat
                       (fn-wildmat-result-value parsed)
                       (fn-state-groups archive))))
          (if (equal kind :active)
              (fn-nntp-list-active session archive groups)
            (fn-nntp-list-newsgroups session groups)))
      (fn-nntp-single session "501 syntax error"))))

(defun fn-nntp-list-active-or-newsgroups (session archive kind args)
  (if (null args)
      (if (equal kind :active)
          (fn-nntp-list-active session archive (fn-state-groups archive))
        (fn-nntp-list-newsgroups session (fn-state-groups archive)))
    (if (and (consp args) (null (cdr args)))
        (fn-nntp-list-filtered-response session archive kind (car args))
      (fn-nntp-single session "501 syntax error"))))

(defun fn-nntp-list-wildmat-argumentp (args)
  (if (null args)
      t
    (if (and (consp args) (null (cdr args)))
        (fn-wildmat-result-okp (fn-wildmat-parse (car args)))
      nil)))

(defun fn-nntp-list-unmaintained-response (session keyword args)
  ; RFC 3977 sections 7.6.4/7.6.5, 8.4, 8.6, and 9.6 specify these arities.
  ; A syntactically valid request for a recognized but unmaintained item is
  ; 503; an argument forbidden by that item's grammar remains 501.
  (if (fn-nntp-keywordp keyword "ACTIVE.TIMES")
      (if (fn-nntp-list-wildmat-argumentp args)
          (fn-nntp-single session "503 data item not stored")
        (fn-nntp-single session "501 syntax error"))
    (if (fn-nntp-keywordp keyword "DISTRIB.PATS")
        (if (null args)
            (fn-nntp-single session "503 data item not stored")
          (fn-nntp-single session "501 syntax error"))
      (if (fn-nntp-keywordp keyword "OVERVIEW.FMT")
          (if (null args)
              (fn-nntp-single session "503 data item not stored")
            (fn-nntp-single session "501 syntax error"))
        (if (fn-nntp-keywordp keyword "HEADERS")
            (if (or (null args)
                    (and (consp args) (null (cdr args))
                         (or (fn-nntp-keywordp (car args) "MSGID")
                             (fn-nntp-keywordp (car args) "RANGE"))))
                (fn-nntp-single session "503 data item not stored")
              (fn-nntp-single session "501 syntax error"))
          (fn-nntp-single session "501 unsupported LIST variant"))))))

(defun fn-nntp-list-response (session archive args)
  (mbe :logic
       (if (null args)
           (fn-nntp-list-active session archive (fn-state-groups archive))
         (let ((keyword (car args)) (arguments (cdr args)))
           (if (not (fn-nntp-keyword-tokenp keyword))
               (fn-nntp-single session "501 syntax error")
             (if (fn-nntp-keywordp keyword "ACTIVE")
                 (fn-nntp-list-active-or-newsgroups session archive :active arguments)
               (if (fn-nntp-keywordp keyword "NEWSGROUPS")
                   (fn-nntp-list-active-or-newsgroups session archive :newsgroups arguments)
                 (fn-nntp-list-unmaintained-response session keyword arguments))))))
       :exec
       (if (null args)
           (fn-nntp-list-active session archive (fn-state-groups archive))
         (let ((keyword (fn-ag-car args)) (arguments (fn-ag-cdr args)))
           (if (not (fn-nntp-keyword-tokenp keyword))
               (fn-nntp-single session "501 syntax error")
             (if (fn-nntp-keywordp keyword "ACTIVE")
                 (fn-nntp-list-active-or-newsgroups session archive :active arguments)
               (if (fn-nntp-keywordp keyword "NEWSGROUPS")
                   (fn-nntp-list-active-or-newsgroups session archive :newsgroups arguments)
                 (fn-nntp-list-unmaintained-response session keyword arguments))))))))

(defun fn-nntp-capabilities (session)
  ; No READER, POST, TLS, authentication, compression, or cryptographic
  ; capability is advertised: this laboratory implements only selected commands.
  (fn-nntp-multi session "101 capability list follows"
                 (list (fn-nntp-string-octets "VERSION 2")
                       (fn-nntp-string-octets "IMPLEMENTATION fn-nntp-lab"))))

(defun fn-nntp-help (session)
  (fn-nntp-multi session "100 help text follows"
                 (list (fn-nntp-string-octets "CAPABILITIES HEAD HELP QUIT STAT")
                       (fn-nntp-string-octets "GROUP ARTICLE BODY NEXT LAST LIST LISTGROUP"))))

(verify-guards fn-nntp-retrieval-initial)

(verify-guards fn-nntp-article-response)

(verify-guards fn-nntp-current-retrieval)

(verify-guards fn-nntp-number-retrieval)

(verify-guards fn-nntp-msgid-retrieval)

(verify-guards fn-nntp-retrieval)

(verify-guards fn-nntp-next-or-last)

(verify-guards fn-nntp-active-line)

(verify-guards fn-nntp-active-lines)

(verify-guards fn-nntp-newsgroup-lines)

(verify-guards fn-nntp-group-matches-parsed-wildmatp)

(verify-guards fn-nntp-filter-groups-by-wildmat)

(verify-guards fn-nntp-list-active)

(verify-guards fn-nntp-list-newsgroups)

(verify-guards fn-nntp-list-filtered-response)

(verify-guards fn-nntp-list-active-or-newsgroups)

(verify-guards fn-nntp-list-wildmat-argumentp)

(verify-guards fn-nntp-list-unmaintained-response)

(verify-guards fn-nntp-list-response)

(verify-guards fn-nntp-capabilities)

(verify-guards fn-nntp-help)

; ---------------------------------------------------------------------------
; Export theory
;
; The definitions this book adds are proof vocabulary for the books above it,
; not rules an includer should inherit.  They are withdrawn under one name so
; a book that reasons about the transitions re-enables exactly them in one
; line (books/nntp-invariants.lisp does).  Ground evaluation is unaffected:
; only the :definition runes are withdrawn.

(deftheory fn-nntp-responses-vocabulary
  '(fn-nntp-retrieval-initial fn-nntp-article-response 
    fn-nntp-current-retrieval fn-nntp-number-retrieval 
    fn-nntp-msgid-retrieval fn-nntp-retrieval fn-nntp-next-or-last 
    fn-nntp-active-line fn-nntp-active-lines fn-nntp-newsgroup-lines 
    fn-nntp-group-matches-parsed-wildmatp fn-nntp-filter-groups-by-wildmat 
    fn-nntp-list-active fn-nntp-list-newsgroups 
    fn-nntp-list-filtered-response fn-nntp-list-active-or-newsgroups 
    fn-nntp-list-wildmat-argumentp fn-nntp-list-unmaintained-response 
    fn-nntp-list-response fn-nntp-capabilities fn-nntp-help))

(in-theory (disable fn-nntp-responses-vocabulary))
