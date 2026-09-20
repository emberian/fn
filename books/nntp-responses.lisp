; fn NNTP reader session core: per-command response builders.
;
; Split out of books/nntp.lisp (2026-09-19).

(in-package "ACL2")
(include-book "nntp-projection")
(include-book "article-fields")
(include-book "clock")

; The books below this one withdraw their definitions at their export events
; (2026-09-19 split of books/nntp.lisp).  This book is the continuation of
; that single file, so it re-enables exactly them, locally: within the
; chain the theory is the one the original file had at this point.
(local (in-theory (enable fn-nntp-syntax-vocabulary
                          fn-nntp-session-vocabulary
                          fn-nntp-projection-vocabulary)))
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
  ; RFC 3977 section 7.6.6: the group name, one or more space or TAB (the
  ; usual practice is a single TAB), then a short description.  fn's
  ; configuration carries no description for a group -- the group table holds
  ; names, policy ids and created/retired stamps only -- so the second field
  ; is the fixed marker "(no description)", identical for every group.  That
  ; fabricates nothing about any group: it is a statement about the server.
  ;
  ; The field is NOT empty, and that is a measured decision.  A bare
  ; "name TAB" line is what section 7.6.6 permits, but Python nntplib strips
  ; the line and then requires name + white space + text, so an empty
  ; description makes the group VANISH from its descriptions() result rather
  ; than appear with no text (measured against tests/interop_nntplib.py,
  ; 2026-09-20).  See the LIST NEWSGROUPS row of specs/nntp-audit.md.
  (if (consp groups)
      (cons (fn-nntp-append-pieces
             (list (fn-nntp-string-octets (car groups)) (list 9)
                   (fn-nntp-string-octets "(no description)")))
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

; -----------------------------------------------------------------------------
; LIST OVERVIEW.FMT (RFC 3977 section 8.4).  Defined here because
; fn-nntp-list-unmaintained-response below answers LIST OVERVIEW.FMT
; with it.

(defconst *fn-nov-fmt-lines*
  '("Subject:" "From:" "Date:" "Message-ID:" "References:" ":bytes" ":lines"))

(defun fn-nov-fmt-octet-lines (texts)
  (if (consp texts)
      (cons (fn-nntp-string-octets (car texts))
            (fn-nov-fmt-octet-lines (cdr texts)))
    nil))

(defun fn-nntp-list-overview-fmt (session)
  (fn-nntp-multi-octets
   session (fn-nntp-string-octets "215 order of fields in overview database")
   (fn-nov-fmt-octet-lines *fn-nov-fmt-lines*)))

; LIST HEADERS (RFC 3977 section 8.6).  HDR below retrieves ANY header of the
; parsed article view, so section 8.6.2 requires the single-colon entry and
; forbids naming individual headers; the two metadata items are listed
; explicitly because they are calculated, not read.  The list is the same for
; the MSGID and the RANGE form, so the argument is accepted and ignored
; exactly as section 8.6.2 directs for a server that does not distinguish
; them.
(defconst *fn-nntp-hdr-field-lines* '(":" ":bytes" ":lines"))

(defun fn-nntp-list-headers (session)
  (fn-nntp-multi-octets
   session (fn-nntp-string-octets "215 field list follows")
   (fn-nov-fmt-octet-lines *fn-nntp-hdr-field-lines*)))

(defun fn-nntp-list-unmaintained-response (session keyword args)
  ; RFC 3977 sections 7.6.5, 8.4, 8.6, and 9.6 and RFC 2980 section 2.1.4
  ; specify these arities.  A syntactically valid request for a recognized but
  ; unmaintained item is 503; an argument forbidden by that item's grammar
  ; remains 501.  ACTIVE.TIMES is NOT decided here: fn-nntp-list-command, at
  ; the end of this book, answers it from the environment's creation facts
  ; before this function is reached, so an arm for it here would be a branch
  ; the composed dispatcher cannot take.
  (if (fn-nntp-keywordp keyword "DISTRIB.PATS")
      (if (null args)
          (fn-nntp-single session "503 data item not stored")
        (fn-nntp-single session "501 syntax error"))
    (if (or (fn-nntp-keywordp keyword "DISTRIBUTIONS")
            ; RFC 2980 section 2.1.8's own response list for LIST
            ; SUBSCRIPTIONS is 215 or 503, so a server that maintains no
            ; default subscription list answers 503, not 501.  slrn 1.0.3
            ; sends this on every connection (measured 2026-09-20).
            (fn-nntp-keywordp keyword "SUBSCRIPTIONS"))
        (if (null args)
            (fn-nntp-single session "503 data item not stored")
          (fn-nntp-single session "501 syntax error"))
      (if (fn-nntp-keywordp keyword "OVERVIEW.FMT")
          (if (null args)
              (fn-nntp-list-overview-fmt session)
            (fn-nntp-single session "501 syntax error"))
        (if (fn-nntp-keywordp keyword "HEADERS")
            (if (or (null args)
                    (and (consp args) (null (cdr args))
                         (or (fn-nntp-keywordp (car args) "MSGID")
                             (fn-nntp-keywordp (car args) "RANGE"))))
                (fn-nntp-list-headers session)
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

; -----------------------------------------------------------------------------
; MODE READER (RFC 3977 section 5.3)
;
; This reader is not mode-switching (RFC 3977 section 3.4.2), so it never
; advertises MODE-READER.  Section 5.3.2's non-mode-switching rules then fix
; both branches exactly: advertising READER means a 200 or 201 response with
; the greeting's meaning and no state change whatsoever; not advertising it
; means 502 followed by an immediate close.  One constant decides both this
; and the capability list, so the two can never disagree.

(defconst *fn-nntp-advertise-readerp* t)

(defun fn-nntp-capability-lines (postingp)
  ; RFC 3977 section 3.3.2 makes a capability label a promise about a whole
  ; bundle, so each label below is advertised only because every command it
  ; indicates in appendix B is implemented with its argument forms:
  ; READER covers ARTICLE, BODY, DATE, GROUP, LAST, LISTGROUP, NEWGROUPS and
  ; NEXT; OVER MSGID covers OVER in all three forms and LIST OVERVIEW.FMT;
  ; HDR covers HDR in all three forms and LIST HEADERS (section 8.6); LIST
  ; names exactly the variants that answer with data.  POST (section 5.2.2)
  ; is advertised exactly when this connection's pinned configuration allows
  ; posting, which is the same bit fn-nntp-post-step reads before it answers
  ; a POST command with 340 rather than 440, so the label is a promise this
  ; server keeps.  No IHAVE, NEWNEWS, MODE-READER, TLS, authentication or
  ; compression capability is advertised, and this reader is not
  ; mode-switching (section 3.4.2).  XOVER and XHDR carry no capability
  ; label: RFC 2980 predates section 3.3 and names no label for them, and a
  ; client discovers them by trying them.
  ; Two ground lists rather than an append of a conditional: every caller's
  ; block-text obligation then evaluates one constant list per branch, which
  ; is what keeps books/nntp-effects.lisp's effect theorems cheap.
  (declare (xargs :guard t))
  (if postingp
      (list (fn-nntp-string-octets "VERSION 2")
            (fn-nntp-string-octets "READER")
            (fn-nntp-string-octets "POST")
            (fn-nntp-string-octets "OVER MSGID")
            (fn-nntp-string-octets "HDR")
            (fn-nntp-string-octets
             "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT")
            (fn-nntp-string-octets "IMPLEMENTATION fn-nntp-lab"))
    (list (fn-nntp-string-octets "VERSION 2")
          (fn-nntp-string-octets "READER")
          (fn-nntp-string-octets "OVER MSGID")
          (fn-nntp-string-octets "HDR")
          (fn-nntp-string-octets
           "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT")
          (fn-nntp-string-octets "IMPLEMENTATION fn-nntp-lab"))))

(defun fn-nntp-unadvertised-capability-lines ()
  (list (fn-nntp-string-octets "VERSION 2")
        (fn-nntp-string-octets "IMPLEMENTATION fn-nntp-lab")))

(defun fn-nntp-capabilities (session postingp)
  (fn-nntp-multi session "101 capability list follows"
                 (if *fn-nntp-advertise-readerp*
                     (fn-nntp-capability-lines postingp)
                   (fn-nntp-unadvertised-capability-lines))))

(defun fn-nntp-help (session)
  ; RFC 3977 section 7.2: a short summary of the commands that are
  ; understood.  Every keyword fn-nntp-session-command or
  ; fn-nntp-archive-command (books/nntp.lisp) recognizes appears here, and
  ; nothing else does; tests/acl2/nntp-legacy-tests.lisp pins the two lists
  ; against each other.
  (fn-nntp-multi session "100 help text follows"
                 (list (fn-nntp-string-octets
                        "CAPABILITIES HELP QUIT MODE DATE POST")
                       (fn-nntp-string-octets
                        "GROUP LISTGROUP LIST NEXT LAST NEWGROUPS")
                       (fn-nntp-string-octets
                        "ARTICLE HEAD BODY STAT")
                       (fn-nntp-string-octets
                        "OVER XOVER HDR XHDR"))))

; -----------------------------------------------------------------------------
; Reader environment: the clock observation and the persisted group-creation
; facts
;
; RFC 3977 section 7.1 requires DATE to report the server's own clock, and
; section 7.3 requires NEWGROUPS to report group creation times.  Neither is
; invented here.  The owner or host supplies one `fn-clock-observationp'
; (books/clock.lisp) and a list of persisted creation facts; the reader reads
; them and refuses when they are absent.  A creation fact is
;   (:fn-nntp-group-fact name created-at-dtn-ms observation)
; where `created-at-dtn-ms' is the DTN time (RFC 9171 section 4.2.6,
; milliseconds since 2000-01-01T00:00:00Z) at which the group was created and
; `observation' is the clock observation under which that time was established.
; The fact carries its own provenance so that a creation time can never be
; back-filled from the reader's current clock.  The mutable-owner lane
; persists these records; this book consumes the shape.

(defun fn-nntp-group-fact (name created-at observation)
  (declare (xargs :guard t :verify-guards nil))
  (list :fn-nntp-group-fact name created-at observation))

(defun fn-nntp-fact-name (x)
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-nntp-fact-created (x)
  (mbe :logic (car (cdr (cdr x))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(defun fn-nntp-fact-observation (x)
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))

(defun fn-nntp-group-factp (x)
  (and (true-listp x)
       (equal (len x) 4)
       (equal (car x) :fn-nntp-group-fact)
       (fn-nntp-safe-group-namep (fn-nntp-fact-name x))
       (natp (fn-nntp-fact-created x))
       (<= (fn-nntp-fact-created x) *fn-clock-max*)
       (fn-clock-observationp (fn-nntp-fact-observation x))))

(defun fn-nntp-group-fact-listp (xs)
  (if (consp xs)
      (and (fn-nntp-group-factp (car xs))
           (fn-nntp-group-fact-listp (cdr xs)))
    (null xs)))

; The third field is the posting permission of the connection the command
; arrived on: RFC 3977 section 5.2.2 makes the POST capability label a
; promise that POST will be accepted, and section 5.1.1 makes the greeting
; code say the same thing, so one bit decides both and the CAPABILITIES
; block can never disagree with what fn-nntp-post-step will do with a POST
; command.  The bit is the connection's own pinned configuration
; (fn-inj-config-allow), supplied by fn-nntp-post-step; nothing here reads a
; global.
(defun fn-nntp-env (observation facts posting)
  (declare (xargs :guard t :verify-guards nil))
  (list :fn-nntp-env observation facts posting))

(defun fn-nntp-env-observation (x)
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-nntp-env-facts (x)
  (mbe :logic (car (cdr (cdr x))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(defun fn-nntp-env-posting (x)
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))

(defun fn-nntp-envp (x)
  (and (true-listp x)
       (equal (len x) 4)
       (equal (car x) :fn-nntp-env)
       (fn-clock-observationp (fn-nntp-env-observation x))
       (fn-nntp-group-fact-listp (fn-nntp-env-facts x))
       (booleanp (fn-nntp-env-posting x))))

; The environment a host supplies when it holds no clock reading and no
; persisted creation facts.  DATE and NEWGROUPS refuse against it; they never
; fall back to a fabricated timestamp.
(defun fn-nntp-blind-env ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-nntp-env (fn-clock-observation 0 0 0 nil) nil nil))

(defthm fn-nntp-blind-env-is-an-env
  (fn-nntp-envp (fn-nntp-blind-env)))

; -----------------------------------------------------------------------------
; Bounded integer and calendar arithmetic
;
; Every division below is guard-total on non-negative integers.  The civil
; conversion is Howard Hinnant's closed-form `civil_from_days'/`days_from_civil'
; pair: no loop over years, so the work is constant whatever the clock reads.
; It is exact for a proleptic Gregorian day count that excludes leap seconds,
; which is what RFC 9171 section 4.2.6's DTN time is.  fn's reader has no
; timezone database, so its local time zone IS Coordinated Universal Time; RFC
; 3977 section 7.3.2 notes that the protocol cannot convey any other choice.

(defun fn-nntp-div (a b)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (integerp a) (integerp b) (< 0 b)) (floor a b) 0))

(defun fn-nntp-mod (a b)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (integerp a) (integerp b) (< 0 b)) (mod a b) 0))

; Days from 1970-01-01 to 2000-01-01, the DTN epoch.
(defconst *fn-nntp-dtn-epoch-days* 10957)
(defconst *fn-nntp-max-rendered-year* 9999)

(defun fn-nntp-civil-from-days (z)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((shifted (+ (nfix z) 719468))
         (era (fn-nntp-div shifted 146097))
         (doe (- shifted (* era 146097)))
         (yoe (fn-nntp-div (- (+ doe (fn-nntp-div doe 36524))
                              (+ (fn-nntp-div doe 1460)
                                 (fn-nntp-div doe 146096)))
                           365))
         (year (+ yoe (* era 400)))
         (doy (- doe (- (+ (* 365 yoe) (fn-nntp-div yoe 4))
                        (fn-nntp-div yoe 100))))
         (mp (fn-nntp-div (+ (* 5 doy) 2) 153))
         (day (+ (- doy (fn-nntp-div (+ (* 153 mp) 2) 5)) 1))
         (month (if (< mp 10) (+ mp 3) (- mp 9))))
    (list (if (<= month 2) (+ year 1) year) month day)))

(defun fn-nntp-days-from-civil (year month day)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((y (if (<= (ifix month) 2) (- (ifix year) 1) (ifix year)))
         (era (fn-nntp-div y 400))
         (yoe (- y (* era 400)))
         (doy (+ (fn-nntp-div (+ (* 153 (if (< 2 (ifix month))
                                            (- (ifix month) 3)
                                          (+ (ifix month) 9)))
                                 2)
                              5)
                 (- (ifix day) 1)))
         (doe (+ (* yoe 365) (fn-nntp-div yoe 4)
                 (- (fn-nntp-div yoe 100)) doy)))
    (+ (* era 146097) doe -719468)))

; (year month day hour minute second) of a DTN millisecond reading.
(defun fn-nntp-dtn-civil (ms)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((secs (fn-nntp-div (nfix ms) 1000))
         (days (+ (fn-nntp-div secs 86400) *fn-nntp-dtn-epoch-days*))
         (tod (fn-nntp-mod secs 86400))
         (ymd (fn-nntp-civil-from-days days)))
    (list (car ymd) (car (cdr ymd)) (car (cdr (cdr ymd)))
          (fn-nntp-div tod 3600)
          (fn-nntp-mod (fn-nntp-div tod 60) 60)
          (fn-nntp-mod tod 60))))

(defun fn-nntp-civil-year (x) (mbe :logic (car x) :exec (fn-ag-car x)))
(defun fn-nntp-civil-month (x)
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-nntp-civil-day (x)
  (mbe :logic (car (cdr (cdr x))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(defun fn-nntp-civil-hour (x)
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))
(defun fn-nntp-civil-minute (x)
  (mbe :logic (car (cdr (cdr (cdr (cdr x)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))
(defun fn-nntp-civil-second (x)
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr x))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                                          (fn-ag-cdr x))))))))

; DTN milliseconds for a civil instant, clamped at the DTN epoch.  A requested
; NEWGROUPS instant before 2000-01-01 selects every recorded creation.
(defun fn-nntp-civil-dtn-ms (year month day hour minute second)
  (declare (xargs :guard t :verify-guards nil))
  (let ((secs (+ (* (- (fn-nntp-days-from-civil year month day)
                       *fn-nntp-dtn-epoch-days*)
                    86400)
                 (* (nfix hour) 3600) (* (nfix minute) 60) (nfix second))))
    (if (< secs 0) 0 (* 1000 secs))))

; The host reads a clock; it does not decide what the reading means.  A POSIX
; millisecond reading reaches the reader unconverted and this function, not the
; adapter, shifts it to RFC 9171 section 4.2.6's DTN epoch.  A reading before
; 2000-01-01 clamps to the epoch rather than becoming a negative time.
(defconst *fn-nntp-unix-dtn-offset-ms* 946684800000)

(defun fn-nntp-unix-dtn-ms (unix-ms)
  (declare (xargs :guard t :verify-guards nil))
  (nfix (- (nfix unix-ms) *fn-nntp-unix-dtn-offset-ms*)))

(defun fn-nntp-host-observation (monotonic-ms unix-ms error-ms has-wall)
  (declare (xargs :guard t :verify-guards nil))
  (fn-clock-observation (nfix monotonic-ms) (fn-nntp-unix-dtn-ms unix-ms)
                        (nfix error-ms) (if has-wall t nil)))

(defthm fn-nntp-host-observation-is-an-observation
  (implies (and (<= (nfix monotonic-ms) *fn-clock-max*)
                (<= (fn-nntp-unix-dtn-ms unix-ms) *fn-clock-max*)
                (<= (nfix error-ms) *fn-clock-max*))
           (fn-clock-observationp
            (fn-nntp-host-observation monotonic-ms unix-ms error-ms has-wall)))
  ; The observation is an opaque record (books/clock.lisp, 2026-09-19): its
  ; recognizer is withdrawn at that book's export, so it is opened here by
  ; name and closed by the accessor-of-constructor lemmas it exports.
  :hints (("Goal" :in-theory (enable fn-clock-observationp)
           :do-not-induct t)))

; -----------------------------------------------------------------------------
; Zero-padded decimal rendering
;
; A rendered digit is a table lookup, not an arithmetic expression, so every
; octet DATE emits is a response octet by cases and needs no arithmetic book.

(defun fn-nntp-digit-octet (n)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((equal n 0) 48) ((equal n 1) 49) ((equal n 2) 50) ((equal n 3) 51)
        ((equal n 4) 52) ((equal n 5) 53) ((equal n 6) 54) ((equal n 7) 55)
        ((equal n 8) 56) ((equal n 9) 57) (t 48)))

(defun fn-nntp-pad2 (n)
  (declare (xargs :guard t :verify-guards nil))
  (list (fn-nntp-digit-octet (fn-nntp-mod (fn-nntp-div (nfix n) 10) 10))
        (fn-nntp-digit-octet (fn-nntp-mod (nfix n) 10))))

(defun fn-nntp-pad4 (n)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-nntp-pad2 (fn-nntp-div (nfix n) 100))
          (fn-nntp-pad2 (fn-nntp-mod (nfix n) 100))))

; -----------------------------------------------------------------------------
; DATE (RFC 3977 section 7.1)

(defun fn-nntp-date-octets (civil)
  (fn-nntp-append-pieces
   (list (fn-nntp-string-octets "111 ")
         (fn-nntp-pad4 (fn-nntp-civil-year civil))
         (fn-nntp-pad2 (fn-nntp-civil-month civil))
         (fn-nntp-pad2 (fn-nntp-civil-day civil))
         (fn-nntp-pad2 (fn-nntp-civil-hour civil))
         (fn-nntp-pad2 (fn-nntp-civil-minute civil))
         (fn-nntp-pad2 (fn-nntp-civil-second civil)))))

; RFC 3977 section 7.1 lists only the 111 response, so a reader with no wall
; reading cannot answer it.  Section 3.2.1 assigns 503 to a recognized command
; whose required information the server does not hold; that is the refusal
; here, and it is stated rather than replaced by a fabricated timestamp.
(defun fn-nntp-date-response (session env)
  (let ((obs (fn-nntp-env-observation env)))
    (if (not (fn-clock-observationp obs))
        (fn-nntp-single session "503 no clock observation supplied")
      (if (not (fn-clock-has-wall obs))
          (fn-nntp-single session "503 server holds no wall clock reading")
        (let ((civil (fn-nntp-dtn-civil (fn-clock-wall obs))))
          (if (and (natp (fn-nntp-civil-year civil))
                   (<= (fn-nntp-civil-year civil) *fn-nntp-max-rendered-year*))
              (fn-nntp-make-result
               session
               (list (fn-nntp-reply-effect
                      (fn-nntp-crlf (fn-nntp-date-octets civil)))))
            (fn-nntp-single
             session "503 clock reading outside the representable range")))))))

; -----------------------------------------------------------------------------
; NEWGROUPS (RFC 3977 section 7.3)

; posp, not zp: zp's own guard is (natp n), so a :guard t caller of zp owes
; (natp n).  (not (posp n)) is zp's value on every input and posp has guard t.
(defun fn-ng-take (n xs)
  (declare (xargs :guard t :verify-guards nil :measure (nfix n)))
  (if (or (not (posp n)) (not (consp xs)))
      nil
    (cons (fn-ag-car xs) (fn-ng-take (- n 1) (fn-ag-cdr xs)))))

(defun fn-ng-nthcdr (n xs)
  (declare (xargs :guard t :verify-guards nil :measure (nfix n)))
  (if (or (not (posp n)) (not (consp xs)))
      xs
    (fn-ng-nthcdr (- n 1) (fn-ag-cdr xs))))

; RFC 3977 section 7.3.2's field ranges.  The seconds field admits 60 for a
; leap second; the DTN day count that carries it does not, so a requested
; 60 second reads as the following instant.
(defun fn-nntp-ymd-okp (year month day)
  (declare (xargs :guard t :verify-guards nil))
  (and (integerp year) (<= 1900 year) (<= year *fn-nntp-max-rendered-year*)
       (integerp month) (<= 1 month) (<= month 12)
       (integerp day) (<= 1 day) (<= day 31)))

(defun fn-nntp-hms-okp (hour minute second)
  (declare (xargs :guard t :verify-guards nil))
  (and (integerp hour) (<= 0 hour) (<= hour 23)
       (integerp minute) (<= 0 minute) (<= minute 59)
       (integerp second) (<= 0 second) (<= second 60)))

; The declarative statement of the two accepted date forms, used as the
; independent side of fn-nntp-newgroups-date-accepts-exactly.
(defun fn-nntp-four-digit-date-formp (token)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-nntp-decimal-tokenp token)
       (equal (len token) 8)
       (fn-nntp-ymd-okp (fn-nntp-decimal-value (fn-ng-take 4 token))
                        (fn-nntp-decimal-value
                         (fn-ng-take 2 (fn-ng-nthcdr 4 token)))
                        (fn-nntp-decimal-value (fn-ng-nthcdr 6 token)))))

(defun fn-nntp-two-digit-date-formp (token)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-nntp-decimal-tokenp token)
       (equal (len token) 6)))

; The RFC's century rule: with a two-digit year, take the current century when
; yy is at most the current two-digit year, and the previous century
; otherwise.  `current-year' is the four-digit year of the supplied clock
; observation; 0 means the host gave no wall reading, and the two-digit form
; is then refused rather than resolved against a guess.
(defun fn-nntp-apply-century (yy current-year)
  (declare (xargs :guard t :verify-guards nil))
  (let ((century (* 100 (fn-nntp-div (nfix current-year) 100)))
        (current-yy (fn-nntp-mod (nfix current-year) 100)))
    (if (<= (nfix yy) current-yy)
        (+ century (nfix yy))
      (+ (- century 100) (nfix yy)))))

(defun fn-nntp-newgroups-date-parse (token current-year)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-nntp-decimal-tokenp token))
      (list :error :syntax)
    (if (equal (len token) 8)
        (let ((year (fn-nntp-decimal-value (fn-ng-take 4 token)))
              (month (fn-nntp-decimal-value
                      (fn-ng-take 2 (fn-ng-nthcdr 4 token))))
              (day (fn-nntp-decimal-value (fn-ng-nthcdr 6 token))))
          (if (fn-nntp-ymd-okp year month day)
              (list :ok year month day)
            (list :error :range)))
      (if (equal (len token) 6)
          (if (not (posp current-year))
              (list :error :no-century)
            (let ((year (fn-nntp-apply-century
                         (fn-nntp-decimal-value (fn-ng-take 2 token))
                         current-year))
                  (month (fn-nntp-decimal-value
                          (fn-ng-take 2 (fn-ng-nthcdr 2 token))))
                  (day (fn-nntp-decimal-value (fn-ng-nthcdr 4 token))))
              (if (fn-nntp-ymd-okp year month day)
                  (list :ok year month day)
                (list :error :range))))
        (list :error :syntax)))))

(defun fn-nntp-newgroups-time-parse (token)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (and (fn-nntp-decimal-tokenp token) (equal (len token) 6)))
      (list :error :syntax)
    (let ((hour (fn-nntp-decimal-value (fn-ng-take 2 token)))
          (minute (fn-nntp-decimal-value (fn-ng-take 2 (fn-ng-nthcdr 2 token))))
          (second (fn-nntp-decimal-value (fn-ng-nthcdr 4 token))))
      (if (fn-nntp-hms-okp hour minute second)
          (list :ok hour minute second)
        (list :error :range)))))

(defun fn-nntp-parse-okp (x)
  (mbe :logic (equal (car x) :ok) :exec (equal (fn-ag-car x) :ok)))
(defun fn-nntp-parse-1 (x)
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-nntp-parse-2 (x)
  (mbe :logic (car (cdr (cdr x))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(defun fn-nntp-parse-3 (x)
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))

; The current four-digit year of a clock observation, or 0 when the host holds
; no wall reading.
(defun fn-nntp-observed-year (obs)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-clock-observationp obs) (fn-clock-has-wall obs))
      (let ((year (fn-nntp-civil-year (fn-nntp-dtn-civil (fn-clock-wall obs)))))
        (if (posp year) year 0))
    0))

(defun fn-nntp-facts-since (threshold facts)
  (if (consp facts)
      ; fn-ng-less-equal, not <=: this function has guard t and threshold is
      ; the caller's parsed value.  fn-ng-less-equal-is-less-equal
      ; (books/nntp-syntax.lisp) is the equality, so the logic is unchanged.
      (if (and (fn-nntp-group-factp (car facts))
               (fn-ng-less-equal threshold (fn-nntp-fact-created (car facts))))
          (cons (car facts) (fn-nntp-facts-since threshold (cdr facts)))
        (fn-nntp-facts-since threshold (cdr facts)))
    nil))

(defun fn-nntp-fact-names (facts)
  (if (consp facts)
      (cons (fn-nntp-fact-name (car facts)) (fn-nntp-fact-names (cdr facts)))
    nil))

(defun fn-nntp-newgroups-response (session archive env args)
  ; NEWGROUPS date time [GMT].  fn's local time zone is UTC, so the GMT token
  ; changes nothing but is accepted exactly where the grammar allows it.
  (if (not (or (and (consp args) (consp (cdr args)) (null (cdr (cdr args))))
               (and (consp args) (consp (cdr args)) (consp (cdr (cdr args)))
                    (null (cdr (cdr (cdr args))))
                    (fn-nntp-keywordp (car (cdr (cdr args))) "GMT"))))
      (fn-nntp-single session "501 syntax error")
    (let* ((obs (fn-nntp-env-observation env))
           (date (fn-nntp-newgroups-date-parse
                  (car args) (fn-nntp-observed-year obs)))
           (time (fn-nntp-newgroups-time-parse (car (cdr args)))))
      (if (and (not (fn-nntp-parse-okp date))
               (equal (car (cdr date)) :no-century))
          (fn-nntp-single
           session "503 two-digit year needs a wall clock reading")
        (if (or (not (fn-nntp-parse-okp date)) (not (fn-nntp-parse-okp time)))
            (fn-nntp-single session "501 syntax error")
          (let ((threshold (fn-nntp-civil-dtn-ms
                            (fn-nntp-parse-1 date) (fn-nntp-parse-2 date)
                            (fn-nntp-parse-3 date) (fn-nntp-parse-1 time)
                            (fn-nntp-parse-2 time) (fn-nntp-parse-3 time))))
            (fn-nntp-multi
             session "231 list of new newsgroups follows"
             (fn-nntp-active-lines
              archive
              (fn-nntp-fact-names
               (fn-nntp-facts-since threshold
                                    (fn-nntp-env-facts env)))))))))))

; -----------------------------------------------------------------------------
; Overview projection (RFC 3977 sections 8.3 and 8.4, RFC 5536 section 3)
;
; Every overview field comes from the proved article view in books/article.lisp
; through books/article-fields.lisp's lookup; this book does not parse a second
; time or reconstruct a header.  The section 8.3.2 transformation is applied
; once, by fn-nov-scrub: CRLF pairs are removed (undoing folding and the
; terminating CRLF) and each remaining TAB, NUL, LF or CR becomes a single
; space.  The resulting field therefore carries none of TAB, CR, LF or NUL, so
; it can neither split a line nor invent a ninth field.

(defconst *fn-nov-subject-name* '(115 117 98 106 101 99 116))
(defconst *fn-nov-from-name* '(102 114 111 109))
(defconst *fn-nov-date-name* '(100 97 116 101))
(defconst *fn-nov-message-id-name* '(109 101 115 115 97 103 101 45 105 100))
(defconst *fn-nov-references-name* '(114 101 102 101 114 101 110 99 101 115))

(defun fn-nov-scrub-byte (byte)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (integerp byte) (<= 1 byte) (<= byte 255)
           (not (equal byte 9)) (not (equal byte 13)) (not (equal byte 10)))
      byte
    32))

(defun fn-nov-scrub (bytes)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count bytes)))
  (if (consp bytes)
      (if (and (equal (fn-ag-car bytes) 13)
               (consp (fn-ag-cdr bytes))
               (equal (fn-ag-car (fn-ag-cdr bytes)) 10))
          (fn-nov-scrub (fn-ag-cdr (fn-ag-cdr bytes)))
        (cons (fn-nov-scrub-byte (fn-ag-car bytes))
              (fn-nov-scrub (fn-ag-cdr bytes))))
    nil))

; RFC 3977 section 8.3.2: the field is the header content, that is, the header
; name and its following colon and space removed.  The parsed view's unfolded
; value begins immediately after the colon.
(defun fn-nov-value-content (value)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp value) (equal (fn-ag-car value) 32))
      (fn-ag-cdr value)
    value))

(defun fn-nov-header-content (view name)
  (declare (xargs :guard (fn-article-syntax-p view) :verify-guards nil))
  (let ((fields (fn-article-get-headers view name)))
    (if (consp fields)
        (fn-nov-scrub (fn-nov-value-content
                       (fn-article-field-unfolded-value (car fields))))
      nil)))

; The :lines metadata item counts the body lines of the exact retained octets;
; :bytes counts those octets themselves.  Neither is stored beside the article
; and neither is recomputed from a normalized copy.
(defun fn-nov-body-line-count (payload)
  (declare (xargs :guard t :verify-guards nil))
  (let ((split (fn-nntp-split-article payload)))
    (if (fn-nntp-split-okp split)
        (let ((lines (fn-nntp-crlf-lines (fn-nntp-split-body split))))
          (if (equal (car lines) :ok) (fn-ng-len (car (cdr lines))) 0))
      0)))

(defun fn-nov-overview (article)
  ; (:ok subject from date message-id references bytes lines) | (:error)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((payload (fn-article-payload article))
         (parsed (fn-article-parse payload)))
    (if (not (and (true-listp parsed)
                  (fn-article-result-okp parsed)
                  (fn-article-syntax-p (fn-article-result-article parsed))))
        (list :error)
      (let ((view (fn-article-result-article parsed)))
        (list :ok
              (fn-nov-header-content view *fn-nov-subject-name*)
              (fn-nov-header-content view *fn-nov-from-name*)
              (fn-nov-header-content view *fn-nov-date-name*)
              (fn-nov-header-content view *fn-nov-message-id-name*)
              (fn-nov-header-content view *fn-nov-references-name*)
              (fn-ng-len payload)
              (fn-nov-body-line-count payload))))))

(defun fn-nov-okp (x)
  (mbe :logic (equal (car x) :ok) :exec (equal (fn-ag-car x) :ok)))
(defun fn-nov-subject (x)
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-nov-from (x)
  (mbe :logic (car (cdr (cdr x))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(defun fn-nov-date (x)
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))
(defun fn-nov-msgid (x)
  (mbe :logic (car (cdr (cdr (cdr (cdr x)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))
(defun fn-nov-references (x)
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr x))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                                          (fn-ag-cdr x))))))))
(defun fn-nov-bytes (x)
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr x)))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                                          (fn-ag-cdr (fn-ag-cdr x)))))))))
(defun fn-nov-lines (x)
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr x))))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                                          (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))))) 

; The eight mandatory fields of RFC 3977 section 8.3.2, TAB separated, in
; order.  No ninth field is emitted: this profile holds no Xref or other
; overview metadata, and section 8.3.2 makes subsequent fields optional.
(defun fn-nov-line (number over)
  (fn-nntp-append-pieces
   (list (fn-nntp-decimal-field number) '(9)
         (fn-nov-subject over) '(9)
         (fn-nov-from over) '(9)
         (fn-nov-date over) '(9)
         (fn-nov-msgid over) '(9)
         (fn-nov-references over) '(9)
         (fn-nntp-decimal-field (fn-nov-bytes over)) '(9)
         (fn-nntp-decimal-field (fn-nov-lines over)))))

(defun fn-nov-lines-for-numbers (group numbers articles)
  ; An article whose retained octets cannot be parsed produces no line: RFC
  ; 3977 section 8.3.2 says the server SHOULD NOT produce output for articles
  ; it cannot report, and an unprojectable article degrades only itself.
  (if (consp numbers)
      (let* ((number (car numbers))
             (article (fn-nntp-available-article group number articles))
             (over (if (consp article) (fn-nov-overview article) (list :error))))
        (if (fn-nov-okp over)
            (cons (fn-nov-line number over)
                  (fn-nov-lines-for-numbers group (cdr numbers) articles))
          (fn-nov-lines-for-numbers group (cdr numbers) articles)))
    nil))



; -----------------------------------------------------------------------------
; OVER (RFC 3977 section 8.3)

(defun fn-nntp-over-current (session archive)
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
            (let ((over (fn-nov-overview article)))
              (if (fn-nov-okp over)
                  (fn-nntp-multi session "224 overview information follows"
                                 (list (fn-nov-line current over)))
                (fn-nntp-single
                 session "503 stored article framing unavailable")))))))))

(defun fn-nntp-over-range (session archive token)
  (let ((group (fn-nntp-session-group session))
        (range (fn-nntp-parse-range token)))
    (if (null group)
        (fn-nntp-single session "412 no newsgroup selected")
      (let* ((numbers (fn-nntp-group-range-numbers
                       group (fn-nntp-range-low range)
                       (fn-nntp-range-high range) (fn-state-articles archive)))
             (lines (fn-nov-lines-for-numbers group numbers
                                              (fn-state-articles archive))))
        (if (consp lines)
            (fn-nntp-multi session "224 overview information follows" lines)
          (fn-nntp-single session "423 no articles in that range"))))))

(defun fn-nntp-over-msgid (session archive token)
  ; RFC 3977 section 8.3.2: the number is zero for the message-id form, and
  ; this form never alters the selected group or the current article.
  (let ((article (fn-find-article (fn-nntp-token-string token)
                                  (fn-state-articles archive))))
    (if (not (consp article))
        (fn-nntp-single session "430 no article with that message-id")
      (let ((over (fn-nov-overview article)))
        (if (fn-nov-okp over)
            (fn-nntp-multi session "224 overview information follows"
                           (list (fn-nov-line 0 over)))
          (fn-nntp-single session "503 stored article framing unavailable"))))))

(defun fn-nntp-over-response (session archive args)
  (mbe :logic
       (if (null args)
           (fn-nntp-over-current session archive)
         (if (null (cdr args))
             (let ((token (car args)))
               (if (fn-nntp-range-okp (fn-nntp-parse-range token))
                   (fn-nntp-over-range session archive token)
                 (if (fn-nntp-message-id-tokenp token)
                     (fn-nntp-over-msgid session archive token)
                   (fn-nntp-single session "501 syntax error"))))
           (fn-nntp-single session "501 syntax error")))
       :exec
       (if (null args)
           (fn-nntp-over-current session archive)
         (if (null (fn-ag-cdr args))
             (let ((token (fn-ag-car args)))
               (if (fn-nntp-range-okp (fn-nntp-parse-range token))
                   (fn-nntp-over-range session archive token)
                 (if (fn-nntp-message-id-tokenp token)
                     (fn-nntp-over-msgid session archive token)
                   (fn-nntp-single session "501 syntax error"))))
           (fn-nntp-single session "501 syntax error")))))


(defun fn-nntp-mode-response (session env args)
  (if (and (consp args) (null (cdr args))
           (fn-nntp-keywordp (car args) "READER"))
      (if *fn-nntp-advertise-readerp*
          ; Section 5.3.2: the response carries the greeting's meaning, so it
          ; reads the same posting bit the greeting and the POST capability
          ; label read (RFC 3977 sections 5.1.1 and 5.2.2).
          (if (fn-nntp-env-posting env)
              (fn-nntp-single session "200 posting allowed")
            (fn-nntp-single session "201 posting prohibited"))
        (fn-nntp-make-result
         session
         (list (fn-nntp-reply-effect
                (fn-nntp-crlf
                 (fn-nntp-string-octets
                  "502 reading service permanently unavailable")))
               (fn-nntp-close-effect))))
    (fn-nntp-single session "501 syntax error")))

; The guard for the overview field lookup: a field returned by the proved
; lookup view of a syntactically valid parsed article is a field.  Local: it
; is a guard fact for fn-nov-overview below and no includer needs it.
(local
 (defthm fn-nov-get-headers-aux-car-is-a-field
   (implies (and (fn-article-field-listp fields)
                 (consp (fn-article-get-headers-aux fields name)))
            (and (fn-article-fieldp (car (fn-article-get-headers-aux fields name)))
                 (true-listp (car (fn-article-get-headers-aux fields name)))))
   :hints (("Goal" :in-theory (enable fn-article-get-headers-aux
                                      fn-article-field-listp
                                      fn-article-fieldp)))))

(local
 (defthm fn-nov-get-headers-car-is-a-field
   (implies (and (fn-article-syntax-p view)
                 (consp (fn-article-get-headers view name)))
            (and (fn-article-fieldp (car (fn-article-get-headers view name)))
                 (true-listp (car (fn-article-get-headers view name)))))
   :hints (("Goal" :in-theory (enable fn-article-get-headers
                                      fn-article-fieldp)))))

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

(verify-guards fn-nov-fmt-octet-lines)

(verify-guards fn-nntp-list-overview-fmt)

(verify-guards fn-nntp-list-headers)

(verify-guards fn-nntp-list-unmaintained-response)

(verify-guards fn-nntp-list-response)

(verify-guards fn-nntp-group-fact)

(verify-guards fn-nntp-fact-name)

(verify-guards fn-nntp-fact-created)

(verify-guards fn-nntp-fact-observation)

(verify-guards fn-nntp-group-factp)

(verify-guards fn-nntp-group-fact-listp)

(verify-guards fn-nntp-env)

(verify-guards fn-nntp-env-observation)

(verify-guards fn-nntp-env-facts)

(verify-guards fn-nntp-env-posting)

(verify-guards fn-nntp-envp)

(verify-guards fn-nntp-blind-env)

(verify-guards fn-nntp-unix-dtn-ms)

(verify-guards fn-nntp-host-observation)

(verify-guards fn-nntp-div)

(verify-guards fn-nntp-mod)

(verify-guards fn-nntp-civil-from-days)

(verify-guards fn-nntp-days-from-civil)

(verify-guards fn-nntp-dtn-civil)

(verify-guards fn-nntp-civil-year)

(verify-guards fn-nntp-civil-month)

(verify-guards fn-nntp-civil-day)

(verify-guards fn-nntp-civil-hour)

(verify-guards fn-nntp-civil-minute)

(verify-guards fn-nntp-civil-second)

(verify-guards fn-nntp-civil-dtn-ms)

(verify-guards fn-nntp-digit-octet)

(verify-guards fn-nntp-pad2)

(verify-guards fn-nntp-pad4)

(verify-guards fn-nntp-date-octets)

(verify-guards fn-nntp-date-response)

(verify-guards fn-ng-take)

(verify-guards fn-ng-nthcdr)

(verify-guards fn-nntp-ymd-okp)

(verify-guards fn-nntp-hms-okp)

(verify-guards fn-nntp-four-digit-date-formp)

(verify-guards fn-nntp-two-digit-date-formp)

(verify-guards fn-nntp-apply-century)

(verify-guards fn-nntp-newgroups-date-parse)

(verify-guards fn-nntp-newgroups-time-parse)

(verify-guards fn-nntp-parse-okp)

(verify-guards fn-nntp-parse-1)

(verify-guards fn-nntp-parse-2)

(verify-guards fn-nntp-parse-3)

(verify-guards fn-nntp-observed-year)

(verify-guards fn-nntp-facts-since)

(verify-guards fn-nntp-fact-names)

(verify-guards fn-nntp-newgroups-response)

(verify-guards fn-nov-scrub-byte)

(verify-guards fn-nov-scrub)

(verify-guards fn-nov-value-content)

; The article accessors stay closed here so that
; fn-nov-get-headers-car-is-a-field (local, above) is what discharges
; the field obligation; opening fn-article-get-headers buries it.
(verify-guards fn-nov-header-content
  :hints (("Goal" :in-theory (disable fn-article-get-headers
                                      fn-article-syntax-p))))

(verify-guards fn-nov-body-line-count)

; The article accessors stay closed here so that
; fn-nov-get-headers-car-is-a-field (local, above) is what discharges
; the field obligation; opening fn-article-get-headers buries it.
(verify-guards fn-nov-overview
  :hints (("Goal" :in-theory (disable fn-article-get-headers
                                      fn-article-syntax-p))))

(verify-guards fn-nov-okp)

(verify-guards fn-nov-subject)

(verify-guards fn-nov-from)

(verify-guards fn-nov-date)

(verify-guards fn-nov-msgid)

(verify-guards fn-nov-references)

(verify-guards fn-nov-bytes)

(verify-guards fn-nov-lines)

(verify-guards fn-nov-line)

(verify-guards fn-nov-lines-for-numbers)

(verify-guards fn-nntp-over-current)

(verify-guards fn-nntp-over-range)

(verify-guards fn-nntp-over-msgid)

(verify-guards fn-nntp-over-response)

(verify-guards fn-nntp-mode-response)

(verify-guards fn-nntp-capability-lines)

(verify-guards fn-nntp-unadvertised-capability-lines)

(verify-guards fn-nntp-capabilities)

(verify-guards fn-nntp-help)

; -----------------------------------------------------------------------------
; POST, RFC 3977 section 6.3.1: the offer
;
; POST reads no committed article, so it is an archive-free command and lives
; with CAPABILITIES, HELP and QUIT.  The offer is the whole of what the
; dispatcher decides: 340, plus the one effect that tells the host to put the
; wire into article mode (books/wire.lisp fn-wire-begin-article).  Whether
; this server accepts postings at all, what the supplied octets become, and
; whether the result is 240 or 441 are decided in books/nntp-post.lisp, which
; is the function the serving host calls; see specs/nntp.md.

(defun fn-nntp-begin-article-effect ()
  (list :begin-article))

(defun fn-nntp-post-offer (session)
  (fn-nntp-make-result
   session
   (list (fn-nntp-reply-effect
          (fn-nntp-crlf (fn-nntp-string-octets "340 send article to be posted")))
         (fn-nntp-begin-article-effect))))

(verify-guards fn-nntp-begin-article-effect)

(verify-guards fn-nntp-post-offer)

; -----------------------------------------------------------------------------
; XOVER (RFC 2980 section 2.8): OVER's legacy spelling
;
; The same overview renderer and the same 224 multi-line body.
; fn-nntp-xover-range and fn-nntp-over-range differ in exactly one octet
; string, because RFC 2980 section 2.8.1 assigns 420 where RFC 3977 section
; 8.3.1 assigns 423; RFC 2980 defines no message-id form and so no 430, and
; this spelling refuses one as a syntax error rather than inventing a code.
; The agreement is proved, not asserted: see
; fn-nntp-xover-agrees-with-over-on-a-nonempty-range in books/nntp-legacy.lisp.

(defun fn-nntp-xover-range (session archive token)
  (let ((group (fn-nntp-session-group session))
        (range (fn-nntp-parse-range token)))
    (if (null group)
        (fn-nntp-single session "412 no newsgroup selected")
      (let* ((numbers (fn-nntp-group-range-numbers
                       group (fn-nntp-range-low range)
                       (fn-nntp-range-high range) (fn-state-articles archive)))
             (lines (fn-nov-lines-for-numbers group numbers
                                              (fn-state-articles archive))))
        (if (consp lines)
            (fn-nntp-multi session "224 overview information follows" lines)
          (fn-nntp-single session "420 no article(s) selected"))))))

(defun fn-nntp-xover-response (session archive args)
  (if (null args)
      (fn-nntp-over-current session archive)
    (if (and (consp args) (null (cdr args))
             (fn-nntp-range-okp (fn-nntp-parse-range (car args))))
        (fn-nntp-xover-range session archive (car args))
      (fn-nntp-single session "501 syntax error"))))

; -----------------------------------------------------------------------------
; HDR (RFC 3977 section 8.5) and XHDR (RFC 2980 section 2.6)
;
; One field of one article at a time, read from the same proved article view
; the overview renderer reads (books/article.lisp fn-article-get-headers) and
; put through the same section 8.3.2 transformation (fn-nov-scrub), so an HDR
; value can no more split a line or invent a field than an overview field can.
; Any header may be requested, which is why LIST HEADERS answers with the
; single colon of section 8.6.2; the two calculated metadata items :bytes and
; :lines are the same two the overview line carries and are computed by the
; same two functions, never re-derived.
;
; The two spellings differ in three places and nowhere else, each fixed by its
; RFC: the initial line is 225 (section 8.5.1) or 221 (section 2.6.1); an
; empty range is 423 (section 8.5.2) or 420 (section 2.6.1); and the
; message-id form renders the article number as 0 (section 8.5.2) or as the
; message-id itself (section 2.6).

(defun fn-nntp-contains-colonp (token)
  (if (consp token)
      (or (equal (car token) 58) (fn-nntp-contains-colonp (cdr token)))
    nil))

(defun fn-nntp-hdr-metadata-tokenp (token)
  (or (fn-nntp-keywordp token ":BYTES") (fn-nntp-keywordp token ":LINES")))

(defun fn-nntp-hdr-fieldp (token)
  ; A header name (RFC 5536 section 2.2: printable US-ASCII except colon) or
  ; one of the two metadata items of RFC 3977 section 8.5.2.  The tokenizer
  ; has already excluded space and TAB; fn-nntp-printable-tokenp excludes CR,
  ; LF, NUL and every octet above 126, so a field name can never carry a
  ; separator into a rendered line.
  (and (consp token)
       (fn-nntp-printable-tokenp token)
       (or (fn-nntp-hdr-metadata-tokenp token)
           (not (fn-nntp-contains-colonp token)))))

(defun fn-nntp-hdr-okp (x)
  (mbe :logic (equal (car x) :ok) :exec (equal (fn-ag-car x) :ok)))
(defun fn-nntp-hdr-octets (x)
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))

(defun fn-nntp-hdr-content (field article)
  ; (:ok octets) | (:error).  :error only where the retained octets do not
  ; parse: section 8.5.2 produces a line for every article in the range that
  ; exists, and an unparsable article degrades only itself, exactly as in
  ; fn-nov-lines-for-numbers.
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-nntp-hdr-metadata-tokenp field)
      (list :ok
            (fn-nntp-decimal-field
             (if (fn-nntp-keywordp field ":BYTES")
                 (fn-ng-len (fn-article-payload article))
               (fn-nov-body-line-count (fn-article-payload article)))))
    (let* ((payload (fn-article-payload article))
           (parsed (fn-article-parse payload)))
      (if (not (and (true-listp parsed)
                    (fn-article-result-okp parsed)
                    (fn-article-syntax-p (fn-article-result-article parsed))))
          (list :error)
        (list :ok (fn-nov-header-content
                   (fn-article-result-article parsed) field))))))

(defun fn-nntp-hdr-line (label content)
  ; RFC 3977 section 8.5.2: the article number, a space, then the contents of
  ; the field.
  (fn-nntp-append-pieces (list label '(32) content)))

(defun fn-nntp-hdr-lines-for-numbers (field group numbers articles)
  (if (consp numbers)
      (let* ((number (car numbers))
             (article (fn-nntp-available-article group number articles))
             (content (if (consp article)
                          (fn-nntp-hdr-content field article)
                        (list :error))))
        (if (fn-nntp-hdr-okp content)
            (cons (fn-nntp-hdr-line (fn-nntp-decimal-field number)
                                    (fn-nntp-hdr-octets content))
                  (fn-nntp-hdr-lines-for-numbers field group (cdr numbers)
                                                 articles))
          (fn-nntp-hdr-lines-for-numbers field group (cdr numbers) articles)))
    nil))

(defun fn-nntp-hdr-initial (legacyp)
  (if legacyp "221 header follows" "225 headers follow"))

(defun fn-nntp-hdr-current (session archive field legacyp)
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
            (let ((content (fn-nntp-hdr-content field article)))
              (if (fn-nntp-hdr-okp content)
                  (fn-nntp-multi
                   session (fn-nntp-hdr-initial legacyp)
                   (list (fn-nntp-hdr-line (fn-nntp-decimal-field current)
                                           (fn-nntp-hdr-octets content))))
                (fn-nntp-single
                 session "503 stored article framing unavailable")))))))))

(defun fn-nntp-hdr-range (session archive field token legacyp)
  (let ((group (fn-nntp-session-group session))
        (range (fn-nntp-parse-range token)))
    (if (null group)
        (fn-nntp-single session "412 no newsgroup selected")
      (let* ((numbers (fn-nntp-group-range-numbers
                       group (fn-nntp-range-low range)
                       (fn-nntp-range-high range) (fn-state-articles archive)))
             (lines (fn-nntp-hdr-lines-for-numbers
                     field group numbers (fn-state-articles archive))))
        (if (consp lines)
            (fn-nntp-multi session (fn-nntp-hdr-initial legacyp) lines)
          (if legacyp
              (fn-nntp-single session "420 no article(s) selected")
            (fn-nntp-single session "423 no articles in that range")))))))

(defun fn-nntp-hdr-msgid (session archive field token legacyp)
  ; RFC 3977 section 8.5.2 renders the article number as zero; RFC 2980
  ; section 2.6 renders the message-id itself.  Neither form alters the
  ; selected group or the current article.  The legacy label goes through
  ; fn-nov-scrub, which is the identity on a printable token and total on
  ; every other value, so the label cannot carry a separator either.
  (let ((article (fn-find-article (fn-nntp-token-string token)
                                  (fn-state-articles archive))))
    (if (not (consp article))
        (fn-nntp-single session "430 no article with that message-id")
      (let ((content (fn-nntp-hdr-content field article)))
        (if (fn-nntp-hdr-okp content)
            (fn-nntp-multi
             session (fn-nntp-hdr-initial legacyp)
             (list (fn-nntp-hdr-line (if legacyp
                                         (fn-nov-scrub token)
                                       (fn-nntp-decimal-field 0))
                                     (fn-nntp-hdr-octets content))))
          (fn-nntp-single session "503 stored article framing unavailable"))))))

(defun fn-nntp-hdr-command (session archive args legacyp)
  (if (not (and (consp args) (fn-nntp-hdr-fieldp (car args))))
      (fn-nntp-single session "501 syntax error")
    (let ((field (car args)) (rest (cdr args)))
      (if (null rest)
          (fn-nntp-hdr-current session archive field legacyp)
        (if (and (consp rest) (null (cdr rest)))
            (let ((token (car rest)))
              (if (fn-nntp-range-okp (fn-nntp-parse-range token))
                  (fn-nntp-hdr-range session archive field token legacyp)
                (if (fn-nntp-message-id-tokenp token)
                    (fn-nntp-hdr-msgid session archive field token legacyp)
                  (fn-nntp-single session "501 syntax error"))))
          (fn-nntp-single session "501 syntax error"))))))

(defun fn-nntp-hdr-response (session archive args)
  (fn-nntp-hdr-command session archive args nil))

(defun fn-nntp-xhdr-response (session archive args)
  (fn-nntp-hdr-command session archive args t))

; -----------------------------------------------------------------------------
; LIST ACTIVE.TIMES (RFC 3977 section 7.6.4, RFC 2980 section 2.1.3)
;
; The list is exactly the persisted group-creation facts the host supplies,
; which are the same facts NEWGROUPS reads, so the two are consistent by
; construction rather than by a second derivation.  Section 7.6.4 permits
; omitting groups whose creation information is unavailable, which is every
; group the configuration history has no created stamp for.  The third field
; is "plain text intended to describe the entity that created the newsgroup";
; a configuration record carries no creator, so the text says so rather than
; naming a mailbox that does not exist.

(defconst *fn-nntp-active-times-creator* " unattributed")

(defun fn-nntp-dtn-unix-seconds (ms)
  ; Section 7.6.4 measures the creation time in seconds since 1970-01-01; a
  ; creation fact carries it as DTN time (RFC 9171 section 4.2.6,
  ; milliseconds since 2000-01-01).  *fn-nntp-unix-dtn-offset-ms* is the same
  ; constant fn-nntp-unix-dtn-ms uses in the other direction.
  (declare (xargs :guard t :verify-guards nil))
  (if (natp ms)
      (fn-nntp-div (+ ms *fn-nntp-unix-dtn-offset-ms*) 1000)
    (fn-nntp-div *fn-nntp-unix-dtn-offset-ms* 1000)))

(defun fn-nntp-active-times-line (fact)
  (fn-nntp-append-pieces
   (list (fn-nntp-string-octets (fn-nntp-fact-name fact)) '(32)
         (fn-nntp-decimal-field
          (fn-nntp-dtn-unix-seconds (fn-nntp-fact-created fact)))
         (fn-nntp-string-octets *fn-nntp-active-times-creator*))))

(defun fn-nntp-active-times-lines (facts)
  (if (consp facts)
      (if (fn-nntp-group-factp (car facts))
          (cons (fn-nntp-active-times-line (car facts))
                (fn-nntp-active-times-lines (cdr facts)))
        (fn-nntp-active-times-lines (cdr facts)))
    nil))

(defun fn-nntp-filter-facts-by-wildmat (patterns facts)
  (if (consp facts)
      (if (and (fn-nntp-group-factp (car facts))
               (fn-nntp-group-matches-parsed-wildmatp
                patterns (fn-nntp-fact-name (car facts))))
          (cons (car facts)
                (fn-nntp-filter-facts-by-wildmat patterns (cdr facts)))
        (fn-nntp-filter-facts-by-wildmat patterns (cdr facts)))
    nil))

(defun fn-nntp-list-active-times (session env args)
  (if (null args)
      (fn-nntp-multi session "215 information follows"
                     (fn-nntp-active-times-lines (fn-nntp-env-facts env)))
    (if (and (consp args) (null (cdr args)))
        (let ((parsed (fn-wildmat-parse (car args))))
          (if (fn-wildmat-result-okp parsed)
              (fn-nntp-multi
               session "215 information follows"
               (fn-nntp-active-times-lines
                (fn-nntp-filter-facts-by-wildmat
                 (fn-wildmat-result-value parsed) (fn-nntp-env-facts env))))
            (fn-nntp-single session "501 syntax error")))
      (fn-nntp-single session "501 syntax error"))))

(defun fn-nntp-list-command (session archive env args)
  ; LIST's variant keyword is dispatched here so that ACTIVE.TIMES can read
  ; the environment's creation facts; every other variant is decided by
  ; fn-nntp-list-response above, which needs no environment.  This is the
  ; function books/nntp.lisp calls for LIST.
  (if (and (consp args)
           (fn-nntp-keyword-tokenp (car args))
           (fn-nntp-keywordp (car args) "ACTIVE.TIMES"))
      (fn-nntp-list-active-times session env (cdr args))
    (fn-nntp-list-response session archive args)))

(verify-guards fn-nntp-xover-range)
(verify-guards fn-nntp-xover-response)
(verify-guards fn-nntp-contains-colonp)
(verify-guards fn-nntp-hdr-metadata-tokenp)
(verify-guards fn-nntp-hdr-fieldp)
(verify-guards fn-nntp-hdr-okp)
(verify-guards fn-nntp-hdr-octets)
; The article accessors stay closed here so that
; fn-nov-get-headers-car-is-a-field (local, above) is what discharges the
; field obligation; opening fn-article-get-headers buries it.
(verify-guards fn-nntp-hdr-content
  :hints (("Goal" :in-theory (disable fn-article-get-headers
                                      fn-article-syntax-p))))
(verify-guards fn-nntp-hdr-line)
(verify-guards fn-nntp-hdr-lines-for-numbers)
(verify-guards fn-nntp-hdr-initial)
(verify-guards fn-nntp-hdr-current)
(verify-guards fn-nntp-hdr-range)
(verify-guards fn-nntp-hdr-msgid)
(verify-guards fn-nntp-hdr-command)
(verify-guards fn-nntp-hdr-response)
(verify-guards fn-nntp-xhdr-response)
(verify-guards fn-nntp-dtn-unix-seconds)
(verify-guards fn-nntp-active-times-line)
(verify-guards fn-nntp-active-times-lines)
(verify-guards fn-nntp-filter-facts-by-wildmat)
(verify-guards fn-nntp-list-active-times)
(verify-guards fn-nntp-list-command)

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
    fn-nntp-list-response fn-nntp-capabilities fn-nntp-help
    fn-nov-fmt-octet-lines fn-nntp-list-overview-fmt fn-nntp-group-fact
    fn-nntp-fact-name fn-nntp-fact-created fn-nntp-fact-observation
    fn-nntp-group-factp fn-nntp-group-fact-listp fn-nntp-env
    fn-nntp-env-observation fn-nntp-env-facts fn-nntp-env-posting
    fn-nntp-envp fn-nntp-blind-env
    fn-nntp-unix-dtn-ms fn-nntp-host-observation fn-nntp-div fn-nntp-mod
    fn-nntp-civil-from-days fn-nntp-days-from-civil fn-nntp-dtn-civil
    fn-nntp-civil-year fn-nntp-civil-month fn-nntp-civil-day
    fn-nntp-civil-hour fn-nntp-civil-minute fn-nntp-civil-second
    fn-nntp-civil-dtn-ms fn-nntp-digit-octet fn-nntp-pad2 fn-nntp-pad4
    fn-nntp-date-octets fn-nntp-date-response fn-ng-take fn-ng-nthcdr
    fn-nntp-ymd-okp fn-nntp-hms-okp fn-nntp-four-digit-date-formp
    fn-nntp-two-digit-date-formp fn-nntp-apply-century
    fn-nntp-newgroups-date-parse fn-nntp-newgroups-time-parse
    fn-nntp-parse-okp fn-nntp-parse-1 fn-nntp-parse-2 fn-nntp-parse-3
    fn-nntp-observed-year fn-nntp-facts-since fn-nntp-fact-names
    fn-nntp-newgroups-response fn-nov-scrub-byte fn-nov-scrub
    fn-nov-value-content fn-nov-header-content fn-nov-body-line-count
    fn-nov-overview fn-nov-okp fn-nov-subject fn-nov-from fn-nov-date
    fn-nov-msgid fn-nov-references fn-nov-bytes fn-nov-lines fn-nov-line
    fn-nov-lines-for-numbers fn-nntp-over-current fn-nntp-over-range
    fn-nntp-over-msgid fn-nntp-over-response fn-nntp-mode-response
    fn-nntp-capability-lines fn-nntp-unadvertised-capability-lines
    fn-nntp-begin-article-effect fn-nntp-post-offer
    fn-nntp-list-headers fn-nntp-xover-range fn-nntp-xover-response
    fn-nntp-contains-colonp fn-nntp-hdr-metadata-tokenp fn-nntp-hdr-fieldp
    fn-nntp-hdr-okp fn-nntp-hdr-octets fn-nntp-hdr-content fn-nntp-hdr-line
    fn-nntp-hdr-lines-for-numbers fn-nntp-hdr-initial fn-nntp-hdr-current
    fn-nntp-hdr-range fn-nntp-hdr-msgid fn-nntp-hdr-command
    fn-nntp-hdr-response fn-nntp-xhdr-response fn-nntp-dtn-unix-seconds
    fn-nntp-active-times-line fn-nntp-active-times-lines
    fn-nntp-filter-facts-by-wildmat fn-nntp-list-active-times
    fn-nntp-list-command))

(in-theory (disable fn-nntp-responses-vocabulary))
