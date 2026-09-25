; fn experimental NNTP reader session core: the dispatcher.
;
; This is a deliberately small laboratory profile, not an NNTP conformance
; claim.  It reads only articles already committed by books/acceptance.lisp;
; it neither posts nor owns a second article store.  Its caller supplies one
; (:command octet-line) event at a time from fn-wire-next.  In particular, a
; host must not dispatch future POST input with bulk fn-wire-feed before it has
; processed the command that changes framing mode.
;
; The cluster below this file, in include order (2026-09-19 split):
;   nntp-syntax      octets, the command-line preflight, tokens, ranges
;   nntp-session     the session record, effects, the exact article projection
;   nntp-projection  projection from the committed acceptance state
;   nntp-responses   the per-command response builders
;   nntp             the dispatcher: fn-nntp-command and fn-nntp-step
; The host entry points (fn-nntp-open-session, fn-nntp-step) and every
; exported name are unchanged; a book that included "nntp" still sees them.

(in-package "ACL2")
(include-book "nntp-responses")

; The books below this one withdraw their definitions at their export events
; (2026-09-19 split of books/nntp.lisp).  This book is the continuation of
; that single file, so it re-enables exactly them, locally: within the
; chain the theory is the one the original file had at this point.
(local (in-theory (enable fn-nntp-syntax-vocabulary
                          fn-nntp-session-vocabulary
                          fn-nntp-projection-vocabulary
                          fn-nntp-responses-vocabulary)))
; The dispatcher is split by whether a command reads the archive at all.  No
; archive content can deny CAPABILITIES, HELP, QUIT, an unrecognized command,
; or a syntax error: see fn-nntp-archive-free-step-ignores-the-archive in
; books/nntp-invariants.lisp.
(defun fn-nntp-archive-keywordp (keyword)
  (or (fn-nntp-keywordp keyword "GROUP")
      (fn-nntp-keywordp keyword "LISTGROUP")
      (fn-nntp-keywordp keyword "LIST")
      (fn-nntp-keywordp keyword "NEXT")
      (fn-nntp-keywordp keyword "LAST")
      (fn-nntp-keywordp keyword "ARTICLE")
      (fn-nntp-keywordp keyword "HEAD")
      (fn-nntp-keywordp keyword "BODY")
      (fn-nntp-keywordp keyword "STAT")
      (fn-nntp-keywordp keyword "OVER")
      (fn-nntp-keywordp keyword "XOVER")
      (fn-nntp-keywordp keyword "HDR")
      (fn-nntp-keywordp keyword "XHDR")
      (fn-nntp-keywordp keyword "XPAT")
      (fn-nntp-keywordp keyword "NEWGROUPS")
      (fn-nntp-keywordp keyword "NEWNEWS")))

(defun fn-nntp-session-command (session env keyword args)
  (cond
   ((fn-nntp-keywordp keyword "CAPABILITIES")
    (if (or (null args)
            (and (consp args) (null (cdr args))
                 (fn-nntp-keyword-tokenp (car args))))
        (fn-nntp-capabilities session (fn-nntp-env-posting env))
      (fn-nntp-single session "501 syntax error")))
   ((fn-nntp-keywordp keyword "HELP")
    (if (null args) (fn-nntp-help session)
      (fn-nntp-single session "501 syntax error")))
   ((fn-nntp-keywordp keyword "POST")
    (if (null args) (fn-nntp-post-offer session)
      (fn-nntp-single session "501 syntax error")))
   ((fn-nntp-keywordp keyword "QUIT")
    (if (null args)
        (fn-nntp-make-result (fn-nntp-make-session nil
                                                   (fn-nntp-session-group session)
                                                   (fn-nntp-session-current session)
                                                   (fn-nntp-session-projected session))
                             (list (fn-nntp-reply-effect
                                    (fn-nntp-crlf (fn-nntp-string-octets "205 closing connection")))
                                   (fn-nntp-close-effect)))
      (fn-nntp-single session "501 syntax error")))
   ((fn-nntp-keywordp keyword "MODE") (fn-nntp-mode-response session env args))
   ((fn-nntp-keywordp keyword "DATE")
    (if (null args) (fn-nntp-date-response session env)
      (fn-nntp-single session "501 syntax error")))
   ; The transit commands (RFC 3977 section 6.3.2 IHAVE; RFC 4644 CHECK,
   ; TAKETHIS) are recognized here so a reader never sees 500 for them, and
   ; are not permitted on a reader connection: RFC 3977 section 3.2.1's 502,
   ; "command not permitted".  A peer connection is served them by
   ; books/peer-inbound.lisp (fn-peer-command) before the line reaches this
   ; dispatcher, from the peer record and the pinned node.
   ((or (fn-nntp-keywordp keyword "IHAVE")
        (fn-nntp-keywordp keyword "CHECK")
        (fn-nntp-keywordp keyword "TAKETHIS"))
    (fn-nntp-single session "502 transit is not permitted on this connection"))
   (t (fn-nntp-single session "500 command not recognized"))))

(defun fn-nntp-archive-command (session archive env keyword args)
  (cond
   ((fn-nntp-keywordp keyword "GROUP")
    (if (and (consp args) (null (cdr args)) (fn-nntp-printable-tokenp (car args)))
        (fn-nntp-group-result session archive (fn-nntp-token-string (car args)))
      (fn-nntp-single session "501 syntax error")))
   ((fn-nntp-keywordp keyword "LISTGROUP")
    (fn-nntp-listgroup-command session archive args))
   ((fn-nntp-keywordp keyword "LIST")
    (fn-nntp-list-command session archive env args))
   ((fn-nntp-keywordp keyword "NEXT")
    (if (null args) (fn-nntp-next-or-last session archive :next)
      (fn-nntp-single session "501 syntax error")))
   ((fn-nntp-keywordp keyword "LAST")
    (if (null args) (fn-nntp-next-or-last session archive :last)
      (fn-nntp-single session "501 syntax error")))
   ((fn-nntp-keywordp keyword "ARTICLE") (fn-nntp-retrieval session archive :article args))
   ((fn-nntp-keywordp keyword "HEAD") (fn-nntp-retrieval session archive :head args))
   ((fn-nntp-keywordp keyword "BODY") (fn-nntp-retrieval session archive :body args))
   ((fn-nntp-keywordp keyword "OVER") (fn-nntp-over-response session archive args))
   ; RFC 2980 sections 2.8 and 2.6: the legacy spellings of RFC 3977 sections
   ; 8.3 and 8.5.  Each is one call to the same renderer; the differences are
   ; the response codes those sections assign, and nothing else.
   ((fn-nntp-keywordp keyword "XOVER") (fn-nntp-xover-response session archive args))
   ((fn-nntp-keywordp keyword "HDR") (fn-nntp-hdr-response session archive args))
   ((fn-nntp-keywordp keyword "XHDR") (fn-nntp-xhdr-response session archive args))
   ; RFC 2980 section 2.9: XHDR with a wildmat filter on the rendered
   ; content.  The same renderer; see fn-nntp-xpat-lines-are-hdr-lines.
   ((fn-nntp-keywordp keyword "XPAT") (fn-nntp-xpat-response session archive args))
   ((fn-nntp-keywordp keyword "NEWGROUPS")
    (fn-nntp-newgroups-response session archive env args))
   ; RFC 3977 section 7.4.  Like NEWGROUPS it reads the environment, for the
   ; century of a two-digit year, and like NEWGROUPS it reads the archive --
   ; the articles here, the configured groups there -- so it belongs to this
   ; arm and not to fn-nntp-session-command.
   ((fn-nntp-keywordp keyword "NEWNEWS")
    (fn-nntp-newnews-response session archive env args))
   (t (fn-nntp-retrieval session archive :stat args))))

(defun fn-nntp-command (session archive env tokens)
  (let ((keyword (mbe :logic (car tokens) :exec (fn-ag-car tokens)))
        (args (mbe :logic (cdr tokens) :exec (fn-ag-cdr tokens))))
    (if (not (fn-nntp-keyword-tokenp keyword))
        (fn-nntp-single session "501 syntax error")
      (if (not (fn-nntp-archive-keywordp keyword))
          (fn-nntp-session-command session env keyword args)
        ; RFC 3977 section 3.2.1 assigns 503 to a recognized command the server
        ; cannot carry out because it does not hold the required information.
        (if (fn-nntp-session-projected session)
            (fn-nntp-archive-command session archive env keyword args)
          (fn-nntp-single session "503 archive projection unavailable"))))))
; A single command event is the integration boundary.  Other wire events are
; rejected as syntax, and a closed session produces no further effects.  The
; archive projection is not revalidated here: fn-nntp-open-session decided it
; once and the session carries the verdict.
(defun fn-nntp-step (session archive env wire-event)
  (if (or (not (fn-nntp-sessionp session))
          (not (equal (fn-nntp-session-openp session) t)))
      (fn-nntp-make-result session nil)
    (if (and (consp wire-event)
             (equal (car wire-event) :command)
             (consp (cdr wire-event))
             (null (cdr (cdr wire-event))))
        (let ((line (car (cdr wire-event))))
          (if (not (fn-nntp-command-inputp line))
              (fn-nntp-single session "501 syntax error")
            (let ((tokens (fn-nntp-tokenize line)))
              (if (and (consp tokens)
                       (fn-nntp-command-arguments-at-mostp tokens))
                  (fn-nntp-command session archive env tokens)
                (fn-nntp-single session "501 syntax error")))))
      (fn-nntp-single session "501 syntax error"))))

(verify-guards fn-nntp-archive-keywordp)

(verify-guards fn-nntp-session-command)

(verify-guards fn-nntp-archive-command)

(verify-guards fn-nntp-command)

(verify-guards fn-nntp-step)

; ---------------------------------------------------------------------------
; Export theory
;
; The definitions this book adds are proof vocabulary for the books above it,
; not rules an includer should inherit.  They are withdrawn under one name so
; a book that reasons about the transitions re-enables exactly them in one
; line (books/nntp-invariants.lisp does).  Ground evaluation is unaffected:
; only the :definition runes are withdrawn.

(deftheory fn-nntp-vocabulary
  '(fn-nntp-archive-keywordp fn-nntp-session-command fn-nntp-archive-command 
    fn-nntp-command fn-nntp-step))

(in-theory (disable fn-nntp-vocabulary))

; Served connections carry an immutable accepted archive, its historical
; verdict projection and the corresponding Message-ID trie.  Only the four
; Message-ID retrieval spellings use the trie here; all other commands retain
; the established archive dispatcher except the pinned :fn-verified HDR item.
(include-book "nntp-verdict")
(include-book "nntp-range-indexed")

; LIST COUNTS (RFC 6048 section 2.2) on the served path.  Each group's
; line reads that group's pinned membership bucket only: at most
; fn-gidx-lookup-work bucket headers (never more than the number of buckets)
; and the bucket's own entries, so a group costs O(B + E_g) for B buckets and
; E_g memberships in the group, and the whole reply O(G*B + M) for G listed
; groups and M memberships.  No archive article is visited.
; fn-gidx-list-counts-command-is-the-archive-fold (books/nntp-list-counts)
; equates the reply with fn-nntp-list-counts-command's under the carried
; bucket relation.
(defun fn-gidx-counts-line (archive buckets group)
  (fn-nntp-counts-summary-line
   group (fn-gidx-group-summary archive buckets group)))

(defun fn-gidx-counts-lines (archive buckets groups)
  (if (consp groups)
      (cons (fn-gidx-counts-line archive buckets (car groups))
            (fn-gidx-counts-lines archive buckets (cdr groups)))
    nil))

(defun fn-gidx-list-counts-command (session archive buckets args)
  (if (null args)
      (fn-nntp-multi session "215 list of newsgroups follows"
                     (fn-gidx-counts-lines archive buckets
                                           (fn-state-groups archive)))
    (if (and (consp args) (null (cdr args)))
        (let ((parsed (fn-wildmat-parse (car args))))
          (if (fn-wildmat-result-okp parsed)
              (fn-nntp-multi session "215 list of newsgroups follows"
                             (fn-gidx-counts-lines
                              archive buckets
                              (fn-nntp-filter-groups-by-wildmat
                               (fn-wildmat-result-value parsed)
                               (fn-state-groups archive))))
            (fn-nntp-single session "501 syntax error")))
      (fn-nntp-single session "501 syntax error"))))

(verify-guards fn-gidx-counts-line)
(verify-guards fn-gidx-counts-lines)
(verify-guards fn-gidx-list-counts-command)

(defthm fn-gidx-list-counts-command-preserves-session
  (equal (fn-nntp-result-session
          (fn-gidx-list-counts-command session archive buckets args))
         session)
  :hints (("Goal" :in-theory (e/d (fn-gidx-list-counts-command)
                                  (fn-gidx-counts-lines)))))

(in-theory (disable fn-gidx-counts-line fn-gidx-counts-lines
                    fn-gidx-list-counts-command))

; Withdrawal answers (packet C3, control-c3e).  The group pin's fourth slot
; carries the control pin of the view the connection is pinned to
; (`fn-ctl-pin': its withdrawn list W and withdrawal records WS,
; books/control-served.lisp).  A number or Message-ID the pinned archive does
; not hold but W does is answered `423 withdrawn' or `430 withdrawn' instead
; of the plain "no article" (RFC 3977 section 6.2.1.2 lets a removed article
; become unavailable; the text says why), and `HDR :fn-control <msgid>'
; states the withdrawing article's status (design 2026-09-25 section 2.5).
; Cost: one walk of W per retrieval by number or Message-ID (W holds only
; withdrawn articles), then the archive scan the retrieval already performs
; or one trie lookup; HDR :fn-control is two lookups for the article, two
; for its target, and one walk of WS.  books/nntp-control.lisp states the
; arms over the kernel.
(include-book "control-served")

(defun fn-nntp-number-withdrawn-p (session archive index token)
  (declare (xargs :guard t))
  (let ((group (fn-nntp-session-group session)))
    (and group
         (fn-nntp-number-tokenp token)
         (let ((number (fn-nntp-decimal-value token)))
           ; `fn-ctl-number-withdrawn' is this lookup in W.
           (and (consp (fn-nntp-find-group-number
                        group number
                        (fn-ctl-pin-withdrawn (fn-gidx-pin-control index))))
                (not (consp (fn-nntp-find-group-number
                             group number (fn-state-articles archive)))))))))

(defun fn-nntp-msgid-withdrawn-p (index token)
  (declare (xargs :guard t))
  (and (fn-octet-listp token)
       (fn-ctl-msgid-withdrawn (fn-nntp-token-string token)
                               (fn-ctl-pin-withdrawn (fn-gidx-pin-control index)))
       (not (consp (fn-midx-lookup (fn-nntp-token-string token)
                                   (fn-gidx-pin-trie index))))
       t))

(defun fn-nntp-withdrawn-reply (session msgidp)
  (declare (xargs :guard t))
  (fn-nntp-single session (if msgidp "430 withdrawn" "423 withdrawn")))

; An HDR field is one line with no NUL, TAB, CR or LF (RFC 3977 section
; 8.5.2; the test is fn-nov-clean-fieldp's, which sits above this book).  An
; item whose target text would break the line is not sent.
(defun fn-nntp-control-cleanp (bytes)
  (declare (xargs :guard t))
  (if (consp bytes)
      (and (integerp (car bytes)) (<= 1 (car bytes)) (<= (car bytes) 255)
           (not (equal (car bytes) 9)) (not (equal (car bytes) 13))
           (not (equal (car bytes) 10))
           (fn-nntp-control-cleanp (cdr bytes)))
    (null bytes)))

(defun fn-nntp-control-hdr-response (session archive index verdicts args)
  (declare (xargs :guard t))
  (if (and (consp args) (consp (cdr args)) (null (cddr args))
           (fn-nntp-message-id-tokenp (cadr args))
           (fn-octet-listp (cadr args)))
      (let* ((control (fn-gidx-pin-control index))
             (trie (fn-gidx-pin-trie index))
             (visible (fn-state-articles archive))
             (withdrawn (fn-ctl-pin-withdrawn control))
             (c (fn-ctl-served-held (fn-nntp-token-string (cadr args))
                                    trie visible withdrawn)))
        (if (not (consp c))
            (fn-nntp-single session "430 no article with that message-id")
          (let ((item (fn-nntp-string-octets
                       (fn-ctl-control-item
                        (fn-ctl-served-status c trie visible withdrawn
                                              (fn-ctl-pin-ws control) verdicts)
                        (fn-ctl-target-octets (fn-article-payload c))))))
            (if (fn-nntp-control-cleanp item)
                (fn-nntp-multi
                 session (fn-nntp-hdr-initial nil)
                 (list (fn-nntp-hdr-line (fn-nntp-decimal-field 0) item)))
              (fn-nntp-single session "503 control status unavailable")))))
    (fn-nntp-single session "501 syntax error")))

(defun fn-nntp-archive-command-pinned
    (session archive index verdicts env keyword args)
  (cond
   ((and (fn-nntp-keywordp keyword "LIST")
         (fn-gidx-pinp index)
         (consp args)
         (fn-nntp-keyword-tokenp (car args))
         (fn-nntp-keywordp (car args) "COUNTS"))
    (fn-gidx-list-counts-command
     session archive (fn-gidx-pin-buckets index) (cdr args)))
   ((and (or (fn-nntp-keywordp keyword "ARTICLE")
             (fn-nntp-keywordp keyword "HEAD")
             (fn-nntp-keywordp keyword "BODY")
             (fn-nntp-keywordp keyword "STAT"))
         (consp args) (null (cdr args))
         (fn-nntp-number-withdrawn-p session archive index (car args)))
    (fn-nntp-withdrawn-reply session nil))
   ((and (or (fn-nntp-keywordp keyword "ARTICLE")
             (fn-nntp-keywordp keyword "HEAD")
             (fn-nntp-keywordp keyword "BODY")
             (fn-nntp-keywordp keyword "STAT"))
         (consp args) (null (cdr args))
         (fn-nntp-message-id-tokenp (car args))
         (fn-nntp-msgid-withdrawn-p index (car args)))
    (fn-nntp-withdrawn-reply session t))
   ((and (or (fn-nntp-keywordp keyword "ARTICLE")
             (fn-nntp-keywordp keyword "HEAD")
             (fn-nntp-keywordp keyword "BODY")
             (fn-nntp-keywordp keyword "STAT"))
         (consp args) (null (cdr args))
         (fn-nntp-message-id-tokenp (car args)))
    (fn-nntp-msgid-retrieval-indexed
     session archive (fn-gidx-pin-trie index)
     (cond ((fn-nntp-keywordp keyword "ARTICLE") :article)
           ((fn-nntp-keywordp keyword "HEAD") :head)
           ((fn-nntp-keywordp keyword "BODY") :body)
           (t :stat))
     (car args)))
   ((and (fn-nntp-keywordp keyword "LISTGROUP")
         (fn-gidx-pinp index))
    (fn-gidx-listgroup-command
     session archive (fn-gidx-pin-buckets index) args))
   ((and (or (fn-nntp-keywordp keyword "OVER")
             (fn-nntp-keywordp keyword "XOVER"))
         (fn-gidx-pinp index)
         (consp args) (null (cdr args))
         (fn-nntp-range-okp (fn-nntp-parse-range (car args))))
    (fn-nntp-over-range-indexed
     session (fn-gidx-pin-buckets index) (fn-gidx-pin-trie index)
     (car args) (fn-nntp-keywordp keyword "XOVER")))
   ((and (fn-nntp-keywordp keyword "HDR")
         (consp args)
         (fn-nntp-keywordp (car args) ":FN-VERIFIED"))
    (fn-nntp-verdict-hdr-response session archive verdicts args))
   ((and (fn-nntp-keywordp keyword "HDR")
         (consp args)
         (fn-nntp-keywordp (car args) ":FN-CONTROL"))
    (fn-nntp-control-hdr-response session archive index verdicts args))
   (t (fn-nntp-archive-command session archive env keyword args))))

(defun fn-nntp-command-pinned (session archive index verdicts env tokens)
  (let ((keyword (mbe :logic (car tokens) :exec (fn-ag-car tokens)))
        (args (mbe :logic (cdr tokens) :exec (fn-ag-cdr tokens))))
    (if (not (fn-nntp-keyword-tokenp keyword))
        (fn-nntp-single session "501 syntax error")
      (if (not (fn-nntp-archive-keywordp keyword))
          (fn-nntp-session-command session env keyword args)
        (if (fn-nntp-session-projected session)
            (fn-nntp-archive-command-pinned
             session archive index verdicts env keyword args)
          (fn-nntp-single session "503 archive projection unavailable"))))))

(defun fn-nntp-step-pinned (session archive index verdicts env wire-event)
  (if (or (not (fn-nntp-sessionp session))
          (not (equal (fn-nntp-session-openp session) t)))
      (fn-nntp-make-result session nil)
    (if (and (consp wire-event)
             (equal (car wire-event) :command)
             (consp (cdr wire-event))
             (null (cdr (cdr wire-event))))
        (let ((line (car (cdr wire-event))))
          (if (not (fn-nntp-command-inputp line))
              (fn-nntp-single session "501 syntax error")
            (let ((tokens (fn-nntp-tokenize line)))
              (if (and (consp tokens)
                       (fn-nntp-command-arguments-at-mostp tokens))
                  (fn-nntp-command-pinned
                   session archive index verdicts env tokens)
                (fn-nntp-single session "501 syntax error")))))
      (fn-nntp-single session "501 syntax error"))))

(defthm fn-nntp-withdrawn-reply-preserves-session
  (equal (fn-nntp-result-session (fn-nntp-withdrawn-reply session msgidp))
         session))

(defthm fn-nntp-control-hdr-response-preserves-session
  (equal (fn-nntp-result-session
          (fn-nntp-control-hdr-response session archive index verdicts args))
         session)
  :hints (("Goal" :in-theory (e/d (fn-nntp-control-hdr-response)
                                  (fn-ctl-control-item fn-ctl-served-status
                                   fn-ctl-served-held fn-nntp-string-octets
                                   fn-nntp-control-cleanp fn-nntp-hdr-line
                                   fn-nntp-decimal-field fn-nntp-message-id-tokenp
                                   fn-gidx-pin-control fn-gidx-pin-trie
                                   fn-ctl-pin-withdrawn fn-ctl-pin-ws
                                   fn-nntp-token-string fn-ctl-target-octets
                                   fn-octet-listp)))))

(in-theory (disable fn-nntp-number-withdrawn-p fn-nntp-msgid-withdrawn-p
                    fn-nntp-control-hdr-response fn-nntp-withdrawn-reply))

(verify-guards fn-nntp-archive-command-pinned)
(verify-guards fn-nntp-command-pinned)
(verify-guards fn-nntp-step-pinned)
