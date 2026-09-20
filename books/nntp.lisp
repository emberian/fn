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
      (fn-nntp-keywordp keyword "NEWGROUPS")))

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
   ((fn-nntp-keywordp keyword "NEWGROUPS")
    (fn-nntp-newgroups-response session archive env args))
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
