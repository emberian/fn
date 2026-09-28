; Teeth for books/protocol-dispatch.lisp (lane defprotocol-2).
;
; KEYSTONE fn-proto-command-pinned-is-command-pinned has no hypothesis, so
; its positive witnesses evaluate both sides on the hostile reader archive
; (tests/acl2/hostile-reader-archive.lisp: withdrawn, reclaimed, unframed,
; cross-posted articles and control messages) for a command line of every
; row with :arms, a line no row names, and a line that is not a command.
; The MUTATION witnesses build the dispatcher from a table whose :arms is
; changed -- ARTICLE's withdrawn-number arm dropped, GROUP's syntax arm
; moved first -- and show a line on which that dispatcher and the
; host-called one differ: the equation refuses a table that says another
; thing than the dispatcher does.  The generated command-layer macro's
; expansion is pinned to the text lane host-lints wrote by hand (the
; byte-identical differential lane defprotocol-2 ran before deleting it).
(in-package "ACL2")
(include-book "hostile-reader-archive")
(include-book "../../books/protocol-dispatch")

(defun pdt-run (session line fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-proto-command-pinned session *hra-archive* *hra-index* *hra-verdicts* *hra-env*
                           (fn-nntp-tokenize (hra-oct line)) fn-arena))
(bpr-lift pdt-run 2)

(defun pdt-reply (session line)
  (declare (xargs :verify-guards nil))
  (in-arena-pdt-run *hra-payloads* session line))

(defconst *pdt-lines*
  '("CAPABILITIES" "CAPABILITIES x y" "HELP" "HELP x" "MODE READER" "MODE STREAM"
    "QUIT" "QUIT x" "GROUP fn.mod.a" "GROUP fn.nowhere" "GROUP" "LISTGROUP"
    "LISTGROUP fn.misc" "LAST" "NEXT" "NEXT x"
    "ARTICLE 1" "ARTICLE <t@example.invalid>" "ARTICLE 3" "ARTICLE 4" "ARTICLE 5"
    "ARTICLE <r@example.invalid>" "ARTICLE" "HEAD 2" "HEAD <f@example.invalid>"
    "BODY 3" "BODY 1" "STAT 4" "STAT <x@example.invalid>" "STAT 9"
    "OVER 1-5" "OVER" "OVER <o@example.invalid>" "XOVER 3" "XOVER 1-"
    "HDR Subject 1-5" "HDR :fn-control <c@example.invalid>"
    "HDR :fn-control <d@example.invalid>" "HDR :fn-verified 1-5"
    "HDR :fn-enrollment 1" "HDR Xref 5" "XHDR Subject 3" "XHDR Xref 5"
    "XPAT Subject 1-5 *" "LIST" "LIST COUNTS" "LIST OVERVIEW.FMT"
    "LIST ACTIVE.TIMES" "LIST SUBSCRIPTIONS" "LIST NOSUCH"
    "NEWGROUPS 20260101 000000" "NEWNEWS * 20260101 000000" "DATE" "DATE x"
    "POST" "POST x" "IHAVE <a@b>" "CHECK <a@b>" "TAKETHIS <a@b>"
    "XFNCATCHUP * 1-2 0 1-2" "XFNCATCHUP" "AUTHINFO USER x" "STARTTLS"
    "XREDEEM code" "FROBNICATE" "123" "article 1" "Group fn.mod.a"))

(defun pdt-agree (lines)
  (declare (xargs :verify-guards nil))
  (if (consp lines)
      (and (equal (pdt-reply *hra-session* (car lines))
                  (hra-reply *hra-session* (car lines)))
           (pdt-agree (cdr lines)))
    t))

; The same archive served with an Xref server named (the served
; environment always names one), so the Xref prelude and the served
; compatibility arms answer: fn-nntp-xref-reply, fn-rcompat-reply.
(defconst *pdt-env-x*
  (fn-nntp-env-listed nil nil nil (list nil nil (hra-oct "news.example.invalid"))))

(defun pdt-x-run (session line fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-proto-command-pinned session *hra-archive* *hra-index* *hra-verdicts* *pdt-env-x*
                           (fn-nntp-tokenize (hra-oct line)) fn-arena))
(bpr-lift pdt-x-run 2)
(defun pdt-x-ref (session line fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-nntp-command-pinned session *hra-archive* *hra-index* *hra-verdicts* *pdt-env-x*
                          (fn-nntp-tokenize (hra-oct line)) fn-arena))
(bpr-lift pdt-x-ref 2)

(defun pdt-x-agree (lines)
  (declare (xargs :verify-guards nil))
  (if (consp lines)
      (and (equal (in-arena-pdt-x-run *hra-payloads* *hra-session* (car lines))
                  (in-arena-pdt-x-ref *hra-payloads* *hra-session* (car lines)))
           (pdt-x-agree (cdr lines)))
    t))

; Positive witness: the generated dispatcher and fn-nntp-command-pinned
; agree on every line, including the special conditions' answers.
(assert-event (pdt-agree *pdt-lines*))
(assert-event (fn-nntp-xref-server *pdt-env-x*))
(assert-event (pdt-x-agree *pdt-lines*))
; With the server named, the Xref arms answer lines the blind environment's
; do not: the witnesses reach them.
(assert-event (not (equal (in-arena-pdt-x-run *hra-payloads* *hra-session* "OVER 1-5")
                          (pdt-reply *hra-session* "OVER 1-5"))))
(assert-event (not (equal (in-arena-pdt-x-run *hra-payloads* *hra-session* "HEAD 2")
                          (pdt-reply *hra-session* "HEAD 2"))))
(assert-event (equal (pdt-reply *hra-session* "ARTICLE 1") (hra-single "423 withdrawn")))
(assert-event (equal (pdt-reply *hra-session* "ARTICLE <r@example.invalid>")
                     (hra-single "430 article reclaimed")))
(assert-event (equal (pdt-reply *hra-session* "ARTICLE 4")
                     (hra-single "503 stored article framing unavailable")))
(assert-event (equal (pdt-reply *hra-session* "FROBNICATE")
                     (hra-single (fn-proto-text "(unrecognized)" :unknown))))
(assert-event (equal (pdt-reply *hra-session* "123")
                     (hra-single (fn-proto-text "(syntax)" :syntax))))
; ... and on a session with no projection: every archive row refuses 503.
(defconst *pdt-unprojected*
  (fn-nntp-make-session t (fn-nntp-session-group *hra-session*)
                        (fn-nntp-session-current *hra-session*) nil))
(assert-event (equal (pdt-reply *pdt-unprojected* "ARTICLE 1")
                     (hra-reply *pdt-unprojected* "ARTICLE 1")))
(assert-event (equal (pdt-reply *pdt-unprojected* "ARTICLE 1")
                     (fn-nntp-single *pdt-unprojected*
                                     "503 archive projection unavailable")))
(assert-event (equal (pdt-reply *pdt-unprojected* "XFNCATCHUP * 1-2 0 1-2")
                     (hra-reply *pdt-unprojected* "XFNCATCHUP * 1-2 0 1-2")))

; -----------------------------------------------------------------------------
; Mutation witnesses: a table whose :arms says another thing.

(defun pdt-with-arms (name arms rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (cons (if (and (consp (car rows)) (equal (car (car rows)) name))
                (cons name (append (list :arms arms) (cdr (car rows))))
              (car rows))
            (pdt-with-arms name arms (cdr rows)))
    nil))

(defun pdt-arms-of (name) (fn-proto-row-arms (fn-proto-row name *fn-proto-table*)))

(defmacro pdt-mutant (fname rows)
  `(make-event
    (list 'defun ',fname '(session archive index verdicts env tokens fn-arena)
          '(declare (xargs :stobjs fn-arena :verify-guards nil))
          (list 'let '((keyword (car tokens)) (args (cdr tokens)))
                (list* 'cond
                       '((not (fn-nntp-keyword-tokenp keyword))
                         (fn-nntp-single session (fn-proto-text "(syntax)" :syntax)))
                       (append (fn-proto-flat-clauses ,rows)
                               '((t (fn-nntp-single
                                     session (fn-proto-text "(unrecognized)" :unknown))))))))))

; ARTICLE without its first arm (the by-number withdrawn test).
(pdt-mutant pdt-mutant-1
            (pdt-with-arms "ARTICLE"
                           (cons (car (pdt-arms-of "ARTICLE")) (cddr (pdt-arms-of "ARTICLE")))
                           *fn-proto-table*))
; GROUP with its syntax arm first (a reordering).
(pdt-mutant pdt-mutant-2
            (pdt-with-arms "GROUP"
                           (list (car (pdt-arms-of "GROUP"))
                                 (list t (cadr (caddr (pdt-arms-of "GROUP"))))
                                 (cadr (pdt-arms-of "GROUP")))
                           *fn-proto-table*))

(defun pdt-m1-run (session line fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (pdt-mutant-1 session *hra-archive* *hra-index* *hra-verdicts* *hra-env*
                (fn-nntp-tokenize (hra-oct line)) fn-arena))
(bpr-lift pdt-m1-run 2)
(defun pdt-m2-run (session line fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (pdt-mutant-2 session *hra-archive* *hra-index* *hra-verdicts* *hra-env*
                (fn-nntp-tokenize (hra-oct line)) fn-arena))
(bpr-lift pdt-m2-run 2)

(defun pdt-mutant-reply (which line)
  (declare (xargs :verify-guards nil))
  (if (equal which 1)
      (in-arena-pdt-m1-run *hra-payloads* *hra-session* line)
    (in-arena-pdt-m2-run *hra-payloads* *hra-session* line)))

(assert-event (not (equal (pdt-mutant-reply 1 "ARTICLE 1") (hra-reply *hra-session* "ARTICLE 1"))))
(assert-event (not (equal (pdt-mutant-reply 2 "GROUP fn.mod.a")
                          (hra-reply *hra-session* "GROUP fn.mod.a"))))
; ... while the lines the mutation does not touch still agree.
(assert-event (equal (pdt-mutant-reply 1 "ARTICLE 2") (hra-reply *hra-session* "ARTICLE 2")))
(assert-event (equal (pdt-mutant-reply 2 "GROUP") (hra-reply *hra-session* "GROUP")))

; -----------------------------------------------------------------------------
; The generated command layer is the text lane host-lints wrote by hand.

(assert-event
 (equal (fn-proto-command-dispatch-term 'archive-call t *fn-proto-table*)
        '(let ((keyword (mbe :logic (car tokens) :exec (fn-ag-car tokens)))
               (args (mbe :logic (cdr tokens) :exec (fn-ag-cdr tokens))))
           (if (not (fn-nntp-keyword-tokenp keyword))
               (fn-nntp-single session (fn-proto-text "(syntax)" :syntax))
             (if (fn-nntp-keywordp keyword "XFNCATCHUP")
                 (if (fn-nntp-session-projected session)
                     (fn-cu-serve-reply session archive index args fn-arena)
                   (fn-nntp-single session (fn-proto-text * :no-projection)))
               (if (not (fn-nntp-archive-keywordp keyword))
                   (fn-nntp-session-command session env keyword args)
                 (if (fn-nntp-session-projected session)
                     archive-call
                   (fn-nntp-single session (fn-proto-text * :no-projection)))))))))
