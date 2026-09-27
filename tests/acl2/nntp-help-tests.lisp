; Teeth for PRF-194: HELP lists the served command table (books/nntp-help).
;
; The subject is fn-auth-step-pinned, the dispatcher books/served.lisp
; fn-served-dispatch calls for every framed command line (host/native/
; owner.lisp's socket read reaches it through fn-own-read and
; fn-served-step).  Per keystone (AGENTS.md, "Teeth ship with each
; keystone"): a reachable witness asserting every hypothesis and the whole
; conclusion; per hypothesis a `must-fail' with that hypothesis dropped and
; the keystone's hints kept, and beside it, where a served session can be
; put in that mode, a concrete value whose other hypotheses hold, whose
; dropped hypothesis fails, and whose conclusion fails.
;
; Every expected reply is assembled here from text written out of RFC 3977,
; never by calling the renderer under test.

(in-package "ACL2")
(include-book "../../books/nntp-help")
(include-book "std/testing/must-fail" :dir :system)

(defconst *nht-archive* (fn-initial-state '("fn.letters")))
(defconst *nht-obs* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *nht-config*
  (fn-inj-make-config t (fn-nntp-string-octets "fn.example.invalid")
                      (list (fn-nntp-string-octets "fn.letters")) 32768))
(defconst *nht-open* (fn-auth-make-config nil nil t nil))
(defconst *nht-s* (fn-auth-open-session *nht-archive* nil nil nil *nht-open* nil))
(assert-event (fn-auth-sessionp *nht-s*))

(defun nht-line (text) (fn-nntp-string-octets text))
(defun nht-step-under (as line config)
  (fn-auth-step-pinned as *nht-archive* nil nil config *nht-obs* *nht-obs*
                       (list :command line)))
(defun nht-step (as line) (nht-step-under as line *nht-config*))
(defun nht-effects (as text) (fn-post-result-effects (nht-step as (nht-line text))))
(defun nht-crlf-lines (texts)
  (if (consp texts)
      (append (fn-nntp-string-octets (car texts)) '(13 10)
              (nht-crlf-lines (cdr texts)))
    nil))
(defun nht-single (text)
  (list (list :reply (append (fn-nntp-string-octets text) '(13 10)))))
(defconst *nht-500* (nht-single "500 command not recognized"))

; HELP over the served step, RFC 3977 section 7.2: the 100 line, one line
; per table row, the terminating dot.
(assert-event
 (equal (nht-effects *nht-s* "HELP")
        (list (list :reply
                    (nht-crlf-lines
                     '("100 help text follows"
                       "CAPABILITIES HELP QUIT MODE DATE POST"
                       "AUTHINFO STARTTLS XREDEEM"
                       "GROUP LISTGROUP LIST NEXT LAST NEWGROUPS NEWNEWS"
                       "ARTICLE HEAD BODY STAT"
                       "OVER XOVER HDR XHDR XPAT"
                       "IHAVE CHECK TAKETHIS"
                       "."))))))

; The converse the keystone does not state (PKT-571), checked by evaluation:
; every keyword HELP lists draws some reply other than 500 from the served
; step, alone on the line, on a served session.
(defconst *nht-listed*
  '("CAPABILITIES" "HELP" "QUIT" "MODE" "DATE" "POST" "AUTHINFO" "STARTTLS"
    "XREDEEM" "GROUP" "LISTGROUP" "LIST" "NEXT" "LAST" "NEWGROUPS" "NEWNEWS"
    "ARTICLE" "HEAD" "BODY" "STAT" "OVER" "XOVER" "HDR" "XHDR" "XPAT"
    "IHAVE" "CHECK" "TAKETHIS"))
(defun nht-all-served (keywords)
  (if (consp keywords)
      (and (fn-nntp-served-keywordp (nht-line (car keywords)))
           (consp (nht-effects *nht-s* (car keywords)))
           (not (equal (nht-effects *nht-s* (car keywords)) *nht-500*))
           (nht-all-served (cdr keywords)))
    t))
(assert-event (nht-all-served *nht-listed*))
; The list is the whole table: 28 keywords, and a lower-case spelling is
; the same keyword (RFC 3977 section 3.1: case-insensitive).
(assert-event (equal (len *nht-listed*) 28))
(defun nht-flatten (rows)
  (if (consp rows) (append (car rows) (nht-flatten (cdr rows))) nil))
(assert-event (equal (nht-flatten *fn-nntp-served-command-table*) *nht-listed*))
(assert-event (fn-nntp-served-keywordp (nht-line "xredeem")))

; -----------------------------------------------------------------------------
; KEYSTONE fn-auth-step-pinned-answers-500-to-a-keyword-help-does-not-list
;
; The reachable witness.  XPATH is RFC 2980 section 2.10, a real legacy
; verb fn refuses to implement (it would publish storage filenames); it is
; not in the table.
(defconst *nht-xpath* (nht-line "XPATH <a@b.invalid>"))
(defun nht-antecedent-under (as line config)
  (and (fn-auth-sessionp as)
       (not (fn-auth-session-handshakingp as))
       (not (fn-peer-session-transfer (fn-auth-session-base as)))
       (not (fn-post-session-awaiting (fn-auth-post-session as)))
       (equal (fn-nntp-session-openp (fn-auth-reader-session as)) t)
       (fn-nntp-command-inputp line)
       (fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))
       (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
       (not (fn-nntp-served-keywordp (car (fn-nntp-tokenize line))))
       (fn-auth-selection-in-viewp as config)))
(defun nht-antecedent (as line) (nht-antecedent-under as line *nht-config*))
(defun nht-conclusion-under (as line config)
  (let ((r (nht-step-under as line config)))
    (and (equal (fn-post-result-effects r) *nht-500*)
         (null (fn-post-result-submission r))
         (equal (fn-post-result-session r) as))))
(defun nht-conclusion (as line) (nht-conclusion-under as line *nht-config*))
(assert-event (nht-antecedent *nht-s* *nht-xpath*))
(assert-event (nht-conclusion *nht-s* *nht-xpath*))
; Not degenerate: the conclusion's 500 line is the one the witness wrote.
(assert-event (equal (fn-auth-single *nht-s* "500 command not recognized")
                     *nht-500*))

; Hypothesis-removal witnesses.  Each: every retained hypothesis holds, the
; dropped one fails, the conclusion fails.
(defun nht-retained-but-under (k as line config)
  (and (or (equal k 1) (fn-auth-sessionp as))
       (or (equal k 2) (not (fn-auth-session-handshakingp as)))
       (or (equal k 3) (not (fn-peer-session-transfer (fn-auth-session-base as))))
       (or (equal k 4) (not (fn-post-session-awaiting (fn-auth-post-session as))))
       (or (equal k 5) (equal (fn-nntp-session-openp (fn-auth-reader-session as)) t))
       (or (equal k 6) (fn-nntp-command-inputp line))
       (or (equal k 7) (fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line))))
       (or (equal k 8) (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line)))
       (or (equal k 9) (not (fn-nntp-served-keywordp (car (fn-nntp-tokenize line)))))
       (or (equal k 10) (fn-auth-selection-in-viewp as config))
       (not (nht-antecedent-under as line config))
       (not (nht-conclusion-under as line config))))
(defun nht-retained-but (k as line) (nht-retained-but-under k as line *nht-config*))

; (10) the selection is in the session's view (PRF-222): a session that
; selected fn.letters and whose rule (the anonymous row, read fn.other)
; does not read it is deselected by its next delegated command -- a change
; of state, so "changes nothing" needs the selection in view.
(defconst *nht-ruled-config*
  (fn-inj-make-config-full t (fn-nntp-string-octets "fn.example.invalid")
                           (list (fn-nntp-string-octets "fn.letters")) 32768
                           (list nil nil nil (list (list "" "fn.other" "*" 3)))
                           nil))
(defconst *nht-selected*
  (fn-post-result-session (nht-step *nht-s* (nht-line "GROUP fn.letters"))))
(assert-event (fn-nntp-session-group (fn-auth-reader-session *nht-selected*)))
(assert-event (fn-auth-access-read *nht-selected* *nht-ruled-config*))
(assert-event (nht-retained-but-under 10 *nht-selected* *nht-xpath* *nht-ruled-config*))
; and in view under the connection's own (unruled) configuration:
(assert-event (nht-antecedent *nht-selected* *nht-xpath*))
(assert-event (nht-conclusion *nht-selected* *nht-xpath*))

; (2) handshaking: STARTTLS's 382 leaves the session handshaking; nothing
; is served until the handshake ends.
(defconst *nht-handshaking*
  (fn-auth-make-session (fn-auth-session-base *nht-s*)
                        (fn-auth-session-config *nht-s*) nil nil nil t))
(assert-event (nht-retained-but 2 *nht-handshaking* *nht-xpath*))
(assert-event (null (fn-post-result-effects (nht-step *nht-handshaking* *nht-xpath*))))
; (4) awaiting a POST body: after 340 the next line is article data.
(defconst *nht-posting*
  (fn-post-result-session (nht-step *nht-s* (nht-line "POST"))))
(assert-event (nht-retained-but 4 *nht-posting* *nht-xpath*))
; (5) closed: after QUIT the session answers nothing.
(defconst *nht-closed*
  (fn-post-result-session (nht-step *nht-s* (nht-line "QUIT"))))
(assert-event (nht-retained-but 5 *nht-closed* *nht-xpath*))
(assert-event (null (fn-post-result-effects (nht-step *nht-closed* *nht-xpath*))))
; (6) not a command line: a line past RFC 3977 section 3.1's 512 octets,
; each argument within its 497.
(defconst *nht-long*
  (append (nht-line "XPATH ") (make-list 300 :initial-element 97)
          '(32) (make-list 300 :initial-element 97)))
(assert-event (nht-retained-but 6 *nht-s* *nht-long*))
; (7) not a keyword token: a keyword must begin with a letter (section 9.8).
(defconst *nht-digit* (nht-line "9XPATH"))
(assert-event (nht-retained-but 7 *nht-s* *nht-digit*))
(assert-event (equal (fn-post-result-effects (nht-step *nht-s* *nht-digit*))
                     (nht-single "501 syntax error")))
; (8) an argument past section 3.1's 497 octets, the line within 512.
(defconst *nht-arg*
  (append (nht-line "XPATH ") (make-list 498 :initial-element 97)))
(assert-event (nht-retained-but 8 *nht-s* *nht-arg*))
; (9) a listed keyword: XHDR is served (221 or a refusal), not 500.
(defconst *nht-xhdr* (nht-line "XHDR subject"))
(assert-event (nht-retained-but 9 *nht-s* *nht-xhdr*))
; (1) and (3) have no served-session value: a non-session is no connection,
; and a transit article is awaited only on a peer connection mid-IHAVE;
; their teeth are the `must-fail's below.

(must-fail
(defthm nht-without-sessionp
  (implies (and 
                (not (fn-auth-session-handshakingp as))
                (not (fn-peer-session-transfer (fn-auth-session-base as)))
                (not (fn-post-session-awaiting (fn-auth-post-session as)))
                (equal (fn-nntp-session-openp (fn-auth-reader-session as)) t)
                (fn-nntp-command-inputp line)
                (fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (not (fn-nntp-served-keywordp (car (fn-nntp-tokenize line))))
                (fn-auth-selection-in-viewp as config))
           (and (equal (fn-post-result-effects
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       (fn-auth-single as "500 command not recognized"))
                (null (fn-post-result-submission
                       (fn-auth-step-pinned as archive index verdicts config
                                            observation injection
                                            (list :command line))))
                (equal (fn-post-result-session
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       as)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step-pinned fn-auth-command fn-auth-gatedp
                            fn-auth-restricted-keywordp fn-auth-tls-eventp
                            fn-auth-redeem-eventp
                            fn-auth-delegate-pinned fn-peer-step-pinned
                            fn-peer-command fn-peer-delegate-pinned
                            fn-nntp-post-step-pinned fn-nntp-step-pinned
                            fn-nntp-command-pinned fn-nntp-archive-keywordp
                            fn-nntp-session-command fn-auth-single
                            fn-nntp-single
                            fn-help-inj-nth-is-nth fn-help-six-list-rebuild fn-help-nth-of-a-constant fn-help-nth-0 fn-help-rebuild-post fn-help-rebuild-peer fn-help-rebuild-auth)
                           (fn-nntp-keywordp fn-nntp-tokenize
                            fn-nntp-command-inputp fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp
                            fn-auth-sessionp fn-peer-sessionp fn-post-sessionp
                            fn-auth-view-archive fn-auth-view-index
                            fn-auth-view-config fn-auth-selection-in-viewp))
           :use ((:instance fn-auth-view-session-when-selection-in-view)
                 (:instance fn-auth-sessionp (x as))
                 (:instance fn-peer-sessionp (x (fn-auth-session-base as)))
                 (:instance fn-post-sessionp (x (fn-auth-post-session as))))))))

(must-fail
(defthm nht-without-handshaking
  (implies (and (fn-auth-sessionp as)
                (not (fn-peer-session-transfer (fn-auth-session-base as)))
                (not (fn-post-session-awaiting (fn-auth-post-session as)))
                (equal (fn-nntp-session-openp (fn-auth-reader-session as)) t)
                (fn-nntp-command-inputp line)
                (fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (not (fn-nntp-served-keywordp (car (fn-nntp-tokenize line))))
                (fn-auth-selection-in-viewp as config))
           (and (equal (fn-post-result-effects
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       (fn-auth-single as "500 command not recognized"))
                (null (fn-post-result-submission
                       (fn-auth-step-pinned as archive index verdicts config
                                            observation injection
                                            (list :command line))))
                (equal (fn-post-result-session
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       as)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step-pinned fn-auth-command fn-auth-gatedp
                            fn-auth-restricted-keywordp fn-auth-tls-eventp
                            fn-auth-redeem-eventp
                            fn-auth-delegate-pinned fn-peer-step-pinned
                            fn-peer-command fn-peer-delegate-pinned
                            fn-nntp-post-step-pinned fn-nntp-step-pinned
                            fn-nntp-command-pinned fn-nntp-archive-keywordp
                            fn-nntp-session-command fn-auth-single
                            fn-nntp-single
                            fn-help-inj-nth-is-nth fn-help-six-list-rebuild fn-help-nth-of-a-constant fn-help-nth-0 fn-help-rebuild-post fn-help-rebuild-peer fn-help-rebuild-auth)
                           (fn-nntp-keywordp fn-nntp-tokenize
                            fn-nntp-command-inputp fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp
                            fn-auth-sessionp fn-peer-sessionp fn-post-sessionp
                            fn-auth-view-archive fn-auth-view-index
                            fn-auth-view-config fn-auth-selection-in-viewp))
           :use ((:instance fn-auth-view-session-when-selection-in-view)
                 (:instance fn-auth-sessionp (x as))
                 (:instance fn-peer-sessionp (x (fn-auth-session-base as)))
                 (:instance fn-post-sessionp (x (fn-auth-post-session as))))))))

(must-fail
(defthm nht-without-transfer
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (not (fn-post-session-awaiting (fn-auth-post-session as)))
                (equal (fn-nntp-session-openp (fn-auth-reader-session as)) t)
                (fn-nntp-command-inputp line)
                (fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (not (fn-nntp-served-keywordp (car (fn-nntp-tokenize line))))
                (fn-auth-selection-in-viewp as config))
           (and (equal (fn-post-result-effects
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       (fn-auth-single as "500 command not recognized"))
                (null (fn-post-result-submission
                       (fn-auth-step-pinned as archive index verdicts config
                                            observation injection
                                            (list :command line))))
                (equal (fn-post-result-session
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       as)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step-pinned fn-auth-command fn-auth-gatedp
                            fn-auth-restricted-keywordp fn-auth-tls-eventp
                            fn-auth-redeem-eventp
                            fn-auth-delegate-pinned fn-peer-step-pinned
                            fn-peer-command fn-peer-delegate-pinned
                            fn-nntp-post-step-pinned fn-nntp-step-pinned
                            fn-nntp-command-pinned fn-nntp-archive-keywordp
                            fn-nntp-session-command fn-auth-single
                            fn-nntp-single
                            fn-help-inj-nth-is-nth fn-help-six-list-rebuild fn-help-nth-of-a-constant fn-help-nth-0 fn-help-rebuild-post fn-help-rebuild-peer fn-help-rebuild-auth)
                           (fn-nntp-keywordp fn-nntp-tokenize
                            fn-nntp-command-inputp fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp
                            fn-auth-sessionp fn-peer-sessionp fn-post-sessionp
                            fn-auth-view-archive fn-auth-view-index
                            fn-auth-view-config fn-auth-selection-in-viewp))
           :use ((:instance fn-auth-view-session-when-selection-in-view)
                 (:instance fn-auth-sessionp (x as))
                 (:instance fn-peer-sessionp (x (fn-auth-session-base as)))
                 (:instance fn-post-sessionp (x (fn-auth-post-session as))))))))

(must-fail
(defthm nht-without-awaiting
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (not (fn-peer-session-transfer (fn-auth-session-base as)))
                (equal (fn-nntp-session-openp (fn-auth-reader-session as)) t)
                (fn-nntp-command-inputp line)
                (fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (not (fn-nntp-served-keywordp (car (fn-nntp-tokenize line))))
                (fn-auth-selection-in-viewp as config))
           (and (equal (fn-post-result-effects
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       (fn-auth-single as "500 command not recognized"))
                (null (fn-post-result-submission
                       (fn-auth-step-pinned as archive index verdicts config
                                            observation injection
                                            (list :command line))))
                (equal (fn-post-result-session
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       as)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step-pinned fn-auth-command fn-auth-gatedp
                            fn-auth-restricted-keywordp fn-auth-tls-eventp
                            fn-auth-redeem-eventp
                            fn-auth-delegate-pinned fn-peer-step-pinned
                            fn-peer-command fn-peer-delegate-pinned
                            fn-nntp-post-step-pinned fn-nntp-step-pinned
                            fn-nntp-command-pinned fn-nntp-archive-keywordp
                            fn-nntp-session-command fn-auth-single
                            fn-nntp-single
                            fn-help-inj-nth-is-nth fn-help-six-list-rebuild fn-help-nth-of-a-constant fn-help-nth-0 fn-help-rebuild-post fn-help-rebuild-peer fn-help-rebuild-auth)
                           (fn-nntp-keywordp fn-nntp-tokenize
                            fn-nntp-command-inputp fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp
                            fn-auth-sessionp fn-peer-sessionp fn-post-sessionp
                            fn-auth-view-archive fn-auth-view-index
                            fn-auth-view-config fn-auth-selection-in-viewp))
           :use ((:instance fn-auth-view-session-when-selection-in-view)
                 (:instance fn-auth-sessionp (x as))
                 (:instance fn-peer-sessionp (x (fn-auth-session-base as)))
                 (:instance fn-post-sessionp (x (fn-auth-post-session as))))))))

(must-fail
(defthm nht-without-open
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (not (fn-peer-session-transfer (fn-auth-session-base as)))
                (not (fn-post-session-awaiting (fn-auth-post-session as)))
                (fn-nntp-command-inputp line)
                (fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (not (fn-nntp-served-keywordp (car (fn-nntp-tokenize line))))
                (fn-auth-selection-in-viewp as config))
           (and (equal (fn-post-result-effects
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       (fn-auth-single as "500 command not recognized"))
                (null (fn-post-result-submission
                       (fn-auth-step-pinned as archive index verdicts config
                                            observation injection
                                            (list :command line))))
                (equal (fn-post-result-session
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       as)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step-pinned fn-auth-command fn-auth-gatedp
                            fn-auth-restricted-keywordp fn-auth-tls-eventp
                            fn-auth-redeem-eventp
                            fn-auth-delegate-pinned fn-peer-step-pinned
                            fn-peer-command fn-peer-delegate-pinned
                            fn-nntp-post-step-pinned fn-nntp-step-pinned
                            fn-nntp-command-pinned fn-nntp-archive-keywordp
                            fn-nntp-session-command fn-auth-single
                            fn-nntp-single
                            fn-help-inj-nth-is-nth fn-help-six-list-rebuild fn-help-nth-of-a-constant fn-help-nth-0 fn-help-rebuild-post fn-help-rebuild-peer fn-help-rebuild-auth)
                           (fn-nntp-keywordp fn-nntp-tokenize
                            fn-nntp-command-inputp fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp
                            fn-auth-sessionp fn-peer-sessionp fn-post-sessionp
                            fn-auth-view-archive fn-auth-view-index
                            fn-auth-view-config fn-auth-selection-in-viewp))
           :use ((:instance fn-auth-view-session-when-selection-in-view)
                 (:instance fn-auth-sessionp (x as))
                 (:instance fn-peer-sessionp (x (fn-auth-session-base as)))
                 (:instance fn-post-sessionp (x (fn-auth-post-session as))))))))

(must-fail
(defthm nht-without-command-input
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (not (fn-peer-session-transfer (fn-auth-session-base as)))
                (not (fn-post-session-awaiting (fn-auth-post-session as)))
                (equal (fn-nntp-session-openp (fn-auth-reader-session as)) t)
                (fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (not (fn-nntp-served-keywordp (car (fn-nntp-tokenize line))))
                (fn-auth-selection-in-viewp as config))
           (and (equal (fn-post-result-effects
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       (fn-auth-single as "500 command not recognized"))
                (null (fn-post-result-submission
                       (fn-auth-step-pinned as archive index verdicts config
                                            observation injection
                                            (list :command line))))
                (equal (fn-post-result-session
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       as)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step-pinned fn-auth-command fn-auth-gatedp
                            fn-auth-restricted-keywordp fn-auth-tls-eventp
                            fn-auth-redeem-eventp
                            fn-auth-delegate-pinned fn-peer-step-pinned
                            fn-peer-command fn-peer-delegate-pinned
                            fn-nntp-post-step-pinned fn-nntp-step-pinned
                            fn-nntp-command-pinned fn-nntp-archive-keywordp
                            fn-nntp-session-command fn-auth-single
                            fn-nntp-single
                            fn-help-inj-nth-is-nth fn-help-six-list-rebuild fn-help-nth-of-a-constant fn-help-nth-0 fn-help-rebuild-post fn-help-rebuild-peer fn-help-rebuild-auth)
                           (fn-nntp-keywordp fn-nntp-tokenize
                            fn-nntp-command-inputp fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp
                            fn-auth-sessionp fn-peer-sessionp fn-post-sessionp
                            fn-auth-view-archive fn-auth-view-index
                            fn-auth-view-config fn-auth-selection-in-viewp))
           :use ((:instance fn-auth-view-session-when-selection-in-view)
                 (:instance fn-auth-sessionp (x as))
                 (:instance fn-peer-sessionp (x (fn-auth-session-base as)))
                 (:instance fn-post-sessionp (x (fn-auth-post-session as))))))))

(must-fail
(defthm nht-without-keyword-token
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (not (fn-peer-session-transfer (fn-auth-session-base as)))
                (not (fn-post-session-awaiting (fn-auth-post-session as)))
                (equal (fn-nntp-session-openp (fn-auth-reader-session as)) t)
                (fn-nntp-command-inputp line)
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (not (fn-nntp-served-keywordp (car (fn-nntp-tokenize line))))
                (fn-auth-selection-in-viewp as config))
           (and (equal (fn-post-result-effects
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       (fn-auth-single as "500 command not recognized"))
                (null (fn-post-result-submission
                       (fn-auth-step-pinned as archive index verdicts config
                                            observation injection
                                            (list :command line))))
                (equal (fn-post-result-session
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       as)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step-pinned fn-auth-command fn-auth-gatedp
                            fn-auth-restricted-keywordp fn-auth-tls-eventp
                            fn-auth-redeem-eventp
                            fn-auth-delegate-pinned fn-peer-step-pinned
                            fn-peer-command fn-peer-delegate-pinned
                            fn-nntp-post-step-pinned fn-nntp-step-pinned
                            fn-nntp-command-pinned fn-nntp-archive-keywordp
                            fn-nntp-session-command fn-auth-single
                            fn-nntp-single
                            fn-help-inj-nth-is-nth fn-help-six-list-rebuild fn-help-nth-of-a-constant fn-help-nth-0 fn-help-rebuild-post fn-help-rebuild-peer fn-help-rebuild-auth)
                           (fn-nntp-keywordp fn-nntp-tokenize
                            fn-nntp-command-inputp fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp
                            fn-auth-sessionp fn-peer-sessionp fn-post-sessionp
                            fn-auth-view-archive fn-auth-view-index
                            fn-auth-view-config fn-auth-selection-in-viewp))
           :use ((:instance fn-auth-view-session-when-selection-in-view)
                 (:instance fn-auth-sessionp (x as))
                 (:instance fn-peer-sessionp (x (fn-auth-session-base as)))
                 (:instance fn-post-sessionp (x (fn-auth-post-session as))))))))

(must-fail
(defthm nht-without-arguments
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (not (fn-peer-session-transfer (fn-auth-session-base as)))
                (not (fn-post-session-awaiting (fn-auth-post-session as)))
                (equal (fn-nntp-session-openp (fn-auth-reader-session as)) t)
                (fn-nntp-command-inputp line)
                (fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))
                (not (fn-nntp-served-keywordp (car (fn-nntp-tokenize line))))
                (fn-auth-selection-in-viewp as config))
           (and (equal (fn-post-result-effects
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       (fn-auth-single as "500 command not recognized"))
                (null (fn-post-result-submission
                       (fn-auth-step-pinned as archive index verdicts config
                                            observation injection
                                            (list :command line))))
                (equal (fn-post-result-session
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       as)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step-pinned fn-auth-command fn-auth-gatedp
                            fn-auth-restricted-keywordp fn-auth-tls-eventp
                            fn-auth-redeem-eventp
                            fn-auth-delegate-pinned fn-peer-step-pinned
                            fn-peer-command fn-peer-delegate-pinned
                            fn-nntp-post-step-pinned fn-nntp-step-pinned
                            fn-nntp-command-pinned fn-nntp-archive-keywordp
                            fn-nntp-session-command fn-auth-single
                            fn-nntp-single
                            fn-help-inj-nth-is-nth fn-help-six-list-rebuild fn-help-nth-of-a-constant fn-help-nth-0 fn-help-rebuild-post fn-help-rebuild-peer fn-help-rebuild-auth)
                           (fn-nntp-keywordp fn-nntp-tokenize
                            fn-nntp-command-inputp fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp
                            fn-auth-sessionp fn-peer-sessionp fn-post-sessionp
                            fn-auth-view-archive fn-auth-view-index
                            fn-auth-view-config fn-auth-selection-in-viewp))
           :use ((:instance fn-auth-view-session-when-selection-in-view)
                 (:instance fn-auth-sessionp (x as))
                 (:instance fn-peer-sessionp (x (fn-auth-session-base as)))
                 (:instance fn-post-sessionp (x (fn-auth-post-session as))))))))

(must-fail
; the prover's search without this hypothesis visits every served keyword;
; bound it (the ground witness above is the counterexample).
(with-prover-step-limit 300000
(defthm nht-without-unlisted
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (not (fn-peer-session-transfer (fn-auth-session-base as)))
                (not (fn-post-session-awaiting (fn-auth-post-session as)))
                (equal (fn-nntp-session-openp (fn-auth-reader-session as)) t)
                (fn-nntp-command-inputp line)
                (fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                )
           (and (equal (fn-post-result-effects
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       (fn-auth-single as "500 command not recognized"))
                (null (fn-post-result-submission
                       (fn-auth-step-pinned as archive index verdicts config
                                            observation injection
                                            (list :command line))))
                (equal (fn-post-result-session
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       as)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step-pinned fn-auth-command fn-auth-gatedp
                            fn-auth-restricted-keywordp fn-auth-tls-eventp
                            fn-auth-redeem-eventp
                            fn-auth-delegate-pinned fn-peer-step-pinned
                            fn-peer-command fn-peer-delegate-pinned
                            fn-nntp-post-step-pinned fn-nntp-step-pinned
                            fn-nntp-command-pinned fn-nntp-archive-keywordp
                            fn-nntp-session-command fn-auth-single
                            fn-nntp-single
                            fn-help-inj-nth-is-nth fn-help-six-list-rebuild fn-help-nth-of-a-constant fn-help-nth-0 fn-help-rebuild-post fn-help-rebuild-peer fn-help-rebuild-auth)
                           (fn-nntp-keywordp fn-nntp-tokenize
                            fn-nntp-command-inputp fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp
                            fn-auth-sessionp fn-peer-sessionp fn-post-sessionp
                            fn-auth-view-archive fn-auth-view-index
                            fn-auth-view-config fn-auth-selection-in-viewp))
           :use ((:instance fn-auth-view-session-when-selection-in-view)
                 (:instance fn-auth-sessionp (x as))
                 (:instance fn-peer-sessionp (x (fn-auth-session-base as)))
                 (:instance fn-post-sessionp (x (fn-auth-post-session as)))))))))

; (10) without the selection in view: a ruled session selected outside its
; view is deselected (the ground case above).
(must-fail
(defthm nht-without-selection-in-view
  (implies (and (fn-auth-sessionp as)
                (not (fn-auth-session-handshakingp as))
                (not (fn-peer-session-transfer (fn-auth-session-base as)))
                (not (fn-post-session-awaiting (fn-auth-post-session as)))
                (equal (fn-nntp-session-openp (fn-auth-reader-session as)) t)
                (fn-nntp-command-inputp line)
                (fn-nntp-keyword-tokenp (car (fn-nntp-tokenize line)))
                (fn-nntp-command-arguments-at-mostp (fn-nntp-tokenize line))
                (not (fn-nntp-served-keywordp (car (fn-nntp-tokenize line)))))
           (and (equal (fn-post-result-effects
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       (fn-auth-single as "500 command not recognized"))
                (null (fn-post-result-submission
                       (fn-auth-step-pinned as archive index verdicts config
                                            observation injection
                                            (list :command line))))
                (equal (fn-post-result-session
                        (fn-auth-step-pinned as archive index verdicts config
                                             observation injection
                                             (list :command line)))
                       as)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-auth-step-pinned fn-auth-command fn-auth-gatedp
                            fn-auth-restricted-keywordp fn-auth-tls-eventp
                            fn-auth-redeem-eventp
                            fn-auth-delegate-pinned fn-peer-step-pinned
                            fn-peer-command fn-peer-delegate-pinned
                            fn-nntp-post-step-pinned fn-nntp-step-pinned
                            fn-nntp-command-pinned fn-nntp-archive-keywordp
                            fn-nntp-session-command fn-auth-single
                            fn-nntp-single)
                           (fn-nntp-keywordp fn-nntp-tokenize
                            fn-nntp-command-inputp fn-nntp-keyword-tokenp
                            fn-nntp-command-arguments-at-mostp
                            fn-auth-sessionp fn-peer-sessionp fn-post-sessionp
                            fn-auth-view-archive fn-auth-view-index
                            fn-auth-view-config fn-auth-selection-in-viewp))
           :use ((:instance fn-auth-sessionp (x as))
                 (:instance fn-peer-sessionp (x (fn-auth-session-base as)))
                 (:instance fn-post-sessionp (x (fn-auth-post-session as))))))))
