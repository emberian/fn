; Expected transcripts for the legacy reader commands: XOVER (RFC 2980 §2.8),
; XHDR (§2.6), HDR and LIST HEADERS (RFC 3977 §§8.5/8.6), LIST ACTIVE.TIMES
; (§7.6.4 / RFC 2980 §2.1.3), LIST NEWSGROUPS (§7.6.6) and HELP (§7.2).
;
; Every expected reply below is assembled by `lg-block'/`lg-single' from text
; written out of the RFC, never by calling the response builder under test:
; those two helpers append the initial line, each block line and the
; terminating "." with their own CRLFs and perform no dot-stuffing, so a reply
; that needed stuffing would fail here rather than pass by construction.  The
; same transcripts are written independently as ASCII in tests/test_reader.py
; and driven over a real socket there.
(in-package "ACL2")
(include-book "../../books/nntp-effects")
(include-book "std/testing/must-fail" :dir :system)

(local (in-theory (enable fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary
                          fn-nntp-projection-vocabulary
                          fn-nntp-responses-vocabulary fn-nntp-vocabulary)))

(defconst *lg-groups* '("fn.letters" "fn.empty"))
(defconst *lg-id* "<Case@Id.invalid>")
; Message-ID: <Case@Id.invalid> CRLF Subject: Test CRLF CRLF Hello CRLF .dot CRLF
(defconst *lg-payload*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 67 97 115 101 64 73 100 46 105
    110 118 97 108 105 100 62 13 10 83 117 98 106 101 99 116 58 32 84 101 115
    116 13 10 13 10 72 101 108 108 111 13 10 46 100 111 116 13 10))
(defconst *lg-archive*
  (fn-accept-complete
   (fn-accept-prepare (fn-initial-state *lg-groups*) 1 *lg-id* *lg-payload*
                      '("fn.letters"))
   0 1 :durable))
(assert-event (fn-nntp-projectionp *lg-archive*))
; The two metadata items the overview line and HDR :bytes/:lines both report.
(assert-event (equal (len *lg-payload*) 61))
(assert-event (equal (fn-nov-body-line-count *lg-payload*) 2))

(defconst *lg-blind-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *lg-obs* (fn-clock-observation 1000 843136496000 1000 t))
; fn.empty was created at 2025-09-21T00:00:00Z: 811728000000 DTN milliseconds,
; which is 1758412800 seconds after 1970-01-01 (811728000 + 946684800).
(defconst *lg-facts*
  (list (fn-nntp-group-fact "fn.empty" 811728000000 *lg-blind-obs*)))
(defconst *lg-env* (fn-nntp-env *lg-obs* *lg-facts* nil))
(defconst *lg-empty-env* (fn-nntp-env *lg-obs* nil nil))
(assert-event (fn-nntp-envp *lg-env*))
(assert-event (equal (fn-nntp-dtn-unix-seconds 811728000000) 1758412800))

(defconst *lg-session0* (fn-nntp-open-session *lg-archive*))
(defun lg-step (session env text)
  (fn-nntp-step session *lg-archive* env
                (list :command (fn-nntp-string-octets text))))
(defconst *lg-session*
  (fn-nntp-result-session (lg-step *lg-session0* *lg-env* "GROUP fn.letters")))

; The expected-reply assembler.  Independent of fn-nntp-multi: it writes its
; own CRLFs and never stuffs.
(defun lg-lines (texts)
  (if (consp texts)
      (append (fn-nntp-string-octets (car texts)) '(13 10) (lg-lines (cdr texts)))
    nil))
(defun lg-block (initial lines)
  (list (list :reply (append (fn-nntp-string-octets initial) '(13 10)
                             (lg-lines lines) '(46 13 10)))))
(defun lg-single (text)
  (list (list :reply (append (fn-nntp-string-octets text) '(13 10)))))
(defmacro lg-reply (env text)
  `(fn-nntp-result-effects (lg-step *lg-session* ,env ,text)))

; The one overview line this archive renders, written field by field: number,
; subject, from, date, message-id, references, bytes, lines, TAB separated
; (RFC 3977 §8.3.2).  From, Date and References are absent from the article,
; so three fields are empty.
(defun lg-over-line (number)
  (append (fn-nntp-string-octets number) '(9)
          (fn-nntp-string-octets "Test") '(9) '(9) '(9)
          (fn-nntp-string-octets "<Case@Id.invalid>") '(9) '(9)
          (fn-nntp-string-octets "61") '(9) (fn-nntp-string-octets "2")))
(defun lg-over-block (number)
  (list (list :reply (append
                      (fn-nntp-string-octets "224 overview information follows")
                      '(13 10) (lg-over-line number) '(13 10) '(46 13 10)))))

; -----------------------------------------------------------------------------
; XOVER (RFC 2980 §2.8): the same 224 block OVER renders

(assert-event (equal (lg-reply *lg-env* "XOVER") (lg-over-block "1")))
(assert-event (equal (lg-reply *lg-env* "XOVER 1-") (lg-over-block "1")))
(assert-event (equal (lg-reply *lg-env* "XOVER 1")
                     (lg-reply *lg-env* "OVER 1")))
; §2.8.1 assigns 420 where RFC 3977 §8.3.1 assigns 423, and defines no
; message-id form, so XOVER with one is a syntax error.
(assert-event (equal (lg-reply *lg-env* "XOVER 5-2")
                     (lg-single "420 no article(s) selected")))
(assert-event (equal (lg-reply *lg-env* "OVER 5-2")
                     (lg-single "423 no articles in that range")))
(assert-event (equal (lg-reply *lg-env* "XOVER <Case@Id.invalid>")
                     (lg-single "501 syntax error")))
(assert-event (equal (fn-nntp-result-effects
                      (lg-step *lg-session0* *lg-env* "XOVER 1-"))
                     (lg-single "412 no newsgroup selected")))

; -----------------------------------------------------------------------------
; HDR (RFC 3977 §8.5) and XHDR (RFC 2980 §2.6)

(assert-event (equal (lg-reply *lg-env* "HDR subject 1")
                     (lg-block "225 headers follow" '("1 Test"))))
(assert-event (equal (lg-reply *lg-env* "HDR message-id 1")
                     (lg-block "225 headers follow"
                               '("1 <Case@Id.invalid>"))))
; §8.5.2: a field the article does not carry renders with an empty content
; portion; the space after the number is retained.
(assert-event (equal (lg-reply *lg-env* "HDR from 1")
                     (lg-block "225 headers follow" '("1 "))))
(assert-event (equal (lg-reply *lg-env* "HDR :bytes 1")
                     (lg-block "225 headers follow" '("1 61"))))
(assert-event (equal (lg-reply *lg-env* "HDR :lines 1")
                     (lg-block "225 headers follow" '("1 2"))))
; §8.5.2: the message-id form labels its line with zero; §2.6 labels it with
; the message-id itself, and its initial line is 221.
(assert-event (equal (lg-reply *lg-env* "HDR subject <Case@Id.invalid>")
                     (lg-block "225 headers follow" '("0 Test"))))
(assert-event (equal (lg-reply *lg-env* "XHDR subject <Case@Id.invalid>")
                     (lg-block "221 header follows"
                               '("<Case@Id.invalid> Test"))))
(assert-event (equal (lg-reply *lg-env* "XHDR subject 1")
                     (lg-block "221 header follows" '("1 Test"))))
(assert-event (equal (lg-reply *lg-env* "HDR subject 5-2")
                     (lg-single "423 no articles in that range")))
(assert-event (equal (lg-reply *lg-env* "XHDR subject 5-2")
                     (lg-single "420 no article(s) selected")))
(assert-event (equal (lg-reply *lg-env* "HDR subject <absent@x.invalid>")
                     (lg-single "430 no article with that message-id")))
(assert-event (equal (lg-reply *lg-env* "HDR") (lg-single "501 syntax error")))
; A field name carrying a colon that is not a metadata item is not a header
; name (RFC 5536 §2.2), so it is refused rather than looked up.
(assert-event (equal (lg-reply *lg-env* "HDR sub:ject 1")
                     (lg-single "501 syntax error")))

; -----------------------------------------------------------------------------
; The LIST variants

(assert-event (equal (lg-reply *lg-env* "LIST HEADERS")
                     (lg-block "215 field list follows"
                               '(":" ":bytes" ":lines"))))
(assert-event (equal (lg-reply *lg-env* "LIST HEADERS MSGID")
                     (lg-reply *lg-env* "LIST HEADERS")))
; §7.6.6: name, TAB, description.  fn holds no description, so the second
; field is the fixed marker, the same for every group.
(assert-event
 (equal (lg-reply *lg-env* "LIST NEWSGROUPS")
        (list (list :reply
                    (append (fn-nntp-string-octets
                             "215 list of newsgroups follows") '(13 10)
                            (fn-nntp-string-octets "fn.letters") '(9)
                            (fn-nntp-string-octets "(no description)") '(13 10)
                            (fn-nntp-string-octets "fn.empty") '(9)
                            (fn-nntp-string-octets "(no description)") '(13 10)
                            '(46 13 10))))))
; §7.6.4: name, creation seconds since 1970-01-01, creator text.  Only
; fn.empty has a creation fact, and §7.6.4 permits omitting the other.
(assert-event (equal (lg-reply *lg-env* "LIST ACTIVE.TIMES")
                     (lg-block "215 information follows"
                               '("fn.empty 1758412800 unattributed"))))
(assert-event (equal (lg-reply *lg-env* "LIST ACTIVE.TIMES fn.e*")
                     (lg-reply *lg-env* "LIST ACTIVE.TIMES")))
(assert-event (equal (lg-reply *lg-env* "LIST ACTIVE.TIMES zz*")
                     (lg-block "215 information follows" nil)))
(assert-event (equal (lg-reply *lg-empty-env* "LIST ACTIVE.TIMES")
                     (lg-block "215 information follows" nil)))
(assert-event (equal (lg-reply *lg-env* "LIST DISTRIBUTIONS")
                     (lg-single "503 data item not stored")))
(assert-event (equal (lg-reply *lg-env* "LIST SUBSCRIPTIONS")
                     (lg-single "503 data item not stored")))
(assert-event (equal (lg-reply *lg-env* "LIST NOSUCHVARIANT")
                     (lg-single "501 unsupported LIST variant")))

; -----------------------------------------------------------------------------
; CAPABILITIES and HELP

(assert-event
 (equal (lg-reply *lg-env* "CAPABILITIES")
        (lg-block "101 capability list follows"
                  '("VERSION 2" "READER" "OVER MSGID" "HDR"
                    "LIST ACTIVE ACTIVE.TIMES HEADERS NEWSGROUPS OVERVIEW.FMT"
                    "IMPLEMENTATION fn-nntp-lab"))))
(defconst *lg-help-lines*
  '("CAPABILITIES HELP QUIT MODE DATE POST"
    "GROUP LISTGROUP LIST NEXT LAST NEWGROUPS"
    "ARTICLE HEAD BODY STAT"
    "OVER XOVER HDR XHDR XPAT"))
(assert-event (equal (lg-reply *lg-env* "HELP")
                     (lg-block "100 help text follows" *lg-help-lines*)))

; Every keyword HELP lists is in fact dispatched: none of them answers the
; §3.2.1 "command not recognized" line.  A keyword removed from the dispatcher
; but left in the help text fails here.
(defconst *lg-help-keywords*
  '("CAPABILITIES" "HELP" "QUIT" "MODE" "DATE" "POST" "GROUP" "LISTGROUP"
    "LIST" "NEXT" "LAST" "NEWGROUPS" "ARTICLE" "HEAD" "BODY" "STAT" "OVER"
    "XOVER" "HDR" "XHDR" "XPAT"))
(defun lg-all-dispatchedp (keywords)
  (if (consp keywords)
      (and (not (equal (fn-nntp-result-effects
                        (lg-step *lg-session* *lg-env* (car keywords)))
                       (lg-single "500 command not recognized")))
           (lg-all-dispatchedp (cdr keywords)))
    t))
(assert-event (lg-all-dispatchedp *lg-help-keywords*))
; The control: a keyword the dispatcher does not know does answer 500, so the
; assertion above is not vacuous.  XPATH is RFC 2980 section 2.10, which this
; reader refuses to implement (it would publish storage filenames); it is a
; real unimplemented legacy keyword, not an invented one.
(assert-event (equal (fn-nntp-result-effects
                      (lg-step *lg-session* *lg-env* "XPATH"))
                     (lg-single "500 command not recognized")))

; -----------------------------------------------------------------------------
; XPAT (RFC 2980 section 2.9)
;
; The archive holds one article, number 1 in fn.letters, whose Subject is
; "Test".  Section 2.9.1 assigns 221 to every successful form, including an
; empty selection, and 430 to a message-id that names no article.

; The range form, pattern matching: the XHDR line survives the filter.
(assert-event (equal (lg-reply *lg-env* "XPAT subject 1-1 *est*")
                     (lg-block "221 header follows" (list "1 Test"))))
; The range form, pattern not matching: still 221, with an empty block.
(assert-event (equal (lg-reply *lg-env* "XPAT subject 1-1 nomatch")
                     (lg-block "221 header follows" nil)))
; A pattern that selects everything gives XHDR's own block, initial line and
; all: the agreement theorem, witnessed.
(assert-event (equal (lg-reply *lg-env* "XPAT subject 1-1 *")
                     (lg-reply *lg-env* "XHDR subject 1-1")))
(assert-event
 (fn-nntp-xpat-selects-everythingp
  (fn-nntp-string-octets "subject")
  (fn-wildmat-result-value (fn-wildmat-parse (fn-nntp-string-octets "*")))
  "fn.letters" (list 1) (fn-state-articles *lg-archive*)))
; ... and the hypothesis of that theorem has a tooth: a pattern that selects
; nothing makes the two blocks differ.
(assert-event
 (not (fn-nntp-xpat-selects-everythingp
       (fn-nntp-string-octets "subject")
       (fn-wildmat-result-value
        (fn-wildmat-parse (fn-nntp-string-octets "nomatch")))
       "fn.letters" (list 1) (fn-state-articles *lg-archive*))))
(assert-event (not (equal (lg-reply *lg-env* "XPAT subject 1-1 nomatch")
                          (lg-reply *lg-env* "XHDR subject 1-1"))))
; Every XPAT line is an XHDR line: the parity keystone, on this transcript.
(assert-event
 (subsetp-equal
  (fn-nntp-xpat-lines-for-numbers
   (fn-nntp-string-octets "subject")
   (fn-wildmat-result-value (fn-wildmat-parse (fn-nntp-string-octets "*est*")))
   "fn.letters" (list 1) (fn-state-articles *lg-archive*))
  (fn-nntp-hdr-lines-for-numbers (fn-nntp-string-octets "subject")
                                 "fn.letters" (list 1)
                                 (fn-state-articles *lg-archive*))))
; The message-id form: section 2.9 renders the message-id as the label, as
; XHDR does, and 430 when no such article exists.
(assert-event (equal (lg-reply *lg-env* "XPAT subject <Case@Id.invalid> *")
                     (lg-block "221 header follows"
                               (list "<Case@Id.invalid> Test"))))
(assert-event (equal (lg-reply *lg-env* "XPAT subject <no@such.invalid> *")
                     (lg-single "430 no article with that message-id")))
; A metadata item is calculated by the same two functions OVER and HDR use.
(assert-event (equal (lg-reply *lg-env* "XPAT :lines 1-1 2")
                     (lg-block "221 header follows" (list "1 2"))))
; No newsgroup selected: the range form is 412, as HDR's is.
(assert-event (equal (fn-nntp-result-effects
                      (lg-step *lg-session0* *lg-env* "XPAT subject 1-1 *"))
                     (lg-single "412 no newsgroup selected")))
; Syntax: at least one pattern is required, the field must be a field name,
; and the second token must be a range or a message-id.
(assert-event (equal (lg-reply *lg-env* "XPAT subject 1-1")
                     (lg-single "501 syntax error")))
(assert-event (equal (lg-reply *lg-env* "XPAT subject")
                     (lg-single "501 syntax error")))
(assert-event (equal (lg-reply *lg-env* "XPAT sub:ject 1-1 *")
                     (lg-single "501 syntax error")))
(assert-event (equal (lg-reply *lg-env* "XPAT subject notarange *")
                     (lg-single "501 syntax error")))
; Section 2.9 joins the trailing arguments with a single space into one
; pattern.  The join, directly.
(assert-event (equal (fn-nntp-xpat-join (list (fn-nntp-string-octets "a")
                                              (fn-nntp-string-octets "b")))
                     (fn-nntp-string-octets "a b")))
(assert-event (equal (fn-nntp-xpat-join (list (fn-nntp-string-octets "a")))
                     (fn-nntp-string-octets "a")))
; ... and the joined pattern is the one matched: "T st" does not match
; "Test", but the two tokens joined are one pattern and not two.
(assert-event (equal (lg-reply *lg-env* "XPAT subject 1-1 *T *t*")
                     (lg-block "221 header follows" nil)))
; LOCAL POLICY, witnessed: the match target is bounded at
; *fn-wildmat-max-octets*.  A content longer than that matches nothing.
(assert-event (not (fn-nntp-xpat-matchesp
                    (fn-wildmat-result-value
                     (fn-wildmat-parse (fn-nntp-string-octets "*")))
                    (make-list (+ 1 *fn-wildmat-max-octets*)
                               :initial-element 65))))
(assert-event (fn-nntp-xpat-matchesp
               (fn-wildmat-result-value
                (fn-wildmat-parse (fn-nntp-string-octets "*")))
               (make-list *fn-wildmat-max-octets* :initial-element 65)))

; -----------------------------------------------------------------------------
; Teeth: one concrete violating value per hypothesis
;
; fn-nov-scrub-is-the-identity-on-a-printable-token (books/nntp-legacy.lisp).

; Hypothesis fn-nntp-printable-tokenp: "A", TAB, "B" is not printable and the
; TAB is replaced, so scrub is not the identity on it.
(assert-event (not (fn-nntp-printable-tokenp '(65 9 66))))
(assert-event (not (equal (fn-nov-scrub '(65 9 66)) '(65 9 66))))
; Hypothesis true-listp: an improper token is printable and scrub truncates it.
(assert-event (fn-nntp-printable-tokenp '(65 . 66)))
(assert-event (with-guard-checking :none
               (not (equal (fn-nov-scrub '(65 . 66)) '(65 . 66)))))

; fn-nntp-hdr-of-a-missing-field-is-empty.  The seed article carries no From,
; so that field is empty; the two hypotheses each have a violating value.
(defconst *lg-article* (fn-find-article *lg-id* (fn-state-articles *lg-archive*)))
(assert-event (consp *lg-article*))
(assert-event
 (equal (fn-nntp-hdr-octets
         (fn-nntp-hdr-content (fn-nntp-string-octets "from") *lg-article*))
        nil))
; Hypothesis (not metadata): ":lines" matches no header of the article and yet
; renders "2", because a metadata item is calculated, not read (§8.5.2).
(assert-event
 (not (consp (fn-article-get-headers
              (fn-article-result-article
               (fn-article-parse (fn-article-payload *lg-article*)))
              (fn-nntp-string-octets ":lines")))))
(assert-event
 (equal (fn-nntp-hdr-octets
         (fn-nntp-hdr-content (fn-nntp-string-octets ":lines") *lg-article*))
        (fn-nntp-string-octets "2")))
; Hypothesis (the field is absent): Subject is present and renders non-empty.
(assert-event
 (consp (fn-article-get-headers
         (fn-article-result-article
          (fn-article-parse (fn-article-payload *lg-article*)))
         (fn-nntp-string-octets "subject"))))
(assert-event
 (equal (fn-nntp-hdr-octets
         (fn-nntp-hdr-content (fn-nntp-string-octets "subject") *lg-article*))
        (fn-nntp-string-octets "Test")))

; fn-nntp-xover-agrees-with-over-on-a-nonempty-range.  Hypothesis (consp
; lines): on the empty range 5-2 the two functions differ, which is the whole
; content of the hypothesis.
(assert-event (not (equal (lg-reply *lg-env* "XOVER 5-2")
                          (lg-reply *lg-env* "OVER 5-2"))))

; fn-nntp-newsgroup-lines-are-clean.  Hypothesis fn-nntp-safe-group-listp: a
; group name carrying a CR renders a line that is not clean.
(defconst *lg-unsafe-group* (coerce (list (code-char 65) (code-char 13)) 'string))
(assert-event (not (fn-nntp-safe-group-listp (list *lg-unsafe-group*))))
(assert-event
 (not (fn-nov-clean-line-listp
       (fn-nntp-newsgroup-lines (list *lg-unsafe-group*)))))

; fn-nntp-active-times-lines-are-clean has no hypothesis: a value that is not
; a creation fact contributes no line at all rather than an unclean one.
(assert-event (equal (fn-nntp-active-times-lines '((:not-a-fact))) nil))
