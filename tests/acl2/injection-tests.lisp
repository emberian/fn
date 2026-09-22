; Ground witnesses and teeth for books/injection.lisp and
; books/injection-invariants.lisp.
;
; Every form below is a computation, not a rewrite: the injected octets, the
; generated Message-ID and each refusal reason are exhibited on a specific
; article.  The teeth are one violating article per clause of RFC 5537
; section 3.5 that books/injection.lisp implements, plus the configuration and
; clock clauses fn adds.  The open items this book stands in for are named at
; the end.
(in-package "ACL2")
(include-book "../../books/injection-invariants")
(include-book "std/testing/must-fail" :dir :system)

(defconst *fn-t-good* '(70 114 111 109 58 32 112 111 115 116 101 114 64 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 13 10 83 117 98 106 101 99 116 58 32 104 101 108 108 111 13 10 78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10 13 10 72 101 108 108 111 44 32 110 101 119 115 46 13 10))
(defconst *fn-t-withid* '(70 114 111 109 58 32 112 111 115 116 101 114 64 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 13 10 83 117 98 106 101 99 116 58 32 104 101 108 108 111 13 10 78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10 77 101 115 115 97 103 101 45 73 68 58 32 60 97 46 98 64 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 62 13 10 13 10 72 101 108 108 111 44 32 110 101 119 115 46 13 10))
(defconst *fn-t-agent* '(102 110 46 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100))
(defconst *fn-t-cfg* (fn-inj-make-config t *fn-t-agent* (list '(102 110 46 108 101 116 116 101 114 115)) 32768))
(defconst *fn-t-cfg-closed* (fn-inj-make-config nil *fn-t-agent* (list '(102 110 46 108 101 116 116 101 114 115)) 32768))
(defconst *fn-t-cfg-other* (fn-inj-make-config t *fn-t-agent* (list '(102 110 46 111 116 104 101 114)) 32768))
(defconst *fn-t-cfg-small* (fn-inj-make-config t *fn-t-agent* (list '(102 110 46 108 101 116 116 101 114 115)) 64))
(defconst *fn-t-obs* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *fn-t-obs-next* (fn-clock-observation 1000001 843004801000 500 t))
(defconst *fn-t-obs-blind* (fn-clock-observation 1000000 843004800000 500 nil))
(defconst *fn-t-obs-far* (fn-clock-observation 1000000 12622780800000 500 t))
(defconst *fn-t-decision* (fn-inj-decide *fn-t-good* *fn-t-cfg* *fn-t-obs*))

(assert-event (fn-inj-configp *fn-t-cfg*))

; The configuration and the clock are real inputs: a witness with neither
; degenerate.
(assert-event (equal (fn-inj-instant-of 843004800000) '(2026 9 18 0 0 0 5)))

; The whole injected article, exactly as ACL2 produces it.  Path,
; Injection-Date, Injection-Info, the generated Message-ID and the generated
; Date precede the supplied source, which follows verbatim.
(assert-event
 (equal (fn-inj-decision-octets *fn-t-decision*)
        (append

         '(80 97 116 104 58 32 102 110 46 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 33 110 111 116 45 102 111 114 45 109 97 105 108 13 10 73 110 106 101 99 116 105 111 110 45 68 97 116 101 58 32 70 114 105 44 32 49 56 32 83 101 112 32 50 48 50 54 32 48 48 58 48 48 58 48 48 32 43 48 48 48 48 13 10 73 110 106 101 99 116 105 111 110 45 73 110 102 111 58 32 102 110 46 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 13 10 77 101 115 115 97 103 101 45 73 68 58 32 60 48 48 48 48 48 48 48 48 56 52 51 48 48 52 56 48 48 48 48 48 46 48 48 48 48 48 48 48 48 48 48 48 48 48 49 48 48 48 48 48 48 46 102 110 64 102 110 46 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 62 13 10 68 97 116 101 58 32 70 114 105 44 32 49 56 32 83 101 112 32 50 48 50 54 32 48 48 58 48 48 58 48 48 32 43 48 48 48 48 13 10)
         *fn-t-good*)))

(assert-event (fn-inj-injectedp *fn-t-decision*))
(assert-event (equal (fn-inj-decision-reason *fn-t-decision*) nil))
(assert-event (equal (fn-inj-decision-groups *fn-t-decision*) (list '(102 110 46 108 101 116 116 101 114 115))))

; The generated identifier is an RFC 5536 msg-id, and the injected article is
; accepted again by the same parser that accepted the proto-article.
(assert-event (fn-af-message-idp (fn-inj-decision-msgid *fn-t-decision*)))
(assert-event (fn-article-result-okp
               (fn-article-parse (fn-inj-decision-octets *fn-t-decision*))))

; Every mandatory RFC 5536 section 3 field is present exactly once in the
; injected article.
(assert-event
 (let ((a (fn-article-result-article
           (fn-article-parse (fn-inj-decision-octets *fn-t-decision*)))))
   (and (equal (len (fn-article-get-headers a *fn-inj-path-name*)) 1)
        (equal (len (fn-article-get-headers a *fn-inj-from-name*)) 1)
        (equal (len (fn-article-get-headers a *fn-inj-subject-name*)) 1)
        (equal (len (fn-article-get-headers a *fn-inj-date-name*)) 1)
        (equal (len (fn-article-get-headers a *fn-inj-injection-date-name*)) 1)
        (equal (len (fn-article-get-headers a *fn-af-newsgroups-name*)) 1)
        (equal (len (fn-article-get-headers a *fn-af-message-id-name*)) 1)
        (equal (len (fn-article-get-headers a *fn-af-injection-info-name*)) 1))))

; Retry identity, both halves of the design choice.
(assert-event (equal (fn-inj-decide *fn-t-good* *fn-t-cfg* *fn-t-obs*)
                     (fn-inj-decide *fn-t-good* *fn-t-cfg* *fn-t-obs*)))
(assert-event (equal (fn-inj-decision-msgid
                      (fn-inj-decide *fn-t-withid* *fn-t-cfg* *fn-t-obs*))
                     (fn-inj-decision-msgid
                      (fn-inj-decide *fn-t-withid* *fn-t-cfg* *fn-t-obs-next*))))
(assert-event (not (equal (fn-inj-decision-msgid
                           (fn-inj-decide *fn-t-good* *fn-t-cfg* *fn-t-obs*))
                          (fn-inj-decision-msgid
                           (fn-inj-decide *fn-t-good* *fn-t-cfg*
                                          *fn-t-obs-next*)))))

; A different clock reading moves the Injection-Date.  This is the ground
; witness for the composition books/injection-invariants.lisp leaves open:
; the two calendar inverse lemmas and the rendering injectivity are proved
; there; that a different millisecond reading yields a different instant is
; not.
(assert-event (not (equal (fn-inj-date-octets (fn-inj-instant-of 843004800000))
                          (fn-inj-date-octets
                           (fn-inj-instant-of 843004801000)))))
(assert-event (not (equal (fn-inj-decision-octets
                           (fn-inj-decide *fn-t-withid* *fn-t-cfg* *fn-t-obs*))
                          (fn-inj-decision-octets
                           (fn-inj-decide *fn-t-withid* *fn-t-cfg*
                                          *fn-t-obs-next*)))))

; -----------------------------------------------------------------------------
; Teeth: one violating proto-article per clause, each refused by its own name.

(assert-event (equal (fn-inj-decision-reason
                      (fn-inj-decide '(83 117 98 106 101 99 116 58 32 104 101 108 108 111 13 10 78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10 13 10 72 101 108 108 111 46 13 10)
                                     *fn-t-cfg* *fn-t-obs*))
                     :from-missing))
(assert-event (equal (fn-inj-decision-reason
                      (fn-inj-decide '(70 114 111 109 58 32 112 64 101 46 105 110 118 97 108 105 100 13 10 78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10 13 10 72 101 108 108 111 46 13 10)
                                     *fn-t-cfg* *fn-t-obs*))
                     :subject-missing))
(assert-event (equal (fn-inj-decision-reason
                      (fn-inj-decide '(70 114 111 109 58 32 112 64 101 46 105 110 118 97 108 105 100 13 10 83 117 98 106 101 99 116 58 32 104 101 108 108 111 13 10 13 10 72 101 108 108 111 46 13 10)
                                     *fn-t-cfg* *fn-t-obs*))
                     :newsgroups-missing))
(assert-event (equal (fn-inj-decision-reason
                      (fn-inj-decide '(70 114 111 109 58 32 112 64 101 46 105 110 118 97 108 105 100 13 10 83 117 98 106 101 99 116 58 32 104 101 108 108 111 13 10 78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10 73 110 106 101 99 116 105 111 110 45 73 110 102 111 58 32 120 46 105 110 118 97 108 105 100 13 10 13 10 72 101 108 108 111 46 13 10)
                                     *fn-t-cfg* *fn-t-obs*))
                     :injection-info))
(assert-event (equal (fn-inj-decision-reason
                      (fn-inj-decide '(70 114 111 109 58 32 112 64 101 46 105 110 118 97 108 105 100 13 10 83 117 98 106 101 99 116 58 32 104 101 108 108 111 13 10 78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10 88 114 101 102 58 32 104 32 102 110 46 108 101 116 116 101 114 115 58 49 13 10 13 10 72 101 108 108 111 46 13 10)
                                     *fn-t-cfg* *fn-t-obs*))
                     :xref))
(assert-event (equal (fn-inj-decision-reason
                      (fn-inj-decide '(70 114 111 109 58 32 112 64 101 46 105 110 118 97 108 105 100 13 10 83 117 98 106 101 99 116 58 32 104 101 108 108 111 13 10 78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10 80 97 116 104 58 32 114 101 108 97 121 33 110 111 116 45 102 111 114 45 109 97 105 108 13 10 13 10 72 101 108 108 111 46 13 10)
                                     *fn-t-cfg* *fn-t-obs*))
                     :path-present))
(assert-event (equal (fn-inj-decision-reason
                      (fn-inj-decide '(70 114 111 109 58 32 112 64 101 46 105 110 118 97 108 105 100 13 10 83 117 98 106 101 99 116 58 32 104 101 108 108 111 13 10 78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10 73 110 106 101 99 116 105 111 110 45 68 97 116 101 58 32 70 114 105 44 32 49 56 32 83 101 112 32 50 48 50 54 32 48 48 58 48 48 58 48 48 32 43 48 48 48 48 13 10 13 10 72 101 108 108 111 46 13 10)
                                     *fn-t-cfg* *fn-t-obs*))
                     :injection-date-present))
(assert-event (equal (fn-inj-decision-reason
                      (fn-inj-decide '(70 114 111 109 58 32 112 64 101 46 105 110 118 97 108 105 100 13 10 70 114 111 109 58 32 113 64 101 46 105 110 118 97 108 105 100 13 10 83 117 98 106 101 99 116 58 32 104 101 108 108 111 13 10 78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10 13 10 72 101 108 108 111 46 13 10)
                                     *fn-t-cfg* *fn-t-obs*))
                     :from-duplicate))
(assert-event (equal (fn-inj-decision-reason
                      (fn-inj-decide '(70 114 111 109 58 32 112 64 101 46 105 110 118 97 108 105 100 13 10 83 117 98 106 101 99 116 58 32 97 13 10 83 117 98 106 101 99 116 58 32 98 13 10 78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10 13 10 72 101 108 108 111 46 13 10)
                                     *fn-t-cfg* *fn-t-obs*))
                     :subject-duplicate))
(assert-event (equal (fn-inj-decision-reason
                      (fn-inj-decide '(70 114 111 109 58 32 112 64 101 46 105 110 118 97 108 105 100 13 10 83 117 98 106 101 99 116 58 32 97 13 10 78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10 78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10 13 10 72 101 108 108 111 46 13 10)
                                     *fn-t-cfg* *fn-t-obs*))
                     :newsgroups-duplicate))
(assert-event (equal (fn-inj-decision-reason
                      (fn-inj-decide '(70 114 111 109 58 32 112 64 101 46 105 110 118 97 108 105 100 13 10 83 117 98 106 101 99 116 58 32 97 13 10 78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10 77 101 115 115 97 103 101 45 73 68 58 32 110 111 116 45 97 110 45 105 100 13 10 13 10 72 101 108 108 111 46 13 10)
                                     *fn-t-cfg* *fn-t-obs*))
                     :message-id-invalid))
(assert-event (equal (fn-inj-decision-reason
                      (fn-inj-decide '(70 114 111 109 58 32 112 64 101 46 105 110 118 97 108 105 100 13 10 83 117 98 106 101 99 116 58 32 97 13 10 78 101 119 115 103 114 111 117 112 115 58 32 102 110 32 108 101 116 116 101 114 115 33 13 10 13 10 72 101 108 108 111 46 13 10)
                                     *fn-t-cfg* *fn-t-obs*))
                     :newsgroups-invalid))

(assert-event (equal (fn-inj-decision-reason
                      (fn-inj-decide '(1 2 3) *fn-t-cfg* *fn-t-obs*))
                     :unparsable))
(assert-event (equal (fn-inj-decision-reason
                      (fn-inj-decide *fn-t-good* *fn-t-cfg-closed* *fn-t-obs*))
                     :posting-disallowed))
(assert-event (equal (fn-inj-decision-reason
                      (fn-inj-decide *fn-t-good* *fn-t-cfg-other* *fn-t-obs*))
                     :unknown-group))
(assert-event (equal (fn-inj-decision-reason
                      (fn-inj-decide *fn-t-good* *fn-t-cfg-small* *fn-t-obs*))
                     :oversize))
(assert-event (equal (fn-inj-decision-reason
                      (fn-inj-decide *fn-t-good* *fn-t-cfg* *fn-t-obs-blind*))
                     :clock-unusable))
(assert-event (equal (fn-inj-decision-reason
                      (fn-inj-decide *fn-t-good* *fn-t-cfg* *fn-t-obs-far*))
                     :clock-out-of-range))
(assert-event (equal (fn-inj-decision-reason
                      (fn-inj-decide *fn-t-good* 17 *fn-t-obs*))
                     :config-invalid))

; Every refusal above produced no octets and no identity.
(assert-event (equal (fn-inj-decision-octets
                      (fn-inj-decide *fn-t-good* *fn-t-cfg-closed* *fn-t-obs*))
                     nil))
(assert-event (equal (fn-inj-decision-msgid
                      (fn-inj-decide *fn-t-good* *fn-t-cfg-other* *fn-t-obs*))
                     nil))

; Open, recorded rather than weakened: fn-af-message-idp of every generated
; identifier (proved only by the witnesses above), and
;   (implies (and (natp a) (natp b) (< (floor a 86400000) 146097)
;                 (< (floor b 86400000) 146097)
;                 (equal (fn-inj-instant-of a) (fn-inj-instant-of b)))
;            (equal (floor a 1000) (floor b 1000)))
; which would close fn-inj-date-octets-separate-different-instants into a
; statement about the clock rather than about the instant.

; -----------------------------------------------------------------------------
; RFC 5536 section 3.1.2: From is an RFC 5322 mailbox-list
; (books/mailbox.lisp; keystones fn-mbx-mailbox-list-names-an-address and
; fn-inj-injected-proto-article-has-a-mailbox-list-from).  The served POST
; (books/nntp-post.lisp fn-nntp-post-step) and the operator's submission
; (books/owner.lisp fn-own-operator-decision) both call fn-inj-decide.
;
; THE WITNESSES ARE THE LABS' OWN ARTICLES.  The INN lab of 2026-09-22
; (planning/evidence/inn-lab-dabebb84-2026-09-22.md, "fn's feed -> innd")
; POSTed the proto-article below to a node whose path identity was
; fnA.hbox.test and fed innd the injected octets written out below, at the
; Injection-Date the transcript shows.  The agents run of the same day
; (planning/evidence/agents-on-hbox-2026-09-22.md, run 03) POSTed with
; `From: yue' and was answered 240; that article's other fields are not in
; the evidence, so the proto-article below is its shape with the From that
; was recorded.

(defun it-codes (cs)
  (declare (xargs :mode :program))
  (if (consp cs) (cons (char-code (car cs)) (it-codes (cdr cs))) nil))
(defun it-octets (s)
  (declare (xargs :mode :program))
  (it-codes (coerce s 'list)))
(defun it-lines (lines)
  (declare (xargs :mode :program))
  (if (consp lines) (append (it-octets (car lines)) '(13 10) (it-lines (cdr lines))) nil))

(defconst *it-lab-proto*
  (it-lines (list "From: lab@example.invalid"
                  "Newsgroups: fn.letters"
                  "Subject: posted on fn, fed to INN"
                  "Date: Tue, 22 Sep 2026 21:26:21 -0000"
                  "Message-ID: <inn-lab-fn-post-8a5f502-20260922T212621Z@example.invalid>"
                  ""
                  "From the fn INN interop lab.")))
(defconst *it-lab-agent* (it-octets "fnA.hbox.test"))
(defconst *it-lab-cfg*
  (fn-inj-make-config t *it-lab-agent* (list (it-octets "fn.letters")) 32768))
; 2026-09-22T21:26:47Z in milliseconds since 2000-01-01T00:00:00Z.
(defconst *it-lab-obs* (fn-clock-observation 1000000 843427607000 500 t))
(defconst *it-lab-decision* (fn-inj-decide *it-lab-proto* *it-lab-cfg* *it-lab-obs*))
(assert-event (fn-inj-injectedp *it-lab-decision*))
; What innd received, octet for octet.
(assert-event
 (equal (fn-inj-decision-octets *it-lab-decision*)
        (append (it-lines (list "Path: fnA.hbox.test!not-for-mail"
                                "Injection-Date: Tue, 22 Sep 2026 21:26:47 +0000"
                                "Injection-Info: fnA.hbox.test"))
                *it-lab-proto*)))

(defun it-from-value (source)
  (declare (xargs :mode :program))
  (fn-article-field-unfolded-value
   (car (fn-article-get-headers
         (fn-article-result-article (fn-article-parse source))
         *fn-inj-from-name*))))

; Keystone fn-inj-injected-proto-article-has-a-mailbox-list-from: the
; witness is the lab's article; its From is a mailbox-list and names "@".
(assert-event (fn-mbx-mailbox-listp (it-from-value *it-lab-proto*)))
(assert-event (member-equal 64 (it-from-value *it-lab-proto*)))
; `From: yue' is refused with its own reason, and its value is no mailbox.
(defconst *it-yue-proto*
  (it-lines (list "From: yue"
                  "Newsgroups: fn.letters"
                  "Subject: run 03"
                  "Message-ID: <yue-03@example.invalid>"
                  ""
                  "hello from yue")))
(assert-event (equal (fn-inj-decision-reason
                      (fn-inj-decide *it-yue-proto* *it-lab-cfg* *it-lab-obs*))
                     :from-invalid))
(assert-event (not (fn-mbx-mailbox-listp (it-from-value *it-yue-proto*))))
(assert-event (not (member-equal 64 (it-from-value *it-yue-proto*))))
; Tooth for the one hypothesis: without the injection, a parsed From need not
; be a mailbox-list -- `From: yue' parses and is not one.
(must-fail
 (defthm it-from-without-injection
   (let* ((article (fn-article-result-article (fn-article-parse source)))
          (value (fn-article-field-unfolded-value
                  (car (fn-article-get-headers article *fn-inj-from-name*)))))
     (and (fn-mbx-mailbox-listp value)
          (member-equal 64 value)))
   :hints (("Goal" :in-theory (e/d (fn-inj-mandatory-reason fn-inj-from-validp)
                                   (fn-mbx-mailbox-listp))))))
(assert-event (fn-article-result-okp (fn-article-parse *it-yue-proto*)))

; Keystone fn-mbx-mailbox-list-names-an-address: accepted values, each with
; an "@", across the grammar's productions (addr-spec, name-addr with a
; quoted and an obs-phrase display name, a list, comments, a
; domain-literal, a quoted local-part); refused values, each with a reason
; the grammar names.
(defun it-mbx (s)
  (declare (xargs :mode :program))
  (fn-mbx-mailbox-listp (it-octets s)))
(assert-event (it-mbx " lab@example.invalid"))
(assert-event (it-mbx " \"John Smith\" <j@example.com>"))
(assert-event (it-mbx " John Q. Public <jqp@example.com>"))
(assert-event (it-mbx " a@b, c@d"))
(assert-event (it-mbx " (comment (nested)) x@y.z (trailing)"))
(assert-event (it-mbx " <a@[127.0.0.1]>"))
(assert-event (it-mbx " \"q\\\"x\"@y"))
(assert-event (it-mbx " a @ b"))
(assert-event (it-mbx " =?UTF-8?Q?J=C3=B6rg?= <j@x.de>"))
(assert-event (not (it-mbx " yue")))              ; no addr-spec
(assert-event (not (it-mbx " Yue")))
(assert-event (not (it-mbx " yue <yue>")))        ; angle-addr without "@"
(assert-event (not (it-mbx " a@b,")))             ; empty list element (obsolete)
(assert-event (not (it-mbx " Joe <a@b")))         ; unclosed angle-addr
(assert-event (not (it-mbx " j..x@y")))           ; not a dot-atom
(assert-event (not (it-mbx " .x@y")))
(assert-event (not (it-mbx " j@x.y.")))
(assert-event (not (it-mbx " group: a@b;")))      ; a group is an address-list
(assert-event (not (it-mbx " <j@x> <k@y>")))
(assert-event (not (it-mbx " \"unterminated@x")))
(assert-event (not (it-mbx " x@")))
(assert-event (not (it-mbx " @y")))
; A value longer than the header block is refused before it is scanned.
(assert-event (not (fn-mbx-mailbox-listp
                    (append (it-octets " a@b ") (make-list 8192 :initial-element 32)))))
; Tooth for the one hypothesis: without it, a value need not name "@".
(must-fail
 (defthm it-every-value-names-an-address
   (member-equal 64 value)))
(assert-event (not (member-equal 64 (it-octets " yue"))))

; Keystone fn-inj-injected-article-is-a-reinjection-of-its-source: the lab's
; injection (supplied Message-ID and Date), and the generated-identifier
; article above (both generated lines present).
(assert-event (fn-inj-reinjectionp
               (fn-inj-decision-octets *it-lab-decision*) *it-lab-proto* *it-lab-agent*
               (fn-inj-decision-msgid *it-lab-decision*)))
(assert-event (fn-inj-reinjectionp
               (fn-inj-decision-octets *fn-t-decision*) *fn-t-good* *fn-t-agent*
               (fn-inj-decision-msgid *fn-t-decision*)))
; Separating: another agent, another source, or the source alone is not.
(assert-event (not (fn-inj-reinjectionp
                    (fn-inj-decision-octets *it-lab-decision*) *it-lab-proto*
                    (it-octets "fnB.hbox.test")
                    (fn-inj-decision-msgid *it-lab-decision*))))
(assert-event (not (fn-inj-reinjectionp
                    (fn-inj-decision-octets *it-lab-decision*) *it-yue-proto*
                    *it-lab-agent* (fn-inj-decision-msgid *it-lab-decision*))))
(assert-event (not (fn-inj-reinjectionp *it-lab-proto* *it-lab-proto* *it-lab-agent*
                                        (fn-inj-decision-msgid *it-lab-decision*))))
; Tooth for the one hypothesis: a refusal's octets (none) are no injection.
(must-fail
 (defthm it-reinjection-without-injection
   (fn-inj-reinjectionp
    (fn-inj-decision-octets (fn-inj-decide source config observation))
    source
    (fn-inj-config-agent config)
    (fn-inj-decision-msgid (fn-inj-decide source config observation)))
   :hints (("Goal" :in-theory (enable fn-inj-decide fn-inj-refuse fn-inj-injectedp)))))
(assert-event (not (fn-inj-reinjectionp
                    (fn-inj-decision-octets
                     (fn-inj-decide *it-yue-proto* *it-lab-cfg* *it-lab-obs*))
                    *it-yue-proto* *it-lab-agent* nil)))

; fn-inj-injection-requires-posting-allowed: a closed configuration refuses.
(assert-event (not (fn-inj-injectedp
                    (fn-inj-decide *it-lab-proto*
                                   (fn-inj-make-config nil *it-lab-agent*
                                                       (list (it-octets "fn.letters"))
                                                       32768)
                                   *it-lab-obs*))))
(must-fail
 (defthm it-every-configuration-allows-posting
   (fn-inj-config-allow config)))

