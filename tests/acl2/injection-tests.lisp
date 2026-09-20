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

