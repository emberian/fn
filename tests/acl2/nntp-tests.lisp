; Independent expected transcripts for the experimental reader-only session,
; and the teeth for the keystone theorems in books/nntp-invariants.lisp and
; books/nntp-effects.lisp: a reachable non-degenerate witness for each, and a
; concrete counterexample or a must-fail for each of their hypotheses.
(in-package "ACL2")
(include-book "../../books/nntp-effects")
(include-book "std/testing/must-fail" :dir :system)

; The reader environment every transcript below runs against: one wall clock
; reading (2026-09-19T12:34:56Z as DTN milliseconds) and one persisted group
; creation fact.  No transcript lets the reader invent either.
(defconst *fn-nntp-obs0*
  (fn-clock-observation 1000 843136496000 1000 t))
(defconst *fn-nntp-blind-obs*
  (fn-clock-observation 1000 0 0 nil))
(defconst *fn-nntp-facts0*
  (list (fn-nntp-group-fact "fn.letters" 0 *fn-nntp-blind-obs*)
        (fn-nntp-group-fact "fn.empty" 811728000000 *fn-nntp-blind-obs*)))
(defconst *fn-nntp-env0* (fn-nntp-env *fn-nntp-obs0* *fn-nntp-facts0*))
(defconst *fn-nntp-blind-env* (fn-nntp-env *fn-nntp-blind-obs* nil))
(assert-event (fn-nntp-envp *fn-nntp-env0*))
(assert-event (fn-nntp-envp *fn-nntp-blind-env*))

(defconst *fn-nntp-groups* '("fn.letters" "fn.empty"))
(defconst *fn-nntp-id* "<Case@Id.invalid>")
(defconst *fn-nntp-payload*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62 13 10
    83 117 98 106 101 99 116 58 32 84 101 115 116 13 10 13 10
    72 101 108 108 111 13 10 46 100 111 116 13 10))
(defconst *fn-nntp-empty-archive* (fn-initial-state *fn-nntp-groups*))
(defconst *fn-nntp-prepared*
  (fn-accept-prepare *fn-nntp-empty-archive* 1 *fn-nntp-id* *fn-nntp-payload* '("fn.letters")))
(defconst *fn-nntp-archive* (fn-accept-complete *fn-nntp-prepared* 0 1 :durable))
(defconst *fn-nntp-session0* (fn-nntp-open-session *fn-nntp-archive*))
(assert-event (fn-statep *fn-nntp-archive*))
(assert-event (fn-nntp-sessionp *fn-nntp-session0*))
(assert-event (fn-nntp-projectionp *fn-nntp-archive*))
(assert-event (equal (fn-nntp-session-projected *fn-nntp-session0*) t))
(assert-event (fn-nntp-session-consistentp *fn-nntp-session0* *fn-nntp-archive*))

; Decimal parsing is left-to-right: 12 is twelve, not twenty-one.  Leading
; zeroes are accepted, and the RFC 3977 maximum is the last accepted value.
(assert-event (equal (fn-nntp-decimal-value '(49 50)) 12))
(assert-event (equal (fn-nntp-decimal-value '(49 50 48)) 120))
(assert-event (equal (fn-nntp-decimal-value '(48 48 49 50)) 12))
(assert-event (fn-nntp-number-tokenp '(50 49 52 55 52 56 51 54 52 55)))
(assert-event (not (fn-nntp-number-tokenp '(50 49 52 55 52 56 51 54 52 56))))

; The rendering guard in fn-nntp-decimal-field is inactive at both ends of RFC
; 3977 section 6's range, so the structural ten-octet field bound costs nothing.
(assert-event (equal (fn-nntp-decimal-field 0) '(48)))
(assert-event (equal (fn-nntp-decimal-field 1) '(49)))
(assert-event (equal (fn-nntp-decimal-field 2147483647)
                     '(50 49 52 55 52 56 51 54 52 55)))
(assert-event (equal (len (fn-nntp-decimal-field 2147483647)) 10))

; Exact selected-group transcript; mixed case changes only the command keyword.
(defconst *fn-nntp-group*
  (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0*
                '(:command (103 82 111 85 112 32 102 110 46 108 101 116 116 101 114 115))))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-group*)
        '((:reply (50 49 49 32 49 32 49 32 49 32 102 110 46 108 101 116 116 101 114 115 13 10)))))
(assert-event (equal (fn-nntp-session-group (fn-nntp-result-session *fn-nntp-group*)) "fn.letters"))
(assert-event (equal (fn-nntp-session-current (fn-nntp-result-session *fn-nntp-group*)) 1))

; HEAD excludes the separator and BODY excludes it, while BODY dot-stuffs the
; stored dot-prefixed line.  Their expected wire octets include every CRLF.
(defconst *fn-nntp-head*
  (fn-nntp-step (fn-nntp-result-session *fn-nntp-group*) *fn-nntp-archive* *fn-nntp-env0*
                '(:command (72 69 65 68))))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-head*)
        '((:reply (50 50 49 32 49 32 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62 32 104 101 97 100 101 114 115 32 102 111 108 108 111 119 13 10
                   77 101 115 115 97 103 101 45 73 68 58 32 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62 13 10
                   83 117 98 106 101 99 116 58 32 84 101 115 116 13 10 46 13 10)))))
(defconst *fn-nntp-body*
  (fn-nntp-step (fn-nntp-result-session *fn-nntp-group*) *fn-nntp-archive* *fn-nntp-env0*
                '(:command (66 79 68 89))))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-body*)
        '((:reply (50 50 50 32 49 32 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62 32 98 111 100 121 32 102 111 108 108 111 119 115 13 10
                   72 101 108 108 111 13 10 46 46 100 111 116 13 10 46 13 10)))))

; Message-ID is exact-case and leaves group/cursor unchanged; numeric retrieval
; without a group is 412, and no-current is 420.
(defconst *fn-nntp-by-id*
  (fn-nntp-step (fn-nntp-result-session *fn-nntp-group*) *fn-nntp-archive* *fn-nntp-env0*
                '(:command (83 84 65 84 32 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62))))
(assert-event (equal (fn-nntp-result-session *fn-nntp-by-id*)
                     (fn-nntp-result-session *fn-nntp-group*)))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-by-id*)
        '((:reply (50 50 51 32 48 32 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62 32 114 101 116 114 105 101 118 101 100 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step (fn-nntp-result-session *fn-nntp-group*) *fn-nntp-archive* *fn-nntp-env0*
                       '(:command (83 84 65 84 32 60 99 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62))))
        '((:reply (52 51 48 32 110 111 32 97 114 116 105 99 108 101 32 119 105 116 104 32 116 104 97 116 32 109 101 115 115 97 103 101 45 105 100 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0* '(:command (83 84 65 84 32 49))))
        '((:reply (52 49 50 32 110 111 32 110 101 119 115 103 114 111 117 112 32 115 101 108 101 99 116 101 100 13 10)))))
(defconst *fn-nntp-empty-group*
  (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0*
                '(:command (71 82 79 85 80 32 102 110 46 101 109 112 116 121))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step (fn-nntp-result-session *fn-nntp-empty-group*) *fn-nntp-archive* *fn-nntp-env0* '(:command (83 84 65 84))))
        '((:reply (52 50 48 32 110 111 32 99 117 114 114 101 110 116 32 97 114 116 105 99 108 101 13 10)))))

; Error and capability transcript: no READER/POST/TLS/auth claim; bad syntax is
; 501 and recognized but unsupported POST is 500.
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0* '(:command (80 79 83 84))))
        '((:reply (53 48 48 32 99 111 109 109 97 110 100 32 110 111 116 32 114 101 99 111 103 110 105 122 101 100 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0* '(:command (71 82 79 85 80 32))))
        '((:reply (53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0* '(:command (32 71 82 79 85 80 32 102 110 46 108 101 116 116 101 114 115))))
        '((:reply (53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0* '(:command (83 84 65 84 32 48))))
        '((:reply (53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
; RFC 3977 section 9.8 keywords contain at least three ASCII characters.
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0* '(:command (78 79))))
        '((:reply (53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0* '(:command (67 65 80 65 66 73 76 73 84 73 69 83 32 65))))
        '((:reply (53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0* '(:command (67 65 80 65 66 73 76 73 84 73 69 83 32 65 66))))
        '((:reply (53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
(defconst *fn-nntp-caps*
  (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0* '(:command (67 65 80 65 66 73 76 73 84 73 69 83))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0* '(:command (67 65 80 65 66 73 76 73 84 73 69 83 32 70 79 79))))
        (fn-nntp-result-effects *fn-nntp-caps*)))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-caps*)
        '((:reply (49 48 49 32 99 97 112 97 98 105 108 105 116 121 32 108 105 115 116 32 102 111 108 108 111 119 115 13 10
                   86 69 82 83 73 79 78 32 50 13 10 73 77 80 76 69 77 69 78 84 65 84 73 79 78 32 102 110 45 110 110 116 112 45 108 97 98 13 10 46 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0*
                       '(:command (67 65 80 65 66 73 76 73 84 73 69 83 32 65 85 84 79 85 80 68 65 84 69))))
        (fn-nntp-result-effects *fn-nntp-caps*)))

; -----------------------------------------------------------------------------
; D3: an unprojectable article degrades only itself

; fn.letters holds a projectable article at 1 and, at 2, one whose stored bytes
; are not CRLF-framed.  acceptance.lisp admits it; the reader used to answer
; 503 to every command in its presence, including CAPABILITIES and QUIT.
(defconst *fn-nntp-broken-payload* '(111 112 97 113 117 101 32 98 121 116 101 115))
(defconst *fn-nntp-mixed-good*
  (fn-make-article "<good@mixed.invalid>" *fn-nntp-payload* '("fn.letters")
                   '(("fn.letters" . 1)) t))
(defconst *fn-nntp-mixed-broken*
  (fn-make-article "<broken@mixed.invalid>" *fn-nntp-broken-payload* '("fn.letters")
                   '(("fn.letters" . 2)) t))
(defconst *fn-nntp-mixed-archive*
  (fn-make-state '("fn.letters") '(("fn.letters" . 3))
                 (list *fn-nntp-mixed-broken* *fn-nntp-mixed-good*) 0 nil nil))
(assert-event (fn-statep *fn-nntp-mixed-archive*))
(assert-event (fn-articlep '("fn.letters") *fn-nntp-mixed-broken*))
(assert-event (not (fn-nntp-projection-articlep *fn-nntp-mixed-broken*)))
(assert-event (fn-nntp-article-idp *fn-nntp-mixed-broken*))
(assert-event (not (fn-nntp-article-framedp *fn-nntp-mixed-broken*)))
; The configuration is still projectable, so the reader opens and serves.
(assert-event (fn-nntp-projectionp *fn-nntp-mixed-archive*))
(defconst *fn-nntp-mixed-session* (fn-nntp-open-session *fn-nntp-mixed-archive*))
(assert-event (equal (fn-nntp-session-projected *fn-nntp-mixed-session*) t))

(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-mixed-session* *fn-nntp-mixed-archive* *fn-nntp-env0*
                       '(:command (67 65 80 65 66 73 76 73 84 73 69 83))))
        (fn-nntp-result-effects *fn-nntp-caps*)))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-mixed-session* *fn-nntp-mixed-archive* *fn-nntp-env0*
                       '(:command (81 85 73 84))))
        '((:reply (50 48 53 32 99 108 111 115 105 110 103 32 99 111 110 110 101 99 116 105 111 110 13 10)) (:close))))
; GROUP counts both articles: an unframed payload is still an article number.
(defconst *fn-nntp-mixed-group*
  (fn-nntp-step *fn-nntp-mixed-session* *fn-nntp-mixed-archive* *fn-nntp-env0*
                '(:command (71 82 79 85 80 32 102 110 46 108 101 116 116 101 114 115))))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-mixed-group*)
        '((:reply (50 49 49 32 50 32 49 32 50 32 102 110 46 108 101 116 116 101 114 115 13 10)))))
(assert-event (equal (fn-nntp-session-current
                      (fn-nntp-result-session *fn-nntp-mixed-group*)) 1))
; STAT reads only the stored identifier, so it answers for the unframed article.
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step (fn-nntp-result-session *fn-nntp-mixed-group*)
                       *fn-nntp-mixed-archive* *fn-nntp-env0* '(:command (83 84 65 84 32 50))))
        '((:reply (50 50 51 32 50 32 60 98 114 111 107 101 110 64 109 105 120 101 100 46 105 110 118 97 108 105 100 62 32 114 101 116 114 105 101 118 101 100 13 10)))))
; ARTICLE, HEAD and BODY need the bytes, and say so for that article only.
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step (fn-nntp-result-session *fn-nntp-mixed-group*)
                       *fn-nntp-mixed-archive* *fn-nntp-env0* '(:command (65 82 84 73 67 76 69 32 50))))
        '((:reply (53 48 51 32 115 116 111 114 101 100 32 97 114 116 105 99 108 101 32 102 114 97 109 105 110 103 32 117 110 97 118 97 105 108 97 98 108 101 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step (fn-nntp-result-session *fn-nntp-mixed-group*)
                       *fn-nntp-mixed-archive* *fn-nntp-env0* '(:command (65 82 84 73 67 76 69 32 49))))
        '((:reply (50 50 48 32 49 32 60 103 111 111 100 64 109 105 120 101 100 46 105 110 118 97 108 105 100 62 32 97 114 116 105 99 108 101 32 102 111 108 108 111 119 115 13 10
                   77 101 115 115 97 103 101 45 73 68 58 32 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62 13 10
                   83 117 98 106 101 99 116 58 32 84 101 115 116 13 10 13 10
                   72 101 108 108 111 13 10 46 46 100 111 116 13 10 46 13 10)))))
; The unframed article keeps its cursor position, so NEXT still reaches it.
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step (fn-nntp-result-session *fn-nntp-mixed-group*)
                       *fn-nntp-mixed-archive* *fn-nntp-env0* '(:command (78 69 88 84))))
        '((:reply (50 50 51 32 50 32 60 98 114 111 107 101 110 64 109 105 120 101 100 46 105 110 118 97 108 105 100 62 32 114 101 116 114 105 101 118 101 100 13 10)))))

; An article whose stored identifier cannot be rendered is excluded from the
; group's numbers and from LISTGROUP, and a command naming its number says so.
(defconst *fn-nntp-bad-id*
  (coerce (list (code-char 60) (code-char 120) (code-char 62)
                (code-char 13) (code-char 10)) 'string))
(defconst *fn-nntp-bad-id-article*
  (fn-make-article *fn-nntp-bad-id* *fn-nntp-payload* '("fn.letters")
                   '(("fn.letters" . 2)) t))
(defconst *fn-nntp-bad-id-archive*
  (fn-make-state '("fn.letters") '(("fn.letters" . 3))
                 (list *fn-nntp-bad-id-article* *fn-nntp-mixed-good*) 0 nil nil))
(assert-event (fn-statep *fn-nntp-bad-id-archive*))
(assert-event (fn-nntp-projectionp *fn-nntp-bad-id-archive*))
(assert-event (not (fn-nntp-article-idp *fn-nntp-bad-id-article*)))
(assert-event (equal (fn-nntp-article-number "fn.letters" *fn-nntp-bad-id-article*) 0))
(defconst *fn-nntp-bad-id-session* (fn-nntp-open-session *fn-nntp-bad-id-archive*))
(defconst *fn-nntp-bad-id-group*
  (fn-nntp-step *fn-nntp-bad-id-session* *fn-nntp-bad-id-archive* *fn-nntp-env0*
                '(:command (76 73 83 84 71 82 79 85 80 32 102 110 46 108 101 116 116 101 114 115))))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-bad-id-group*)
        '((:reply (50 49 49 32 49 32 49 32 49 32 102 110 46 108 101 116 116 101 114 115 32 108 105 115 116 32 102 111 108 108 111 119 115 13 10
                   49 13 10 46 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step (fn-nntp-result-session *fn-nntp-bad-id-group*)
                       *fn-nntp-bad-id-archive* *fn-nntp-env0* '(:command (83 84 65 84 32 50))))
        '((:reply (53 48 51 32 115 116 111 114 101 100 32 97 114 116 105 99 108 101 32 105 100 101 110 116 105 102 105 101 114 32 117 110 97 118 97 105 108 97 98 108 101 13 10)))))
; NEXT from the first article does not move onto it.
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step (fn-nntp-result-session *fn-nntp-bad-id-group*)
                       *fn-nntp-bad-id-archive* *fn-nntp-env0* '(:command (78 69 88 84))))
        '((:reply (52 50 49 32 110 111 32 110 101 120 116 32 97 114 116 105 99 108 101 13 10)))))

; -----------------------------------------------------------------------------
; Configuration refusal, and the 549-octet initial line

(defun fn-nntp-test-chars (n)
  (if (zp n) nil (cons (code-char 97) (fn-nntp-test-chars (1- n)))))
(defconst *fn-nntp-group-460* (coerce (fn-nntp-test-chars 460) 'string))
(defconst *fn-nntp-group-461* (coerce (fn-nntp-test-chars 461) 'string))
(defconst *fn-nntp-group-497* (coerce (fn-nntp-test-chars 497) 'string))
(assert-event (fn-nntp-safe-group-namep *fn-nntp-group-460*))
(assert-event (not (fn-nntp-safe-group-namep *fn-nntp-group-461*)))
; The review's case: a 497-octet group name made a LISTGROUP 211 line 549
; octets long.  That configuration is now refused before the reader opens.
(assert-event (not (fn-nntp-safe-group-namep *fn-nntp-group-497*)))
(assert-event (not (fn-nntp-projectionp (fn-initial-state (list *fn-nntp-group-497*)))))
(defconst *fn-nntp-wide-archive* (fn-initial-state (list *fn-nntp-group-460*)))
(assert-event (fn-nntp-projectionp *fn-nntp-wide-archive*))
(assert-event
 (<= (+ (len (fn-nntp-listgroup-initial *fn-nntp-wide-archive* *fn-nntp-group-460*)) 2)
     *fn-nntp-max-response-octets*))
(assert-event
 (fn-nntp-effectsp
  (fn-nntp-result-effects
   (fn-nntp-step (fn-nntp-open-session *fn-nntp-wide-archive*) *fn-nntp-wide-archive* *fn-nntp-env0*
                 (list :command (append '(76 73 83 84 71 82 79 85 80 32)
                                        (fn-nntp-string-octets *fn-nntp-group-460*)))))))
; A group name a response cannot render refuses the configuration, and the
; session still answers every command that does not read the archive.
(defconst *fn-nntp-unsafe-group*
  (coerce (list (code-char 102) (code-char 110) (code-char 13) (code-char 10)
                (code-char 50) (code-char 48) (code-char 53)) 'string))
(defconst *fn-nntp-unsafe-group-archive* (fn-initial-state (list *fn-nntp-unsafe-group*)))
(assert-event (fn-statep *fn-nntp-unsafe-group-archive*))
(assert-event (not (fn-nntp-projectionp *fn-nntp-unsafe-group-archive*)))
(defconst *fn-nntp-degraded-session*
  (fn-nntp-open-session *fn-nntp-unsafe-group-archive*))
(assert-event (null (fn-nntp-session-projected *fn-nntp-degraded-session*)))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-degraded-session* *fn-nntp-unsafe-group-archive* *fn-nntp-env0*
                       '(:command (76 73 83 84))))
        '((:reply (53 48 51 32 97 114 99 104 105 118 101 32 112 114 111 106 101 99 116 105 111 110 32 117 110 97 118 97 105 108 97 98 108 101 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-degraded-session* *fn-nntp-unsafe-group-archive* *fn-nntp-env0*
                       '(:command (67 65 80 65 66 73 76 73 84 73 69 83))))
        (fn-nntp-result-effects *fn-nntp-caps*)))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-degraded-session* *fn-nntp-unsafe-group-archive* *fn-nntp-env0*
                       '(:command (81 85 73 84))))
        '((:reply (50 48 53 32 99 108 111 115 105 110 103 32 99 111 110 110 101 99 116 105 111 110 13 10)) (:close))))

; -----------------------------------------------------------------------------
; Teeth

; fn-nntp-step-preserves-carried-projection is unconditional, so its teeth are
; the two reachable verdicts and a trace that keeps each one.
(assert-event (equal (fn-nntp-session-projected
                      (fn-nntp-run-session *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0*
                                           '((:command (71 82 79 85 80 32 102 110 46 108 101 116 116 101 114 115))
                                             (:command (83 84 65 84))
                                             (:command (81 85 73 84))
                                             (:command (83 84 65 84)))))
                     t))
(assert-event (equal (fn-nntp-session-projected
                      (fn-nntp-run-session *fn-nntp-degraded-session*
                                           *fn-nntp-unsafe-group-archive* *fn-nntp-env0*
                                           '((:command (76 73 83 84))
                                             (:command (67 65 80 65 66 73 76 73 84 73 69 83)))))
                     nil))
; Without the carried verdict the two sessions would be indistinguishable; they
; are not.
(assert-event (not (equal (fn-nntp-session-projected *fn-nntp-session0*)
                          (fn-nntp-session-projected *fn-nntp-degraded-session*))))

; fn-nntp-archive-free-step-ignores-the-archive: the hypothesis has force.
; GROUP is archive-dependent, and its answer does change with the archive.
(assert-event
 (equal (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0* '(:command (81 85 73 84)))
        (fn-nntp-step *fn-nntp-session0* *fn-nntp-mixed-archive* *fn-nntp-env0* '(:command (81 85 73 84)))))
(assert-event
 (equal (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0*
                      '(:command (67 65 80 65 66 73 76 73 84 73 69 83)))
        (fn-nntp-step *fn-nntp-session0* *fn-nntp-mixed-archive* *fn-nntp-env0*
                      '(:command (67 65 80 65 66 73 76 73 84 73 69 83)))))
(assert-event (fn-nntp-archive-keywordp '(71 82 79 85 80)))
(assert-event
 (not (equal (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0*
                           '(:command (71 82 79 85 80 32 102 110 46 108 101 116 116 101 114 115)))
             (fn-nntp-step *fn-nntp-session0* *fn-nntp-mixed-archive* *fn-nntp-env0*
                           '(:command (71 82 79 85 80 32 102 110 46 108 101 116 116 101 114 115))))))
(must-fail
 (thm (equal (fn-nntp-step session archive *fn-nntp-env0* (list :command line))
             (fn-nntp-step session other *fn-nntp-env0* (list :command line)))))

; fn-nntp-step-preserves-consistent-session: dropping the hypothesis fails on a
; reachable-shaped session whose cursor names no available article.
(defconst *fn-nntp-stale-session* (fn-nntp-make-session t "fn.letters" 99 t))
(assert-event (fn-nntp-sessionp *fn-nntp-stale-session*))
(assert-event (not (fn-nntp-session-consistentp *fn-nntp-stale-session* *fn-nntp-archive*)))
(assert-event
 (not (fn-nntp-session-consistentp
       (fn-nntp-result-session
        (fn-nntp-step *fn-nntp-stale-session* *fn-nntp-archive* *fn-nntp-env0* '(:command (83 84 65 84))))
       *fn-nntp-archive*)))
(must-fail
 (thm (fn-nntp-session-consistentp
       (fn-nntp-result-session (fn-nntp-step session archive *fn-nntp-env0* wire-event))
       archive)))

; fn-nntp-step-effects-well-formed: a session that claims a projection the
; archive does not have escapes the 460-octet group cap, which is the only
; reason every generated initial line fits, so the conclusion is false
; without the hypothesis.
(defconst *fn-nntp-forged-session* (fn-nntp-make-session t nil nil t))
(assert-event (fn-nntp-sessionp *fn-nntp-forged-session*))
(assert-event (not (fn-nntp-session-consistentp
                    *fn-nntp-forged-session* *fn-nntp-unsafe-group-archive*)))
; The witness is LISTGROUP over a 497-octet group name, the widest argument
; token a command line may carry: the name alone is 497 octets and
; " list follows" adds 13, so the initial line cannot fit 512 once its CRLF
; is charged, and the emitted effect is not a reply.
(defconst *fn-nntp-oversize-group-archive*
  (fn-initial-state (list *fn-nntp-group-497*)))
(assert-event (fn-statep *fn-nntp-oversize-group-archive*))
(assert-event (not (fn-nntp-projectionp *fn-nntp-oversize-group-archive*)))
(assert-event (not (fn-nntp-session-consistentp
                    *fn-nntp-forged-session* *fn-nntp-oversize-group-archive*)))
(assert-event
 (< *fn-nntp-max-response-octets*
    (+ (len (fn-nntp-listgroup-initial *fn-nntp-oversize-group-archive*
                                       *fn-nntp-group-497*))
       2)))
(assert-event
 (not (fn-nntp-effectsp
       (fn-nntp-result-effects
        (fn-nntp-step *fn-nntp-forged-session* *fn-nntp-oversize-group-archive* *fn-nntp-env0*
                      (list :command
                            (append (fn-nntp-string-octets "LISTGROUP ")
                                    (fn-nntp-string-octets *fn-nntp-group-497*))))))))
; The CRLF-bearing group name is not a witness on this axis, and the honest
; record of that is the fact itself.  LIST emits the name inside a multi-line
; block, where the injected CRLF reads as an ordinary line break and the
; octets re-parse as a well-formed response.  Effect typing is a grammar over
; emitted octets: it frames and bounds them, and does not claim to detect a
; splice that is grammatically a line.  What keeps such a name off the wire is
; the configuration refusal above, which denies the projection outright.
(assert-event
 (fn-nntp-effectsp
  (fn-nntp-result-effects
   (fn-nntp-step *fn-nntp-forged-session* *fn-nntp-unsafe-group-archive* *fn-nntp-env0*
                 '(:command (76 73 83 84))))))
(must-fail
 (thm (fn-nntp-effectsp
       (fn-nntp-result-effects (fn-nntp-step session archive *fn-nntp-env0* wire-event)))))

; The same session against a projectable archive is well formed, so the
; separating witness separates on more than the weakest clause.
(assert-event
 (fn-nntp-effectsp
  (fn-nntp-result-effects
   (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0* '(:command (76 73 83 84))))))
(assert-event
 (fn-nntp-effectsp
  (fn-nntp-result-effects
   (fn-nntp-step (fn-nntp-result-session *fn-nntp-mixed-group*) *fn-nntp-mixed-archive* *fn-nntp-env0*
                 '(:command (65 82 84 73 67 76 69 32 49))))))
(assert-event
 (fn-nntp-replyp
  (fn-nntp-crlf (fn-nntp-string-octets "501 syntax error"))))
(assert-event
 (not (fn-nntp-replyp '(54 53))))
(assert-event (not (fn-nntp-effectp '(:reply (65)))))
(assert-event (not (fn-nntp-effectp '(:reply (50 48 53 13 10 50 48 53)))))
(assert-event (fn-nntp-effectp '(:reply (50 48 53 13 10))))

; fn-nntp-group-selects-the-first-available-article: both hypotheses have force.
(assert-event
 (equal (fn-nntp-result-session
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0*
                       '(:command (71 82 79 85 80 32 110 111 46 115 117 99 104))))
        *fn-nntp-session0*))
(assert-event
 (null (fn-nntp-session-current (fn-nntp-result-session *fn-nntp-empty-group*))))
(assert-event
 (not (equal (fn-nntp-session-current (fn-nntp-result-session *fn-nntp-empty-group*))
             (fn-nntp-group-low "fn.empty" (fn-state-articles *fn-nntp-archive*)))))
(must-fail
 (thm (equal (fn-nntp-session-current
              (fn-nntp-result-session (fn-nntp-group-result session archive group)))
             (fn-nntp-group-low group (fn-state-articles archive)))))

; -----------------------------------------------------------------------------
; acceptance permits opaque strings and bytes; the projection refuses unsafe
; committed data before it can interpolate CRLF into any response line.
(defconst *fn-nntp-unsafe-id*
  (coerce (list (code-char 60) (code-char 120) (code-char 62)
                (code-char 13) (code-char 10) (code-char 50) (code-char 48) (code-char 53))
          'string))
(defconst *fn-nntp-unsafe-id-prepared*
  (fn-accept-prepare *fn-nntp-empty-archive* 2 *fn-nntp-unsafe-id*
                     *fn-nntp-payload* '("fn.letters")))
(defconst *fn-nntp-unsafe-id-archive*
  (fn-accept-complete *fn-nntp-unsafe-id-prepared* 0 2 :durable))
(defconst *fn-nntp-unsafe-payload-prepared*
  (fn-accept-prepare *fn-nntp-empty-archive* 3 "<payload@invalid>"
                     '(72 101 97 100 58 32 120 13 10 13 10 66) '("fn.letters")))
(defconst *fn-nntp-unsafe-payload-archive*
  (fn-accept-complete *fn-nntp-unsafe-payload-prepared* 0 3 :durable))
(assert-event (fn-statep *fn-nntp-unsafe-id-archive*))
(assert-event (fn-statep *fn-nntp-unsafe-payload-archive*))
; Both configurations now open; the one damaged article answers for itself.
(assert-event (fn-nntp-projectionp *fn-nntp-unsafe-id-archive*))
(assert-event (fn-nntp-projectionp *fn-nntp-unsafe-payload-archive*))
(defconst *fn-nntp-unsafe-id-session*
  (fn-nntp-open-session *fn-nntp-unsafe-id-archive*))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step
          (fn-nntp-result-session
           (fn-nntp-step *fn-nntp-unsafe-id-session* *fn-nntp-unsafe-id-archive*
                         '(:command (71 82 79 85 80 32 102 110 46 108 101 116 116 101 114 115))))
          *fn-nntp-unsafe-id-archive* *fn-nntp-env0* '(:command (83 84 65 84 32 49))))
        '((:reply (53 48 51 32 115 116 111 114 101 100 32 97 114 116 105 99 108 101 32 105 100 101 110 116 105 102 105 101 114 32 117 110 97 118 97 105 108 97 98 108 101 13 10)))))
(defconst *fn-nntp-unsafe-payload-session*
  (fn-nntp-open-session *fn-nntp-unsafe-payload-archive*))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step
          (fn-nntp-result-session
           (fn-nntp-step *fn-nntp-unsafe-payload-session* *fn-nntp-unsafe-payload-archive*
                         '(:command (71 82 79 85 80 32 102 110 46 108 101 116 116 101 114 115))))
          *fn-nntp-unsafe-payload-archive* *fn-nntp-env0* '(:command (65 82 84 73 67 76 69))))
        '((:reply (53 48 51 32 115 116 111 114 101 100 32 97 114 116 105 99 108 101 32 102 114 97 109 105 110 103 32 117 110 97 118 97 105 108 97 98 108 101 13 10)))))
; A payload carrying NUL cannot be sent in a multi-line block (RFC 3977 3.1.1).
(assert-event
 (not (fn-nntp-article-framedp
       (fn-make-article "<nul@invalid>" '(72 58 32 120 13 10 13 10 0 13 10)
                        '("fn.letters") '(("fn.letters" . 1)) t))))

; -----------------------------------------------------------------------------
; RFC 3977 sections 4 and 7.6: LIST defaults to ACTIVE; its two locally
; supported variants accept one parsed wildmat and preserve session state.
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0* '(:command (76 73 83 84))))
        '((:reply (50 49 53 32 108 105 115 116 32 111 102 32 97 99 116 105 118 101 32 110 101 119 115 103 114 111 117 112 115 32 102 111 108 108 111 119 115 13 10
                   102 110 46 108 101 116 116 101 114 115 32 49 32 49 32 121 13 10
                   102 110 46 101 109 112 116 121 32 48 32 49 32 121 13 10 46 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0*
                       '(:command (76 73 83 84 32 65 67 84 73 86 69 32 102 110 46 101 109 112 116 121))))
        '((:reply (50 49 53 32 108 105 115 116 32 111 102 32 97 99 116 105 118 101 32 110 101 119 115 103 114 111 117 112 115 32 102 111 108 108 111 119 115 13 10
                   102 110 46 101 109 112 116 121 32 48 32 49 32 121 13 10 46 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0*
                       '(:command (76 73 83 84 32 78 69 87 83 71 82 79 85 80 83 32 102 110 46 108 101 116 116 101 114 115))))
        '((:reply (50 49 53 32 108 105 115 116 32 111 102 32 110 101 119 115 103 114 111 117 112 115 32 102 111 108 108 111 119 115 13 10
                   102 110 46 108 101 116 116 101 114 115 32 102 110 32 101 120 112 101 114 105 109 101 110 116 97 108 32 103 114 111 117 112 13 10 46 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0*
                       '(:command (76 73 83 84 32 65 67 84 73 86 69 32 110 111 46 42))))
        '((:reply (50 49 53 32 108 105 115 116 32 111 102 32 97 99 116 105 118 101 32 110 101 119 115 103 114 111 117 112 115 32 102 111 108 108 111 119 115 13 10 46 13 10)))))

; The pattern is parsed once before it is applied to configured groups.  Bad
; UTF-8, a command-line BOM, reserved wildmat punctuation, and non-ASCII in a
; command keyword all reject without changing an already selected session.
(defconst *fn-nntp-list-invalid*
  (fn-nntp-step (fn-nntp-result-session *fn-nntp-group*) *fn-nntp-archive* *fn-nntp-env0*
                '(:command (76 73 83 84 32 65 67 84 73 86 69 32 91))))
(assert-event (equal (fn-nntp-result-session *fn-nntp-list-invalid*)
                     (fn-nntp-result-session *fn-nntp-group*)))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-list-invalid*)
        '((:reply (53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step (fn-nntp-result-session *fn-nntp-group*) *fn-nntp-archive* *fn-nntp-env0*
                       '(:command (76 73 83 84 32 65 67 84 73 86 69 32 192 160))))
        '((:reply (53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step (fn-nntp-result-session *fn-nntp-group*) *fn-nntp-archive* *fn-nntp-env0*
                       '(:command (76 73 83 84 32 65 67 84 73 86 69 32 239 187 191 42))))
        '((:reply (53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0* '(:command (195 163 66 67))))
        '((:reply (53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0* '(:command (71 82 79 85 80 32 194 163))))
        '((:reply (53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))

; Unknown LIST variants are 501.  Known but unmaintained variants use 503 only
; for their RFC 3977 section 9.6 arity; forbidden/malformed arguments remain
; syntax errors.
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0* '(:command (76 73 83 84 32 88 46 68 65 84 65))))
        '((:reply (53 48 49 32 117 110 115 117 112 112 111 114 116 101 100 32 76 73 83 84 32 118 97 114 105 97 110 116 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0* '(:command (76 73 83 84 32 65 67 84 73 86 69 46 84 73 77 69 83 32 102 110 46 42))))
        '((:reply (53 48 51 32 100 97 116 97 32 105 116 101 109 32 110 111 116 32 115 116 111 114 101 100 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0* '(:command (76 73 83 84 32 68 73 83 84 82 73 66 46 80 65 84 83 32 120))))
        '((:reply (53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0* '(:command (76 73 83 84 32 72 69 65 68 69 82 83 32 77 83 71 73 68))))
        '((:reply (53 48 51 32 100 97 116 97 32 105 116 101 109 32 110 111 116 32 115 116 111 114 101 100 13 10)))))

; Core-side line and argument caps protect direct callers as well as the wire
; adapter.  LIST ACTIVE's second token is a variant keyword, not part of the
; argument budget: a 497-octet pattern fits its 511-octet CRLF-framed command;
; 498 is still under the total command cap but is rejected by wildmat parsing.
(defun fn-nntp-test-repeat (n byte)
  (if (zp n) nil
    (cons byte (fn-nntp-test-repeat (1- n) byte))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0*
                       (list :command
                             (append '(76 73 83 84 32 65 67 84 73 86 69 32)
                                     (fn-nntp-test-repeat 497 97)))))
        '((:reply (50 49 53 32 108 105 115 116 32 111 102 32 97 99 116 105 118 101 32 110 101 119 115 103 114 111 117 112 115 32 102 111 108 108 111 119 115 13 10 46 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0*
                       (list :command
                             (append '(76 73 83 84 32 65 67 84 73 86 69 32)
                                     (fn-nntp-test-repeat 498 97)))))
        '((:reply (53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0*
                       (list :command (fn-nntp-test-repeat 511 65))))
        '((:reply (53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))

; NEXT at the only article and QUIT have defined state/effect behavior.
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step (fn-nntp-result-session *fn-nntp-group*) *fn-nntp-archive* *fn-nntp-env0* '(:command (78 69 88 84))))
        '((:reply (52 50 49 32 110 111 32 110 101 120 116 32 97 114 116 105 99 108 101 13 10)))))
(defconst *fn-nntp-quit*
  (fn-nntp-step (fn-nntp-result-session *fn-nntp-group*) *fn-nntp-archive* *fn-nntp-env0* '(:command (81 85 73 84))))
(assert-event (equal (fn-nntp-result-effects *fn-nntp-quit*)
                     '((:reply (50 48 53 32 99 108 111 115 105 110 103 32 99 111 110 110 101 99 116 105 111 110 13 10)) (:close))))
(assert-event (equal (fn-nntp-session-openp (fn-nntp-result-session *fn-nntp-quit*)) nil))
(assert-event (equal (fn-nntp-session-projected (fn-nntp-result-session *fn-nntp-quit*)) t))

; RFC 3977 section 6.1.2 LISTGROUP selects the current group when omitted and
; resets its cursor to the group's first article even when a range excludes it.
(defconst *fn-nntp-listgroup-current*
  (fn-nntp-step (fn-nntp-result-session *fn-nntp-group*) *fn-nntp-archive* *fn-nntp-env0*
                '(:command (76 73 83 84 71 82 79 85 80))))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-listgroup-current*)
        '((:reply (50 49 49 32 49 32 49 32 49 32 102 110 46 108 101 116 116 101 114 115 32 108 105 115 116 32 102 111 108 108 111 119 115 13 10 49 13 10 46 13 10)))))
(assert-event (equal (fn-nntp-session-current
                      (fn-nntp-result-session *fn-nntp-listgroup-current*)) 1))
(defconst *fn-nntp-listgroup-open-empty*
  (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0*
                '(:command (76 73 83 84 71 82 79 85 80 32 102 110 46 108 101 116 116 101 114 115 32 50 45))))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-listgroup-open-empty*)
        '((:reply (50 49 49 32 49 32 49 32 49 32 102 110 46 108 101 116 116 101 114 115 32 108 105 115 116 32 102 111 108 108 111 119 115 13 10 46 13 10)))))
(assert-event (equal (fn-nntp-session-current
                      (fn-nntp-result-session *fn-nntp-listgroup-open-empty*)) 1))
(defconst *fn-nntp-listgroup-empty-group*
  (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0*
                '(:command (76 73 83 84 71 82 79 85 80 32 102 110 46 101 109 112 116 121))))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-listgroup-empty-group*)
        '((:reply (50 49 49 32 48 32 49 32 48 32 102 110 46 101 109 112 116 121 32 108 105 115 116 32 102 111 108 108 111 119 115 13 10 46 13 10)))))
(assert-event (equal (fn-nntp-session-current
                      (fn-nntp-result-session *fn-nntp-listgroup-empty-group*)) nil))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0* '(:command (76 73 83 84 71 82 79 85 80))))
        '((:reply (52 49 50 32 110 111 32 110 101 119 115 103 114 111 117 112 32 115 101 108 101 99 116 101 100 13 10)))))
(defconst *fn-nntp-listgroup-unknown*
  (fn-nntp-step (fn-nntp-result-session *fn-nntp-group*) *fn-nntp-archive* *fn-nntp-env0*
                '(:command (76 73 83 84 71 82 79 85 80 32 110 111 46 115 117 99 104))))
(assert-event (equal (fn-nntp-result-session *fn-nntp-listgroup-unknown*)
                     (fn-nntp-result-session *fn-nntp-group*)))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-listgroup-unknown*)
        '((:reply (52 49 49 32 110 111 32 115 117 99 104 32 110 101 119 115 103 114 111 117 112 13 10)))))
(defconst *fn-nntp-gone-session* (fn-nntp-make-session t "gone.group" 1 t))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-gone-session* *fn-nntp-archive* *fn-nntp-env0* '(:command (76 73 83 84 71 82 79 85 80))))
        '((:reply (52 49 50 32 110 111 32 110 101 119 115 103 114 111 117 112 32 115 101 108 101 99 116 101 100 13 10)))))
; There is no bare-range LISTGROUP form: the one argument is a group name.
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0* '(:command (76 73 83 84 71 82 79 85 80 32 49 45))))
        '((:reply (52 49 49 32 110 111 32 115 117 99 104 32 110 101 119 115 103 114 111 117 112 13 10)))))

; Sparse local allocation remains scoped to fn.sparse and is filtered
; inclusively by the requested range.  NEXT and LAST cross the gap.
(defconst *fn-nntp-sparse-groups* '("fn.sparse"))
(defconst *fn-nntp-sparse-a1*
  (fn-make-article "<one@sparse.invalid>" *fn-nntp-payload* '("fn.sparse")
                   '(("fn.sparse" . 1)) t))
(defconst *fn-nntp-sparse-a3*
  (fn-make-article "<three@sparse.invalid>" *fn-nntp-payload* '("fn.sparse")
                   '(("fn.sparse" . 3)) t))
(defconst *fn-nntp-sparse-archive*
  (fn-make-state *fn-nntp-sparse-groups* '(("fn.sparse" . 4))
                 (list *fn-nntp-sparse-a3* *fn-nntp-sparse-a1*) 0 nil nil))
(assert-event (fn-statep *fn-nntp-sparse-archive*))
(assert-event (fn-nntp-projectionp *fn-nntp-sparse-archive*))
(defconst *fn-nntp-sparse-session* (fn-nntp-open-session *fn-nntp-sparse-archive*))
(defconst *fn-nntp-listgroup-sparse*
  (fn-nntp-step *fn-nntp-sparse-session* *fn-nntp-sparse-archive* *fn-nntp-env0*
                '(:command (76 73 83 84 71 82 79 85 80 32 102 110 46 115 112 97 114 115 101 32 50 45 51))))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-listgroup-sparse*)
        '((:reply (50 49 49 32 50 32 49 32 51 32 102 110 46 115 112 97 114 115 101 32 108 105 115 116 32 102 111 108 108 111 119 115 13 10 51 13 10 46 13 10)))))
(assert-event (equal (fn-nntp-session-current
                      (fn-nntp-result-session *fn-nntp-listgroup-sparse*)) 1))
(defconst *fn-nntp-listgroup-reversed*
  (fn-nntp-step *fn-nntp-sparse-session* *fn-nntp-sparse-archive* *fn-nntp-env0*
                '(:command (76 73 83 84 71 82 79 85 80 32 102 110 46 115 112 97 114 115 101 32 51 45 49))))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-listgroup-reversed*)
        '((:reply (50 49 49 32 50 32 49 32 51 32 102 110 46 115 112 97 114 115 101 32 108 105 115 116 32 102 111 108 108 111 119 115 13 10 46 13 10)))))
; The LISTGROUP block is in numerical order even though the committed article
; list is not (RFC 3977 section 6.1.2.2).
(defconst *fn-nntp-listgroup-all-sparse*
  (fn-nntp-step *fn-nntp-sparse-session* *fn-nntp-sparse-archive* *fn-nntp-env0*
                '(:command (76 73 83 84 71 82 79 85 80 32 102 110 46 115 112 97 114 115 101))))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-listgroup-all-sparse*)
        '((:reply (50 49 49 32 50 32 49 32 51 32 102 110 46 115 112 97 114 115 101 32 108 105 115 116 32 102 111 108 108 111 119 115 13 10 49 13 10 51 13 10 46 13 10)))))
(assert-event
 (fn-nntp-orderedp (fn-nntp-group-range-numbers
                    "fn.sparse" 1 2147483647 (fn-state-articles *fn-nntp-sparse-archive*))))
; NEXT and LAST move the cursor to an available number and nowhere else.
(defconst *fn-nntp-sparse-next*
  (fn-nntp-step (fn-nntp-result-session *fn-nntp-listgroup-all-sparse*)
                *fn-nntp-sparse-archive* *fn-nntp-env0* '(:command (78 69 88 84))))
(assert-event (equal (fn-nntp-session-current
                      (fn-nntp-result-session *fn-nntp-sparse-next*)) 3))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-sparse-next*)
        '((:reply (50 50 51 32 51 32 60 116 104 114 101 101 64 115 112 97 114 115 101 46 105 110 118 97 108 105 100 62 32 114 101 116 114 105 101 118 101 100 13 10)))))
(defconst *fn-nntp-sparse-last*
  (fn-nntp-step (fn-nntp-result-session *fn-nntp-sparse-next*)
                *fn-nntp-sparse-archive* *fn-nntp-env0* '(:command (76 65 83 84))))
(assert-event (equal (fn-nntp-session-current
                      (fn-nntp-result-session *fn-nntp-sparse-last*)) 1))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step (fn-nntp-result-session *fn-nntp-sparse-last*)
                       *fn-nntp-sparse-archive* *fn-nntp-env0* '(:command (76 65 83 84))))
        '((:reply (52 50 50 32 110 111 32 112 114 101 118 105 111 117 115 32 97 114 116 105 99 108 101 13 10)))))
; A number inside the gap is 423, not a silent success.
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step (fn-nntp-result-session *fn-nntp-listgroup-all-sparse*)
                       *fn-nntp-sparse-archive* *fn-nntp-env0* '(:command (83 84 65 84 32 50))))
        '((:reply (52 50 51 32 110 111 32 97 114 116 105 99 108 101 32 119 105 116 104 32 116 104 97 116 32 110 117 109 98 101 114 13 10)))))

; Parser boundaries: single, open, leading-zero, reversed-empty, malformed,
; and excess-argument forms.  12/120 protect the decimal accumulator regression.
(assert-event (equal (fn-nntp-parse-range '(49 50)) '(:ok 12 12)))
(assert-event (equal (fn-nntp-parse-range '(49 50 48 45)) '(:ok 120 2147483647)))
(assert-event (equal (fn-nntp-parse-range '(48 48 49 50 45 49 50)) '(:ok 12 12)))
(assert-event (equal (fn-nntp-parse-range '(57 45 49)) '(:ok 9 1)))
(assert-event (not (fn-nntp-range-okp (fn-nntp-parse-range '(45 49)))))
(assert-event (not (fn-nntp-range-okp (fn-nntp-parse-range '(49 45 50 45 51)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0*
                       '(:command (76 73 83 84 71 82 79 85 80 32 102 110 46 108 101 116 116 101 114 115 32 45 49))))
        '((:reply (53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* *fn-nntp-env0*
                       '(:command (76 73 83 84 71 82 79 85 80 32 102 110 46 108 101 116 116 101 114 115 32 49 32 50))))
        '((:reply (53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
