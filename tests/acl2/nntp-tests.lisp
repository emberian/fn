; Independent expected transcripts for the experimental reader-only session.
(in-package "ACL2")
(include-book "../../books/nntp")

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
(defconst *fn-nntp-session0* (fn-nntp-initial-session))
(assert-event (fn-statep *fn-nntp-archive*))
(assert-event (fn-nntp-sessionp *fn-nntp-session0*))

; Decimal parsing is left-to-right: 12 is twelve, not twenty-one.  Leading
; zeroes are accepted, and the RFC 3977 maximum is the last accepted value.
(assert-event (equal (fn-nntp-decimal-value '(49 50)) 12))
(assert-event (equal (fn-nntp-decimal-value '(49 50 48)) 120))
(assert-event (equal (fn-nntp-decimal-value '(48 48 49 50)) 12))
(assert-event (fn-nntp-number-tokenp '(50 49 52 55 52 56 51 54 52 55)))
(assert-event (not (fn-nntp-number-tokenp '(50 49 52 55 52 56 51 54 52 56))))

; Exact selected-group transcript; mixed case changes only the command keyword.
(defconst *fn-nntp-group*
  (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive*
                '(:command (103 82 111 85 112 32 102 110 46 108 101 116 116 101 114 115))))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-group*)
        '((:reply (50 49 49 32 49 32 49 32 49 32 102 110 46 108 101 116 116 101 114 115 13 10)))))
(assert-event (equal (fn-nntp-session-group (fn-nntp-result-session *fn-nntp-group*)) "fn.letters"))
(assert-event (equal (fn-nntp-session-current (fn-nntp-result-session *fn-nntp-group*)) 1))

; HEAD excludes the separator and BODY excludes it, while BODY dot-stuffs the
; stored dot-prefixed line.  Their expected wire octets include every CRLF.
(defconst *fn-nntp-head*
  (fn-nntp-step (fn-nntp-result-session *fn-nntp-group*) *fn-nntp-archive*
                '(:command (72 69 65 68))))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-head*)
        '((:reply (50 50 49 32 49 32 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62 32 104 101 97 100 101 114 115 32 102 111 108 108 111 119 13 10
                   77 101 115 115 97 103 101 45 73 68 58 32 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62 13 10
                   83 117 98 106 101 99 116 58 32 84 101 115 116 13 10 46 13 10)))))
(defconst *fn-nntp-body*
  (fn-nntp-step (fn-nntp-result-session *fn-nntp-group*) *fn-nntp-archive*
                '(:command (66 79 68 89))))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-body*)
        '((:reply (50 50 50 32 49 32 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62 32 98 111 100 121 32 102 111 108 108 111 119 115 13 10
                   72 101 108 108 111 13 10 46 46 100 111 116 13 10 46 13 10)))))

; Message-ID is exact-case and leaves group/cursor unchanged; numeric retrieval
; without a group is 412, and no-current is 420.
(defconst *fn-nntp-by-id*
  (fn-nntp-step (fn-nntp-result-session *fn-nntp-group*) *fn-nntp-archive*
                '(:command (83 84 65 84 32 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62))))
(assert-event (equal (fn-nntp-result-session *fn-nntp-by-id*)
                     (fn-nntp-result-session *fn-nntp-group*)))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-by-id*)
        '((:reply (50 50 51 32 48 32 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62 32 114 101 116 114 105 101 118 101 100 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step (fn-nntp-result-session *fn-nntp-group*) *fn-nntp-archive*
                       '(:command (83 84 65 84 32 60 99 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62))))
        '((:reply (52 51 48 32 110 111 32 97 114 116 105 99 108 101 32 119 105 116 104 32 116 104 97 116 32 109 101 115 115 97 103 101 45 105 100 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* '(:command (83 84 65 84 32 49))))
        '((:reply (52 49 50 32 110 111 32 110 101 119 115 103 114 111 117 112 32 115 101 108 101 99 116 101 100 13 10)))))
(defconst *fn-nntp-empty-group*
  (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive*
                '(:command (71 82 79 85 80 32 102 110 46 101 109 112 116 121))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step (fn-nntp-result-session *fn-nntp-empty-group*) *fn-nntp-archive* '(:command (83 84 65 84))))
        '((:reply (52 50 48 32 110 111 32 99 117 114 114 101 110 116 32 97 114 116 105 99 108 101 13 10)))))

; Error and capability transcript: no READER/POST/TLS/auth claim; bad syntax is
; 501 and recognized but unsupported POST is 500.
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* '(:command (80 79 83 84))))
        '((:reply (53 48 48 32 99 111 109 109 97 110 100 32 110 111 116 32 114 101 99 111 103 110 105 122 101 100 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* '(:command (71 82 79 85 80 32))))
        '((:reply (53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* '(:command (32 71 82 79 85 80 32 102 110 46 108 101 116 116 101 114 115))))
        '((:reply (53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* '(:command (83 84 65 84 32 48))))
        '((:reply (53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
(defconst *fn-nntp-caps*
  (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* '(:command (67 65 80 65 66 73 76 73 84 73 69 83))))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-caps*)
        '((:reply (49 48 49 32 99 97 112 97 98 105 108 105 116 121 32 108 105 115 116 32 102 111 108 108 111 119 115 13 10
                   86 69 82 83 73 79 78 32 50 13 10 73 77 80 76 69 77 69 78 84 65 84 73 79 78 32 102 110 45 110 110 116 112 45 108 97 98 13 10 46 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive*
                       '(:command (67 65 80 65 66 73 76 73 84 73 69 83 32 65 85 84 79 85 80 68 65 84 69))))
        (fn-nntp-result-effects *fn-nntp-caps*)))

; acceptance permits opaque strings and bytes.  The NNTP projection refuses
; unsafe committed data before it can interpolate CRLF into any response line.
(defconst *fn-nntp-unsafe-id*
  (coerce (list (code-char 60) (code-char 120) (code-char 62)
                (code-char 13) (code-char 10) (code-char 50) (code-char 48) (code-char 53))
          'string))
(defconst *fn-nntp-unsafe-id-prepared*
  (fn-accept-prepare *fn-nntp-empty-archive* 2 *fn-nntp-unsafe-id*
                     *fn-nntp-payload* '("fn.letters")))
(defconst *fn-nntp-unsafe-id-archive*
  (fn-accept-complete *fn-nntp-unsafe-id-prepared* 0 2 :durable))
(defconst *fn-nntp-unsafe-group*
  (coerce (list (code-char 102) (code-char 110) (code-char 13) (code-char 10)
                (code-char 50) (code-char 48) (code-char 53)) 'string))
(defconst *fn-nntp-unsafe-group-archive* (fn-initial-state (list *fn-nntp-unsafe-group*)))
(defconst *fn-nntp-unsafe-payload-prepared*
  (fn-accept-prepare *fn-nntp-empty-archive* 3 "<payload@invalid>"
                     '(72 101 97 100 58 32 120 13 10 13 10 66) '("fn.letters")))
(defconst *fn-nntp-unsafe-payload-archive*
  (fn-accept-complete *fn-nntp-unsafe-payload-prepared* 0 3 :durable))
(assert-event (fn-statep *fn-nntp-unsafe-id-archive*))
(assert-event (fn-statep *fn-nntp-unsafe-group-archive*))
(assert-event (fn-statep *fn-nntp-unsafe-payload-archive*))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-unsafe-id-archive* '(:command (83 84 65 84))))
        '((:reply (53 48 51 32 97 114 99 104 105 118 101 32 112 114 111 106 101 99 116 105 111 110 32 117 110 97 118 97 105 108 97 98 108 101 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-unsafe-group-archive* '(:command (76 73 83 84))))
        '((:reply (53 48 51 32 97 114 99 104 105 118 101 32 112 114 111 106 101 99 116 105 111 110 32 117 110 97 118 97 105 108 97 98 108 101 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-unsafe-payload-archive* '(:command (65 82 84 73 67 76 69))))
        '((:reply (53 48 51 32 97 114 99 104 105 118 101 32 112 114 111 106 101 99 116 105 111 110 32 117 110 97 118 97 105 108 97 98 108 101 13 10)))))

; NEXT at the only article and QUIT have defined state/effect behavior.
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step (fn-nntp-result-session *fn-nntp-group*) *fn-nntp-archive* '(:command (78 69 88 84))))
        '((:reply (52 50 49 32 110 111 32 110 101 120 116 32 97 114 116 105 99 108 101 13 10)))))
(defconst *fn-nntp-quit*
  (fn-nntp-step (fn-nntp-result-session *fn-nntp-group*) *fn-nntp-archive* '(:command (81 85 73 84))))
(assert-event (equal (fn-nntp-result-effects *fn-nntp-quit*)
                     '((:reply (50 48 53 32 99 108 111 115 105 110 103 32 99 111 110 110 101 99 116 105 111 110 13 10)) (:close))))
(assert-event (equal (fn-nntp-session-openp (fn-nntp-result-session *fn-nntp-quit*)) nil))

; RFC 3977 section 6.1.2 LISTGROUP selects the current group when omitted and
; resets its cursor to the group's first article even when a range excludes it.
(defconst *fn-nntp-listgroup-current*
  (fn-nntp-step (fn-nntp-result-session *fn-nntp-group*) *fn-nntp-archive*
                '(:command (76 73 83 84 71 82 79 85 80))))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-listgroup-current*)
        '((:reply (50 49 49 32 49 32 49 32 49 32 102 110 46 108 101 116 116 101 114 115 32 108 105 115 116 32 102 111 108 108 111 119 115 13 10 49 13 10 46 13 10)))))
(assert-event (equal (fn-nntp-session-current
                      (fn-nntp-result-session *fn-nntp-listgroup-current*)) 1))
(defconst *fn-nntp-listgroup-open-empty*
  (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive*
                '(:command (76 73 83 84 71 82 79 85 80 32 102 110 46 108 101 116 116 101 114 115 32 50 45))))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-listgroup-open-empty*)
        '((:reply (50 49 49 32 49 32 49 32 49 32 102 110 46 108 101 116 116 101 114 115 32 108 105 115 116 32 102 111 108 108 111 119 115 13 10 46 13 10)))))
(assert-event (equal (fn-nntp-session-current
                      (fn-nntp-result-session *fn-nntp-listgroup-open-empty*)) 1))
(defconst *fn-nntp-listgroup-empty-group*
  (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive*
                '(:command (76 73 83 84 71 82 79 85 80 32 102 110 46 101 109 112 116 121))))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-listgroup-empty-group*)
        '((:reply (50 49 49 32 48 32 49 32 48 32 102 110 46 101 109 112 116 121 32 108 105 115 116 32 102 111 108 108 111 119 115 13 10 46 13 10)))))
(assert-event (equal (fn-nntp-session-current
                      (fn-nntp-result-session *fn-nntp-listgroup-empty-group*)) nil))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* '(:command (76 73 83 84 71 82 79 85 80))))
        '((:reply (52 49 50 32 110 111 32 110 101 119 115 103 114 111 117 112 32 115 101 108 101 99 116 101 100 13 10)))))
(defconst *fn-nntp-listgroup-unknown*
  (fn-nntp-step (fn-nntp-result-session *fn-nntp-group*) *fn-nntp-archive*
                '(:command (76 73 83 84 71 82 79 85 80 32 110 111 46 115 117 99 104))))
(assert-event (equal (fn-nntp-result-session *fn-nntp-listgroup-unknown*)
                     (fn-nntp-result-session *fn-nntp-group*)))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-listgroup-unknown*)
        '((:reply (52 49 49 32 110 111 32 115 117 99 104 32 110 101 119 115 103 114 111 117 112 13 10)))))
(defconst *fn-nntp-stale-session* (fn-nntp-make-session t "gone.group" 1))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-stale-session* *fn-nntp-archive* '(:command (76 73 83 84 71 82 79 85 80))))
        '((:reply (52 49 50 32 110 111 32 110 101 119 115 103 114 111 117 112 32 115 101 108 101 99 116 101 100 13 10)))))
; There is no bare-range LISTGROUP form: the one argument is a group name.
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive* '(:command (76 73 83 84 71 82 79 85 80 32 49 45))))
        '((:reply (52 49 49 32 110 111 32 115 117 99 104 32 110 101 119 115 103 114 111 117 112 13 10)))))

; Sparse local allocation remains scoped to fn.sparse and is filtered
; inclusively by the requested range.
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
(defconst *fn-nntp-listgroup-sparse*
  (fn-nntp-step *fn-nntp-session0* *fn-nntp-sparse-archive*
                '(:command (76 73 83 84 71 82 79 85 80 32 102 110 46 115 112 97 114 115 101 32 50 45 51))))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-listgroup-sparse*)
        '((:reply (50 49 49 32 50 32 49 32 51 32 102 110 46 115 112 97 114 115 101 32 108 105 115 116 32 102 111 108 108 111 119 115 13 10 51 13 10 46 13 10)))))
(assert-event (equal (fn-nntp-session-current
                      (fn-nntp-result-session *fn-nntp-listgroup-sparse*)) 1))
(defconst *fn-nntp-listgroup-reversed*
  (fn-nntp-step *fn-nntp-session0* *fn-nntp-sparse-archive*
                '(:command (76 73 83 84 71 82 79 85 80 32 102 110 46 115 112 97 114 115 101 32 51 45 49))))
(assert-event
 (equal (fn-nntp-result-effects *fn-nntp-listgroup-reversed*)
        '((:reply (50 49 49 32 50 32 49 32 51 32 102 110 46 115 112 97 114 115 101 32 108 105 115 116 32 102 111 108 108 111 119 115 13 10 46 13 10)))))

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
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive*
                       '(:command (76 73 83 84 71 82 79 85 80 32 102 110 46 108 101 116 116 101 114 115 32 45 49))))
        '((:reply (53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
(assert-event
 (equal (fn-nntp-result-effects
         (fn-nntp-step *fn-nntp-session0* *fn-nntp-archive*
                       '(:command (76 73 83 84 71 82 79 85 80 32 102 110 46 108 101 116 116 101 114 115 32 49 32 50))))
        '((:reply (53 48 49 32 115 121 110 116 97 120 32 101 114 114 111 114 13 10)))))
