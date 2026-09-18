; Bounded article syntax parser vectors.  These exercise syntax preservation,
; folding, unknown/repeated fields, MIME-shaped bytes, and hostile framing.
(in-package "ACL2")
(include-book "../../books/article")

(defconst *fn-article-test-source*
  '(88 45 84 97 103 58 32 111 110 101 13 10
    83 117 98 106 101 99 116 58 32 97 108 112 104 97 13 10
    9 98 101 116 97 13 10
    88 45 84 97 103 58 32 116 119 111 13 10
    67 111 110 116 101 110 116 45 84 121 112 101 58 32 116 101 120 116 47
    112 108 97 105 110 59 32 99 104 97 114 115 101 116 61 85 84 70 45 56 13 10
    13 10
    0 255 40 114 101 97 100 32 34 110 111 116 32 76 105 115 112 34 41
    227 129 147 13 10))

(defconst *fn-article-test-header*
  '(88 45 84 97 103 58 32 111 110 101 13 10
    83 117 98 106 101 99 116 58 32 97 108 112 104 97 13 10
    9 98 101 116 97 13 10
    88 45 84 97 103 58 32 116 119 111 13 10
    67 111 110 116 101 110 116 45 84 121 112 101 58 32 116 101 120 116 47
    112 108 97 105 110 59 32 99 104 97 114 115 101 116 61 85 84 70 45 56 13 10))

(defconst *fn-article-test-body*
  '(0 255 40 114 101 97 100 32 34 110 111 116 32 76 105 115 112 34 41
    227 129 147 13 10))

(defconst *fn-article-test-result* (fn-article-parse *fn-article-test-source*))
(assert-event (fn-article-result-okp *fn-article-test-result*))
(defconst *fn-article-test-article*
  (fn-article-result-article *fn-article-test-result*))
(assert-event (fn-article-syntax-p *fn-article-test-article*))
(assert-event (equal (fn-article-header *fn-article-test-article*)
                     *fn-article-test-header*))
(assert-event (equal (fn-article-body *fn-article-test-article*)
                     *fn-article-test-body*))
(assert-event (equal (fn-article-source *fn-article-test-article*)
                     *fn-article-test-source*))

; Lowercase lookup leaves raw spelling, ordering, repeated unknown fields, and
; folding available in the field view.
(defconst *fn-article-x-tags*
  (fn-article-get-headers *fn-article-test-article* '(120 45 116 97 103)))
(assert-event (equal (len *fn-article-x-tags*) 2))
(assert-event (equal (fn-article-field-raw-lines (car *fn-article-x-tags*))
                     '((88 45 84 97 103 58 32 111 110 101))))
(assert-event (equal (fn-article-field-unfolded-value (car *fn-article-x-tags*))
                     '(32 111 110 101)))
(defconst *fn-article-subject*
  (fn-article-get-header *fn-article-test-article*
                         '(83 85 66 74 69 67 84)))
(assert-event (equal (fn-article-field-name *fn-article-subject*)
                     '(115 117 98 106 101 99 116)))
(assert-event (equal (fn-article-field-raw-lines *fn-article-subject*)
                     '((83 117 98 106 101 99 116 58 32 97 108 112 104 97)
                       (9 98 101 116 97))))
(assert-event (equal (fn-article-field-unfolded-value *fn-article-subject*)
                     '(32 97 108 112 104 97 9 98 101 116 97)))

; Complete header/body separator, strict CRLF, field syntax, and orphan folds.
(assert-event (equal (fn-article-parse '(83 117 98 106 101 99 116 58 32 120 13 10))
                     '(:error :missing-separator)))
(assert-event (equal (fn-article-parse '(83 117 98 106 101 99 116 58 32 120 10 10))
                     '(:error :invalid-header)))
(assert-event (equal (fn-article-parse '(9 120 13 10 13 10))
                     '(:error :invalid-header)))
(assert-event (equal (fn-article-parse '(88 58 121 13 10 13 10))
                     '(:error :invalid-header)))
(assert-event (equal (fn-article-parse '(88 58 32 1 13 10 13 10))
                     '(:error :invalid-header)))
(assert-event (equal (fn-article-parse '(88 58 32 120 13 10 13 10 0 10))
                     '(:error :invalid-header)))

; Fixed preflight and physical-line limits distinguish hostile oversize input.
(defun fn-article-test-repeat (n byte)
  (if (zp n) nil
    (cons byte (fn-article-test-repeat (1- n) byte))))

(defun fn-article-test-fields (n)
  (if (zp n)
      '(13 10)
    (append '(88 58 32 120 13 10)
            (fn-article-test-fields (1- n)))))

(defun fn-article-test-folds (n)
  (if (zp n)
      '(13 10)
    (append '(9 120 13 10) (fn-article-test-folds (1- n)))))

(defun fn-article-test-long-folds (n)
  (if (zp n)
      '(13 10)
    (append (cons 9 (append (fn-article-test-repeat 64 120) '(13 10)))
            (fn-article-test-long-folds (1- n)))))

(assert-event (equal (fn-article-parse
                      (append (fn-article-test-repeat 999 65)
                              '(58 32 120 13 10 13 10)))
                     '(:error :limit)))
(assert-event (equal (fn-article-parse (fn-article-test-repeat 32769 65))
                     '(:error :limit)))
(assert-event (fn-article-result-okp
               (fn-article-parse (fn-article-test-fields 64))))
(assert-event (equal (fn-article-parse (fn-article-test-fields 65))
                     '(:error :limit)))

; Exactly 128 physical header lines (one field plus 127 folds) are accepted;
; the next fold exceeds the line-count cap.  Separately, 123 valid short-enough
; folds exceed only the 8,192-octet header budget.
(assert-event (fn-article-result-okp
               (fn-article-parse
                (append '(88 58 32 120 13 10) (fn-article-test-folds 127)))))
(assert-event (equal
               (fn-article-parse
                (append '(88 58 32 120 13 10) (fn-article-test-folds 128)))
               '(:error :limit)))
(assert-event (equal
               (fn-article-parse
                (append '(88 58 32 120 13 10)
                        (fn-article-test-long-folds 123)))
               '(:error :limit)))
