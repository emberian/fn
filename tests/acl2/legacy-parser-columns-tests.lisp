(in-package "ACL2")
(include-book "../../books/legacy-parser-columns")

(defun lpvct-repeat (n) (if (zp n) nil (cons 120 (lpvct-repeat (1- n)))))

(defconst *lpvct-columns* (fn-novlp-columns nil *fn-novlp-names*))
(defconst *lpvct-name* '(83 117 98 106 101 99 116))
(defconst *lpvct-value* '(32 120))
(defconst *lpvct-line* (append *lpvct-name* (cons 58 (append *lpvct-value* '(13 10)))))
(defconst *lpvct-state* (fn-nlv-run *lpvct-line* (fn-lpc-header-begin) 0 0 :pin))
(defconst *lpvct-field* (fn-article-make-field (list (append *lpvct-name* (cons 58 *lpvct-value*))) *fn-nov-subject-name* *lpvct-value*))
(defconst *lpvct-open-line* (append *lpvct-name* '(58 13 10)))
(defconst *lpvct-open-state* (fn-nlv-run *lpvct-open-line* (fn-lpc-header-begin) 0 0 :pin))
(defconst *lpvct-open-field* (fn-article-make-field (list (append *lpvct-name* '(58))) *fn-nov-subject-name* nil))

; Literal full antecedent/conclusion; removals negate only their named premise.
(defthm lpvct-new-field-positive
  (let* ((s *lpvct-state*)
         (source *lpvct-line*)
         (current *lpvct-field*)
         (columns *lpvct-columns*)
         (name *lpvct-name*)
         (value '(32 121))
         (line (append name (cons 58 (append value '(13 10))))))
    (and (fn-lpv-header-equiv s source current columns 0 :pin)
         (fn-article-field-closedp current)
         (fn-article-namep name)
         (fn-article-header-bytes-p value)
         (or (not (consp value)) (fn-article-wspp (car value)))
         (<= (+ (len name) 1 (len value)) *fn-article-max-line-octets*)
         (fn-lpv-header-equiv
 (fn-nlv-run line s (len source) 0 :pin) (append source line)
 (fn-article-make-field (list (append name (cons 58 value))) (fn-article-ascii-downcase name) value)
 (fn-novlp-add-field columns current *fn-novlp-names*) 0 :pin)))
  :rule-classes nil)

; Literal full antecedent/conclusion; removals negate only their named premise.
(defthm lpvct-new-field-without-invariant
  (let* ((s (fn-lpc-put 8 '((9 0 1 :pin) nil nil nil nil) *lpvct-state*))
         (source *lpvct-line*)
         (current *lpvct-field*)
         (columns *lpvct-columns*)
         (name *lpvct-name*)
         (value '(32 121))
         (line (append name (cons 58 (append value '(13 10))))))
    (and (not (fn-lpv-header-equiv s source current columns 0 :pin))
         (fn-article-field-closedp current)
         (fn-article-namep name)
         (fn-article-header-bytes-p value)
         (or (not (consp value)) (fn-article-wspp (car value)))
         (<= (+ (len name) 1 (len value)) *fn-article-max-line-octets*)
         (not (fn-lpv-header-equiv
 (fn-nlv-run line s (len source) 0 :pin) (append source line)
 (fn-article-make-field (list (append name (cons 58 value))) (fn-article-ascii-downcase name) value)
 (fn-novlp-add-field columns current *fn-novlp-names*) 0 :pin))))
  :rule-classes nil)

; Literal full antecedent/conclusion; removals negate only their named premise.
(defthm lpvct-new-field-without-closed-current
  (let* ((s *lpvct-open-state*)
         (source *lpvct-open-line*)
         (current *lpvct-open-field*)
         (columns *lpvct-columns*)
         (name *lpvct-name*)
         (value '(32 121))
         (line (append name (cons 58 (append value '(13 10))))))
    (and (fn-lpv-header-equiv s source current columns 0 :pin)
         (not (fn-article-field-closedp current))
         (fn-article-namep name)
         (fn-article-header-bytes-p value)
         (or (not (consp value)) (fn-article-wspp (car value)))
         (<= (+ (len name) 1 (len value)) *fn-article-max-line-octets*)
         (not (fn-lpv-header-equiv
 (fn-nlv-run line s (len source) 0 :pin) (append source line)
 (fn-article-make-field (list (append name (cons 58 value))) (fn-article-ascii-downcase name) value)
 (fn-novlp-add-field columns current *fn-novlp-names*) 0 :pin))))
  :rule-classes nil)

; Literal full antecedent/conclusion; removals negate only their named premise.
(defthm lpvct-new-field-without-name-grammar
  (let* ((s *lpvct-state*)
         (source *lpvct-line*)
         (current *lpvct-field*)
         (columns *lpvct-columns*)
         (name '(58))
         (value '(32 121))
         (line (append name (cons 58 (append value '(13 10))))))
    (and (fn-lpv-header-equiv s source current columns 0 :pin)
         (fn-article-field-closedp current)
         (not (fn-article-namep name))
         (fn-article-header-bytes-p value)
         (or (not (consp value)) (fn-article-wspp (car value)))
         (<= (+ (len name) 1 (len value)) *fn-article-max-line-octets*)
         (not (fn-lpv-header-equiv
 (fn-nlv-run line s (len source) 0 :pin) (append source line)
 (fn-article-make-field (list (append name (cons 58 value))) (fn-article-ascii-downcase name) value)
 (fn-novlp-add-field columns current *fn-novlp-names*) 0 :pin))))
  :rule-classes nil)

; Literal full antecedent/conclusion; removals negate only their named premise.
(defthm lpvct-new-field-without-value-grammar
  (let* ((s *lpvct-state*)
         (source *lpvct-line*)
         (current *lpvct-field*)
         (columns *lpvct-columns*)
         (name *lpvct-name*)
         (value '(32 0))
         (line (append name (cons 58 (append value '(13 10))))))
    (and (fn-lpv-header-equiv s source current columns 0 :pin)
         (fn-article-field-closedp current)
         (fn-article-namep name)
         (not (fn-article-header-bytes-p value))
         (or (not (consp value)) (fn-article-wspp (car value)))
         (<= (+ (len name) 1 (len value)) *fn-article-max-line-octets*)
         (not (fn-lpv-header-equiv
 (fn-nlv-run line s (len source) 0 :pin) (append source line)
 (fn-article-make-field (list (append name (cons 58 value))) (fn-article-ascii-downcase name) value)
 (fn-novlp-add-field columns current *fn-novlp-names*) 0 :pin))))
  :rule-classes nil)

; Literal full antecedent/conclusion; removals negate only their named premise.
(defthm lpvct-new-field-without-initial-wsp
  (let* ((s *lpvct-state*)
         (source *lpvct-line*)
         (current *lpvct-field*)
         (columns *lpvct-columns*)
         (name *lpvct-name*)
         (value '(120))
         (line (append name (cons 58 (append value '(13 10))))))
    (and (fn-lpv-header-equiv s source current columns 0 :pin)
         (fn-article-field-closedp current)
         (fn-article-namep name)
         (fn-article-header-bytes-p value)
         (not (or (not (consp value)) (fn-article-wspp (car value))))
         (<= (+ (len name) 1 (len value)) *fn-article-max-line-octets*)
         (not (fn-lpv-header-equiv
 (fn-nlv-run line s (len source) 0 :pin) (append source line)
 (fn-article-make-field (list (append name (cons 58 value))) (fn-article-ascii-downcase name) value)
 (fn-novlp-add-field columns current *fn-novlp-names*) 0 :pin))))
  :rule-classes nil)

; Literal full antecedent/conclusion; removals negate only their named premise.
(defthm lpvct-new-field-without-line-bound
  (let* ((s *lpvct-state*)
         (source *lpvct-line*)
         (current *lpvct-field*)
         (columns *lpvct-columns*)
         (name '(88))
         (value (cons 32 (lpvct-repeat 996)))
         (line (append name (cons 58 (append value '(13 10))))))
    (and (fn-lpv-header-equiv s source current columns 0 :pin)
         (fn-article-field-closedp current)
         (fn-article-namep name)
         (fn-article-header-bytes-p value)
         (or (not (consp value)) (fn-article-wspp (car value)))
         (not (<= (+ (len name) 1 (len value)) *fn-article-max-line-octets*))
         (not (fn-lpv-header-equiv
 (fn-nlv-run line s (len source) 0 :pin) (append source line)
 (fn-article-make-field (list (append name (cons 58 value))) (fn-article-ascii-downcase name) value)
 (fn-novlp-add-field columns current *fn-novlp-names*) 0 :pin))))
  :rule-classes nil)

(defthm lpvct-fold-positive
  (let* ((s *lpvct-state*)
         (source *lpvct-line*)
         (current *lpvct-field*)
         (columns *lpvct-columns*)
         (line '(32 122 9)))
    (and (fn-lpv-header-equiv s source current columns 0 :pin)
         current
         (fn-article-fold-linep line)
         (<= (len line) *fn-article-max-line-octets*)
         (fn-lpv-header-equiv (fn-nlv-run (append line '(13 10)) s (len source) 0 :pin)
 (append source (append line '(13 10))) (fn-article-add-fold current line) columns 0 :pin)))
  :rule-classes nil)

(defthm lpvct-fold-without-invariant
  (let* ((s (fn-lpc-put 4 999 *lpvct-state*))
         (source *lpvct-line*)
         (current *lpvct-field*)
         (columns *lpvct-columns*)
         (line '(32 122 9)))
    (and (not (fn-lpv-header-equiv s source current columns 0 :pin))
         current
         (fn-article-fold-linep line)
         (<= (len line) *fn-article-max-line-octets*)
         (not (fn-lpv-header-equiv (fn-nlv-run (append line '(13 10)) s (len source) 0 :pin)
 (append source (append line '(13 10))) (fn-article-add-fold current line) columns 0 :pin))))
  :rule-classes nil)

(defthm lpvct-fold-without-current
  (let* ((s (fn-lpc-header-begin))
         (source nil)
         (current nil)
         (columns *lpvct-columns*)
         (line '(32 122 9)))
    (and (fn-lpv-header-equiv s source current columns 0 :pin)
         (not current)
         (fn-article-fold-linep line)
         (<= (len line) *fn-article-max-line-octets*)
         (not (fn-lpv-header-equiv (fn-nlv-run (append line '(13 10)) s (len source) 0 :pin)
 (append source (append line '(13 10))) (fn-article-add-fold current line) columns 0 :pin))))
  :rule-classes nil)

(defthm lpvct-fold-without-fold-grammar
  (let* ((s *lpvct-state*)
         (source *lpvct-line*)
         (current *lpvct-field*)
         (columns *lpvct-columns*)
         (line '(32 9)))
    (and (fn-lpv-header-equiv s source current columns 0 :pin)
         current
         (not (fn-article-fold-linep line))
         (<= (len line) *fn-article-max-line-octets*)
         (not (fn-lpv-header-equiv (fn-nlv-run (append line '(13 10)) s (len source) 0 :pin)
 (append source (append line '(13 10))) (fn-article-add-fold current line) columns 0 :pin))))
  :rule-classes nil)

(defthm lpvct-fold-without-line-bound
  (let* ((s *lpvct-state*)
         (source *lpvct-line*)
         (current *lpvct-field*)
         (columns *lpvct-columns*)
         (line (cons 32 (lpvct-repeat 998))))
    (and (fn-lpv-header-equiv s source current columns 0 :pin)
         current
         (fn-article-fold-linep line)
         (not (<= (len line) *fn-article-max-line-octets*))
         (not (fn-lpv-header-equiv (fn-nlv-run (append line '(13 10)) s (len source) 0 :pin)
 (append source (append line '(13 10))) (fn-article-add-fold current line) columns 0 :pin))))
  :rule-classes nil)

(defthm lpvct-separator-body-positive
  (let* ((s *lpvct-state*) (source *lpvct-line*) (current *lpvct-field*)
         (columns *lpvct-columns*) (body '(120 13 10 121)))
    (and (fn-lpv-header-equiv s source current columns 0 :pin)
         (fn-article-field-closedp current)
         (fn-lpv-columns-equiv
          (fn-lpc-at 8 (fn-nlv-run (cons 13 (cons 10 body)) s (len source) 0 :pin))
          (fn-novlp-add-field columns current *fn-novlp-names*)
          (append source (cons 13 (cons 10 body))))))
  :rule-classes nil)

; Corrupted-state removal: the source and selected field disagree.
(defthm lpvct-separator-without-invariant
  (let* ((s (fn-lpc-put 4 999 *lpvct-state*)) (source *lpvct-line*)
         (current *lpvct-field*) (columns *lpvct-columns*) (body '(120 13 10)))
    (and (not (fn-lpv-header-equiv s source current columns 0 :pin))
         (fn-article-field-closedp current)
         (not (fn-lpv-columns-equiv
          (fn-lpc-at 8 (fn-nlv-run (cons 13 (cons 10 body)) s (len source) 0 :pin))
          (fn-novlp-add-field columns current *fn-novlp-names*)
          (append source (cons 13 (cons 10 body)))))))
  :rule-classes nil)

(defthm lpvct-separator-without-closed-current
  (let* ((s *lpvct-open-state*) (source *lpvct-open-line*)
         (current *lpvct-open-field*) (columns *lpvct-columns*) (body '(120 13 10)))
    (and (fn-lpv-header-equiv s source current columns 0 :pin)
         (not (fn-article-field-closedp current))
         (not (fn-lpv-columns-equiv
          (fn-lpc-at 8 (fn-nlv-run (cons 13 (cons 10 body)) s (len source) 0 :pin))
          (fn-novlp-add-field columns current *fn-novlp-names*)
          (append source (cons 13 (cons 10 body)))))))
  :rule-classes nil)

(defthm lpvct-successful-header-positive
  (let* ((s *lpvct-state*) (source *lpvct-line*) (current *lpvct-field*)
         (columns *lpvct-columns*) (octets '(32 121 13 10 13 10 98 13 10))
         (limits *fn-article-ceiling-limits*) (lines-left 10) (header-bytes (len source)) (nfields 0))
    (and (fn-lpv-header-equiv s source current columns 0 :pin)
         (fn-article-result-okp (fn-novlp-parse-lines octets limits lines-left header-bytes nfields columns current *fn-novlp-names*))
         (equal (fn-lpv-span-values (fn-lpc-at 8 (fn-nlv-run octets s (len source) 0 :pin)) (append source octets))
                (cadr (fn-novlp-parse-lines octets limits lines-left header-bytes nfields columns current *fn-novlp-names*)))))
  :rule-classes nil)

(defthm lpvct-successful-header-without-invariant
  (let* ((s (fn-lpc-put 4 999 *lpvct-state*)) (source *lpvct-line*) (current *lpvct-field*)
         (columns *lpvct-columns*) (octets '(13 10 98 13 10))
         (limits *fn-article-ceiling-limits*) (lines-left 10) (header-bytes (len source)) (nfields 0))
    (and (not (fn-lpv-header-equiv s source current columns 0 :pin))
         (fn-article-result-okp (fn-novlp-parse-lines octets limits lines-left header-bytes nfields columns current *fn-novlp-names*))
         (not (equal (fn-lpv-span-values (fn-lpc-at 8 (fn-nlv-run octets s (len source) 0 :pin)) (append source octets))
                     (cadr (fn-novlp-parse-lines octets limits lines-left header-bytes nfields columns current *fn-novlp-names*))))))
  :rule-classes nil)

(defthm lpvct-successful-header-without-success
  (let* ((s *lpvct-state*) (source *lpvct-line*) (current *lpvct-field*)
         (columns *lpvct-columns*) (octets '(32 9 13 10 13 10))
         (limits *fn-article-ceiling-limits*) (lines-left 10) (header-bytes (len source)) (nfields 0))
    (and (fn-lpv-header-equiv s source current columns 0 :pin)
         (not (fn-article-result-okp (fn-novlp-parse-lines octets limits lines-left header-bytes nfields columns current *fn-novlp-names*)))
         (not (equal (fn-lpv-span-values (fn-lpc-at 8 (fn-nlv-run octets s (len source) 0 :pin)) (append source octets))
                     (cadr (fn-novlp-parse-lines octets limits lines-left header-bytes nfields columns current *fn-novlp-names*))))))
  :rule-classes nil)

; Actual first hit is retained through an empty initial value, folding,
; mixed-case repeated name, and distinct TAB versus the single dropped SP.
(defconst *lpvct-complete*
  '(83 117 98 106 101 99 116 58 13 10 32 120 9 121 13 10
    115 85 66 106 101 99 116 58 32 122 13 10
    70 114 111 109 58 9 97 13 10
    68 97 116 101 58 32 100 13 10
    77 101 115 115 97 103 101 45 73 68 58 32 60 109 62 13 10
    82 101 102 101 114 101 110 99 101 115 58 32 60 114 62 13 10 13 10 98 13 10))
(defthm lpvct-complete-actual-overview-positive
  (let* ((bytes *lpvct-complete*)
         (view (fn-article-result-article (fn-article-parse bytes)))
         (values (fn-lpv-span-values (fn-lpc-at 8 (fn-nlv-run bytes (fn-lpc-header-begin) 0 0 :pin)) bytes)))
    (and (fn-article-result-okp (fn-article-parse bytes))
         (equal values (list (fn-nov-header-content view *fn-nov-subject-name*)
                             (fn-nov-header-content view *fn-nov-from-name*)
                             (fn-nov-header-content view *fn-nov-date-name*)
                             (fn-nov-header-content view *fn-nov-message-id-name*)
                             (fn-nov-header-content view *fn-nov-references-name*)))
         (equal values '((120 32 121) (32 97) (100) (60 109 62) (60 114 62)))))
  :rule-classes nil)

(defthm lpvct-complete-without-parser-success
  (let* ((bytes (append *lpvct-line* '(88 58 32 121 13 10 66 97 100 13 10 13 10)))
         (view (fn-article-result-article (fn-article-parse bytes)))
         (values (fn-lpv-span-values (fn-lpc-at 8 (fn-nlv-run bytes (fn-lpc-header-begin) 0 0 :pin)) bytes)))
    (and (not (fn-article-result-okp (fn-article-parse bytes)))
         (not (equal values (list (fn-nov-header-content view *fn-nov-subject-name*)
                                  (fn-nov-header-content view *fn-nov-from-name*)
                                  (fn-nov-header-content view *fn-nov-date-name*)
                                  (fn-nov-header-content view *fn-nov-message-id-name*)
                                  (fn-nov-header-content view *fn-nov-references-name*))))))
  :rule-classes nil)
