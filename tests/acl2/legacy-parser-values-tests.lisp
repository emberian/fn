(in-package "ACL2")
(include-book "../../books/legacy-parser-values")

(defun fn-lpvt-run (bytes s pos)
  (declare (xargs :guard (natp pos)))
  (if (consp bytes)
      (fn-lpvt-run (cdr bytes) (fn-lpc-header-byte s (car bytes) pos 0 :pin)
                   (+ 1 pos)) s))

(defconst *lpvt-prefix* '(83 117 98 106 101 99 116 58 32))
(defconst *lpvt-before*
  (fn-lpvt-run *lpvt-prefix* (fn-lpc-header-begin) 0))

; Literal positive: the state is reached through the actual header machine,
; and every antecedent and conclusion of the actual byte theorem is checked.
(defthm lpvt-actual-byte-positive
  (let* ((s *lpvt-before*) (source *lpvt-prefix*) (value '(32)) (byte 120)
         (out (fn-lpc-header-byte s byte (len source) 0 :pin)))
    (and (fn-lpv-value-state-p s source value)
         (equal (fn-lpc-at 0 s) :value)
         (< (nfix (fn-lpc-at 1 s)) *fn-article-max-line-octets*)
         (fn-article-header-bytep byte)
         (fn-lpv-value-state-p out (append source (list byte))
                               (append value (list byte)))))
  :rule-classes nil)

; CORRUPTED STATE / hypothesis removal: all remaining hypotheses hold.
(defthm lpvt-without-value-invariant
  (let* ((s (fn-lpc-put 4 1000 *lpvt-before*))
         (source *lpvt-prefix*) (value '(32)) (byte 120))
    (and (not (fn-lpv-value-state-p s source value))
         (equal (fn-lpc-at 0 s) :value)
         (< (nfix (fn-lpc-at 1 s)) *fn-article-max-line-octets*)
         (fn-article-header-bytep byte)
         (not (fn-lpv-value-state-p
               (fn-lpc-header-byte s byte (len source) 0 :pin)
               (append source (list byte)) (append value (list byte))))))
  :rule-classes nil)

(defthm lpvt-without-value-phase
  (let* ((s (fn-lpc-put 0 :name *lpvt-before*))
         (source *lpvt-prefix*) (value '(32)) (byte 120))
    (and (fn-lpv-value-state-p s source value)
         (not (equal (fn-lpc-at 0 s) :value))
         (< (nfix (fn-lpc-at 1 s)) *fn-article-max-line-octets*)
         (fn-article-header-bytep byte)
         (not (fn-lpv-value-state-p
               (fn-lpc-header-byte s byte (len source) 0 :pin)
               (append source (list byte)) (append value (list byte))))))
  :rule-classes nil)

(defthm lpvt-without-line-budget
  (let* ((s (fn-lpc-put 1 *fn-article-max-line-octets* *lpvt-before*))
         (source *lpvt-prefix*) (value '(32)) (byte 120))
    (and (fn-lpv-value-state-p s source value)
         (equal (fn-lpc-at 0 s) :value)
         (not (< (nfix (fn-lpc-at 1 s)) *fn-article-max-line-octets*))
         (fn-article-header-bytep byte)
         (not (fn-lpv-value-state-p
               (fn-lpc-header-byte s byte (len source) 0 :pin)
               (append source (list byte)) (append value (list byte))))))
  :rule-classes nil)

(defthm lpvt-without-header-byte
  (let* ((s *lpvt-before*) (source *lpvt-prefix*) (value '(32)) (byte 0))
    (and (fn-lpv-value-state-p s source value)
         (equal (fn-lpc-at 0 s) :value)
         (< (nfix (fn-lpc-at 1 s)) *fn-article-max-line-octets*)
         (not (fn-article-header-bytep byte))
         (not (fn-lpv-value-state-p
               (fn-lpc-header-byte s byte (len source) 0 :pin)
               (append source (list byte)) (append value (list byte))))))
  :rule-classes nil)

; Folded source spans retain physical CRLF while the reference unfolds it.
(defthm lpvt-fold-and-completed-span-positive
  (let* ((source (append *lpvt-prefix* '(120 13 10)))
         (value '(32 120))
         (s (fn-lpvt-run source (fn-lpc-header-begin) 0))
         (fold (fn-lpc-header-byte s 32 (len source) 0 :pin))
         (fold-source (append source '(32)))
         (fold-value (append value '(32)))
         (seen (fn-lpc-header-byte fold 121 (len fold-source) 0 :pin))
         (seen-source (append fold-source '(121)))
         (seen-value (append fold-value '(121)))
         (out (fn-lpc-header-byte
               (fn-lpc-header-byte seen 13 (len seen-source) 0 :pin)
               10 (+ 1 (len seen-source)) 0 :pin)))
    (and (fn-lpv-value-state-p s source value)
         (equal (fn-lpc-at 0 s) :start) (fn-lpc-at 2 s)
         (< (nfix (fn-lpc-at 1 s)) *fn-article-max-line-octets*)
         (fn-article-wspp 32)
         (fn-lpv-value-state-p fold fold-source fold-value)
         (fn-lpv-value-state-p seen seen-source seen-value)
         (consp seen-value) (member-eq (fn-lpc-at 0 seen) '(:first :value))
         (not (equal (fn-lpc-at 10 seen) :fold-empty))
         (equal (fn-nov-scrub
                 (fn-lpv-slice (append seen-source '(13 10))
                               (fn-lpc-at 4 out) (fn-lpc-at 5 out)))
                (fn-nov-scrub (fn-nov-value-content seen-value)))
         (equal (fn-nov-scrub (fn-nov-value-content seen-value)) '(120 32 121))))
  :rule-classes nil)

; MUTATIONS: flattening CR/LF into spaces or dropping TAB are observable.
(assert-event
 (and (equal (fn-nov-scrub '(120 13 10 32 121)) '(120 32 121))
      (not (equal '(120 32 32 32 121) '(120 32 121)))
      (equal (fn-nov-scrub (fn-nov-value-content '(9 120))) '(32 120))
      (not (equal '(120) '(32 120)))
      (equal (fn-nov-scrub (fn-nov-value-content '(32 32 120))) '(32 120))))

; A present empty first value must not turn into an absent column.
(defthm lpvt-empty-first-hit-positive-and-mutation
  (let* ((columns '((nil)))
         (field (fn-article-make-field nil *fn-nov-subject-name* '(32 120)))
         (names (list *fn-nov-subject-name*)))
    (and (car columns)
         (equal (fn-lpv-columns (fn-novlp-add-field columns field names))
                (fn-lpv-add-normal-field (fn-lpv-columns columns) field names))
         (equal (car (fn-lpv-columns (fn-novlp-add-field columns field names)))
                (fn-lpv-column (car columns)))
         (equal (fn-lpv-columns (fn-novlp-add-field columns field names)) '((nil)))
         (not (equal (fn-lpv-columns (fn-novlp-add-field '(nil) field names)) '((nil))))))
  :rule-classes nil)
