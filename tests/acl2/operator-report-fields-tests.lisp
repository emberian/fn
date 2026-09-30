(in-package "ACL2")
(include-book "../../books/operator-report-fields")

; Reachable positive complete antecedent/conclusion: mixed fields, empty
; borrowed strings, zero, a value above 64 bits, and the high octet.
(defconst *fn-orf-test-fields*
  (list (list :text "n=") (list :nat 0) (list :text "")
        (list :text ",") (list :nat 18446744073709551616)
        (list :text (coerce (list (code-char 255)) 'string))))

(assert-event
 (let ((c (fn-orf-start *fn-orf-test-fields*)))
   (and (fn-orf-fieldsp *fn-orf-test-fields*) (fn-orf-invariant c)
        (equal (fn-orf-run c) (fn-orf-reference *fn-orf-test-fields*))
        (equal (fn-orf-run c)
               (append '(110 61 48 44)
                       '(49 56 52 52 54 55 52 52 48 55 51 55 48 57 53 53 49 54 49 54)
                       '(255))))))

(assert-event
 (let ((c (fn-orf-start nil)))
   (and (fn-orf-invariant c) (fn-orf-terminalp c)
        (mv-let (next output done) (fn-orf-step c)
          (and (equal next c) (equal output nil) (equal done t)))
        (equal (fn-orf-run c) nil))))

; No arbitrary decimal-width cap: an admitted natural with 101 digits.
(assert-event
 (let* ((fields (list (list :nat (expt 10 100))))
        (c (fn-orf-start fields)))
   (and (fn-orf-fieldsp fields) (fn-orf-invariant c)
        (equal (fn-orf-run c) (cons 49 (make-list 100 :initial-element 48)))
        (equal (fn-orf-run c) (fn-orf-reference fields)))))

; Hypothesis-removal witness for conservation. The entire single invariant
; hypothesis fails affirmatively, and the literal conclusion fails.
(defthm fn-orf-conservation-hypothesis-removal-witness
 (let ((c (fn-orf-cursor :prepare '((:nat 0)) "" 0 -1 nil)))
   (and (not (fn-orf-invariant c))
        (not (equal (append (mv-nth 1 (fn-orf-step c))
                            (fn-orf-denotation (mv-nth 0 (fn-orf-step c))))
                    (fn-orf-denotation c)))))
 :rule-classes nil)
