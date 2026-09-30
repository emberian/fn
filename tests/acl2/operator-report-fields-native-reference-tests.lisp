(in-package "ACL2")
(include-book "operator-report-fields-tests")
(include-book "../../books/operator-report-fields-native-reference")

(assert-event
 (and (fn-orf-fieldsp *fn-orf-test-fields*)
      (equal (fn-orf-run (fn-orf-start *fn-orf-test-fields*))
             (fn-orf-nls-reference *fn-orf-test-fields*))))

(assert-event
 (and (natp 0) (natp (expt 10 100))
      (equal (fn-orf-decimal 0 nil) (fn-nls-nat 0))
      (equal (fn-orf-decimal (expt 10 100) nil)
             (fn-nls-nat (expt 10 100)))))

(assert-event
 (let ((text (coerce (list (code-char 0) (code-char 255)) 'string)))
   (and (stringp text)
        (equal (fn-orf-text-tail text 0) (fn-nls-text text))
        (equal (fn-orf-text-tail text 0) '(0 255)))))

; Removing the descriptor-domain hypothesis invalidates the complete join.
; Logical witness, since this intentionally violates executable guards.
(defthm fn-orf-nls-completion-hypothesis-removal-witness
  (let ((fields '((:nat -1))))
    (and (not (fn-orf-fieldsp fields))
         (not (equal (fn-orf-run (fn-orf-start fields))
                     (fn-orf-nls-reference fields)))))
  :rule-classes nil)
