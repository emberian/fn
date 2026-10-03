(in-package "ACL2")
(include-book "../../books/string-line-fill")

; Literal positive witnesses for both unconditional exact-residual keystones
; and both byte bounds. No hypothesis-removal witness applies: there are no
; hypotheses. Execute through an actual local abstract stobj, not a twin.
(defun slf-witness (text position phase bytes directp fn-octets)
  (declare (xargs :guard (natp bytes) :verify-guards nil :stobjs fn-octets))
  (let* ((cur (fn-sl-make text position phase))
         (fn-octets (fn-octets-from-list '(90) fn-octets)))
    (mv-let (next fn-octets)
      (if directp (fn-slf-loop text position phase bytes fn-octets)
        (fn-sl-fill cur bytes fn-octets))
      (let ((out (fn-octets-list fn-octets)))
        (mv (and (equal (append out (fn-sl-remaining next))
                        (append '(90) (fn-sl-remaining cur)))
                 (<= (len out) (+ 1 (nfix bytes))))
            fn-octets)))))

(defun slf-witness-value (text position phase bytes directp)
  (declare (xargs :guard (natp bytes) :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (ok fn-octets)
      (slf-witness text position phase bytes directp fn-octets) ok)))

(assert-event (and (slf-witness-value ".abc" 0 :stuff 3 t)
                   (slf-witness-value ".abc" 0 :stuff 3 nil)))
(assert-event (and (slf-witness-value "abc" 0 :text 2 t)
                   (slf-witness-value "abc" 0 :text 2 nil)))
(assert-event (and (slf-witness-value "abc" 3 :cr 1 t)
                   (slf-witness-value "abc" 3 :cr 1 nil)))
(assert-event (and (slf-witness-value "abc" 3 :lf 9 t)
                   (slf-witness-value "abc" 3 :lf 9 nil)))
(assert-event (and (slf-witness-value "" 0 :cr 0 t)
                   (slf-witness-value "" 0 :cr 0 nil)))
; Corrupted-state witnesses: total functions preserve their literal residual,
; without promoting invalid cursor fields to a supported native plan.
(assert-event (and (slf-witness-value 77 'bad :text 9 t)
                   (slf-witness-value 77 'bad :text 9 nil)
                   (slf-witness-value "abc" 99 :unknown 9 t)
                   (slf-witness-value "abc" 99 :unknown 9 nil)))
(assert-event (and (eq (symbol-class 'fn-slf-loop (w state)) :common-lisp-compliant)
                   (eq (symbol-class 'fn-sl-fill (w state)) :common-lisp-compliant)))
