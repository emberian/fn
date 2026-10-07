(in-package "ACL2")
(include-book "../../books/string-line-fill")
(include-book "../../books/defkeystone")

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

; fn-sl-step-residual (TEETH CONTRACT v1).  fn-sl-step returns several values, so the witnesses are ground theorems (:witness-lemma / :lemma; TEETH-OWED-MV-CLAIM lemma debt).  No hypotheses.
(defthm slf-gl-step-residual-witness
  (equal (append (car (fn-sl-step (fn-sl-make "abc" 0 :text) 2))
                 (fn-sl-remaining (mv-nth 1 (fn-sl-step (fn-sl-make "abc" 0 :text) 2))))
         (fn-sl-remaining (fn-sl-make "abc" 0 :text))))
(defthm slf-gl-step-residual-mutant
  (and (equal (append (car (fn-sl-step (fn-sl-make "abc" 0 :text) 2))
                      (fn-sl-remaining (mv-nth 1 (fn-sl-step (fn-sl-make "abc" 0 :text) 2))))
              (fn-sl-remaining (fn-sl-make "abc" 0 :text)))
       (not (equal (append (car (fn-sl-step (fn-sl-make "abc" 0 :text) 2))
                           (fn-sl-remaining (fn-sl-make "abc" 0 :text)))
                   (fn-sl-remaining (fn-sl-make "abc" 0 :text))))))
(defteeth fn-sl-step-residual
  :claim (() (equal (append (car (fn-sl-step cur bytes))
                            (fn-sl-remaining (mv-nth 1 (fn-sl-step cur bytes))))
                    (fn-sl-remaining cur)))
  :subject fn-sl-step
  :witness-lemma slf-gl-step-residual-witness
  :witness ((cur (fn-sl-make "abc" 0 :text)) (bytes 2))
  :mutations ((emitted-bytes-lost
               (:conclusion (equal (append (car (fn-sl-step cur bytes)) (fn-sl-remaining cur))
                                   (fn-sl-remaining cur)))
               ((cur (fn-sl-make "abc" 0 :text)) (bytes 2))
               :fault "a step whose cursor never advances past the octets it emitted"
               :lemma slf-gl-step-residual-mutant)))
