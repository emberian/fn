(in-package "ACL2")
(include-book "../../books/def-cursor")
(include-book "must-fail-checked")

; A candidate contributes five octets, exceeding the two-octet output
; quantum. Saved scan progress is distinct from its three pending octets.
(defun fn-cur-test-one (progress)
  (declare (xargs :guard t))
  (mv '(65 66 67 68 69) (if (consp progress) (cdr progress) nil)))
(defthm fn-cur-test-visits
  (<= (- (len progress) (len (mv-nth 1 (fn-cur-test-one progress)))) 1))
(def-cursor fn-cur-test ()
  :call (fn-cur-test-one progress)
  :visit-proof fn-cur-test-visits :visit-metric (len progress))

(verify-guards fn-cur-test-step)

(assert-event
 (let* ((cur (fn-cur-make '(:view root-a :config cfg-a) '(a b) nil nil))
        (step (mv-list 4 (fn-cur-test-step cur 1 2)))
        (next (nth 1 step))
        (drain (mv-list 4 (fn-cur-test-step next 0 2))))
   (and (equal (nth 0 step) '(65 66))
        (equal (fn-cur-progress next) '(b))
        (equal (fn-cur-pending next) '(67 68 69))
        (equal (fn-cur-context next) (fn-cur-context cur))
        (equal (nth 2 step) 1)
        (equal (nth 0 drain) '(67 68))
        (equal (fn-cur-progress (nth 1 drain)) '(b))
        (equal (fn-cur-pending (nth 1 drain)) '(69))
        (equal (nth 2 drain) 0))))

; Zero budgets preserve obligations. A pending physical operation carries
; its nested resource token unchanged: neither drain nor timeout settles it.
(assert-event
 (let* ((token '(:resource (7 . 13) 5 19))
        (dependency (list :operation '(2 . 11) token))
        (cur (fn-cur-make '(:view root-a) '(a b) '(65 66) dependency)))
   (and (equal (nth 1 (mv-list 4 (fn-cur-test-step cur 1 2))) cur)
        (equal (nth 3 (mv-list 4 (fn-cur-test-step cur 1 2))) :suspended)
        (equal (nth 0 (mv-list 4 (fn-cur-test-step cur 1 2))) nil)
        (equal (nth 2 (mv-list 4 (fn-cur-test-step cur 1 2))) 0))))
(assert-event
 (let ((cur (fn-cur-make '(:view root-a) '(a b) nil nil)))
   (and (equal (nth 1 (mv-list 4 (fn-cur-test-step cur 0 2))) cur)
        (equal (nth 1 (mv-list 4 (fn-cur-test-step cur 1 0))) cur))))

; Missing named candidate obligation is refused before emitting definitions.
(must-fail
 (def-cursor fn-cur-absent ()
   :call (fn-cur-test-one progress)
   :visit-proof fn-cur-nonexistent-proof :visit-metric (len progress)))

; An admitted theorem of another statement cannot license a declaration.
(defthm fn-cur-unrelated t :rule-classes nil)
(must-fail
 (def-cursor fn-cur-wrong-proof ()
   :call (fn-cur-test-one progress)
   :visit-proof fn-cur-unrelated :visit-metric (len progress)))
