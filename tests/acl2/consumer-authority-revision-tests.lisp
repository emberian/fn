(in-package "ACL2")
(include-book "../../books/consumer-authority-revision")

(defconst *cart-rows* '((:account (97) 1 t (7 8))))
(defconst *cart-pending*
  (list :adoption '(10) 9 1 3 '((:account (98) 2 t (11)))
        '(98) (make-list 32 :initial-element 0) t))
(defconst *cart-state*
  (fn-cp-state-carry '(1) '(2) 11 2 '((:entry (3) (4) (5) 1 9 1 0))
                    (list :authority 9 2 '(9) *cart-rows* *cart-pending*)))

(assert-event (fn-cp-statep *cart-state*))

; Current admitted authority changes one revision, preserves the exact
; account/creation roots and consumer progress, and discards pending rows.
(assert-event
 (let ((next (fn-cp-nth 1 (fn-carv-semantic-step *cart-state*))))
   (and (fn-cp-statep *cart-state*)
        (fn-cp-nth 3 (fn-cp-nth 6 *cart-state*))
        (fn-cp-uintp (fn-cp-nth 1 (fn-cp-nth 6 *cart-state*)))
        (< (fn-cp-nth 1 (fn-cp-nth 6 *cart-state*)) *fn-cbor-max-uint*)
        (eq (car (fn-carv-semantic-step *cart-state*)) :ok)
        (fn-cp-statep next)
        (equal (fn-cp-nth 6 next) (list :authority 10 2 '(9) *cart-rows* nil))
        (equal (fn-cp-nth 5 next) (fn-cp-nth 5 *cart-state*))
        (equal (fn-cp-nth 3 next) 11))))

; Exhaustion refuses; no wrap or partially changed authority is returned.
(assert-event
 (let ((s (fn-carv-revision-state *cart-state* *fn-cbor-max-uint*)))
   (and (fn-cp-statep s)
        (equal (fn-carv-semantic-step s)
               '(:refused :authority-revision-exhausted)))))

; Before namespace birth a config change does not count historical events,
; but it invalidates provisional adoption against the previous roots.
(assert-event
 (let* ((a (list :authority 9 1 nil nil *cart-pending*))
        (s (fn-cp-state-carry '(1) '(2) 11 1 nil a))
        (next (fn-cp-nth 1 (fn-carv-semantic-step s))))
   (and (fn-cp-statep s) (fn-cp-statep next)
        (equal (fn-cp-nth 6 next) '(:authority 9 1 nil nil nil))
        (equal (fn-carv-semantic-step nil) '(:ok nil)))))

; Hypothesis removal: without active authority, both scalar hypotheses
; remain true but the comparison revision does not advance.
(assert-event
 (let* ((s (fn-cp-state-carry '(1) '(2) 11 1 nil
                             '(:authority 9 1 nil nil nil)))
        (a (fn-cp-nth 6 s))
        (next (fn-cp-nth 1 (fn-carv-semantic-step s))))
   (and (fn-cp-statep s) (not (fn-cp-nth 3 a))
        (fn-cp-uintp (fn-cp-nth 1 a))
        (< (fn-cp-nth 1 a) *fn-cbor-max-uint*)
        (not (equal (fn-cp-nth 1 (fn-cp-nth 6 next))
                    (1+ (fn-cp-nth 1 a)))))))

; Hypothesis removal: active and typed but exhausted; no wrap is emitted.
(assert-event
 (let* ((s (fn-carv-revision-state *cart-state* *fn-cbor-max-uint*))
        (a (fn-cp-nth 6 s))
        (next (fn-cp-nth 1 (fn-carv-semantic-step s))))
   (and (fn-cp-statep s) (fn-cp-nth 3 a)
        (fn-cp-uintp (fn-cp-nth 1 a))
        (not (< (fn-cp-nth 1 a) *fn-cbor-max-uint*))
        (not (eq (car (fn-carv-semantic-step s)) :ok))
        (not (equal (fn-cp-nth 1 (fn-cp-nth 6 next))
                    (1+ (fn-cp-nth 1 a)))))))

; Hypothesis removal for preservation: unbootstrapped NIL is an allowed
; outer projection state but is not a typed CP7. Success alone cannot
; imply the CP7 state invariant.
(assert-event
 (and (not (fn-cp-statep nil))
      (eq (car (fn-carv-semantic-step nil)) :ok)
      (not (fn-cp-statep (fn-cp-nth 1 (fn-carv-semantic-step nil))))))

; Corrupted-state / hypothesis removal: active and below exhaustion, but
; the revision is not an admitted integer. It cannot produce success.
(assert-event
 (let* ((s (fn-carv-revision-state *cart-state* 1/2))
        (a (fn-cp-nth 6 s)))
   (and (not (fn-cp-statep s)) (fn-cp-nth 3 a)
        (not (fn-cp-uintp (fn-cp-nth 1 a)))
        (< (fn-cp-nth 1 a) *fn-cbor-max-uint*)
        (not (eq (car (fn-carv-semantic-step s)) :ok)))))
