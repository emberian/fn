; Regression for the 750-step counterexample accepted in f8dd7ce87.
; The old cursor (0 2047 nil) on an empty store grew words 0 -> 2049.
; It must now refuse by name with the entire store unchanged.
(in-package "ACL2")
(include-book "../../books/history-image-place")
(include-book "must-fail-checked")

(defconst *m13-refusal-fresh* '(nil nil nil nil nil nil))
(defconst *m13-refusal-pw*
 '(0 (0 0 0 0 0) ((0 2047 nil) (0 0 nil) (0 0 nil) (0 0 nil) (0 0 nil))))

(defthm fn-his-place-teeth-malformed-cursor-refused
 (let ((res (fn-his-place-run 1 '((:other 1 nil)) 0 *m13-refusal-pw*
                              '(1 2 3 4 5) 6 *m13-refusal-fresh*)))
   (and (equal (mv-nth 0 res) '(:refused :placement))
        (equal (mv-nth 1 res) '((:other 1 nil)))
        (equal (mv-nth 2 res) *m13-refusal-pw*)
        (equal (mv-nth 3 res) *m13-refusal-fresh*)))
 :rule-classes nil)

; @mutation-witness: the previously accepted result is now impossible.
(must-fail-checked
 (defthm fn-his-place-teeth-malformed-cursor-still-succeeds
   (equal (mv-nth 0 (fn-his-place-run 1 '((:other 1 nil)) 0 *m13-refusal-pw*
                                      '(1 2 3 4 5) 6 *m13-refusal-fresh*)) :done))
 :step-limit 10000)

; A bad target in a later region refuses BEFORE writing an earlier region.
(defthm fn-his-place-teeth-late-region-refuses-atomically
 (let* ((rc (list 0 2047 (adt-zeros 2047)))
        (res (fn-his-rcs-put '((7) (8)) (list rc rc) '(0 2)
                              (list (adt-zeros 2048) nil nil '(0) nil nil))))
   (and (equal (mv-nth 0 res) '(:refused :placement))
        (equal (mv-nth 2 res) (list (adt-zeros 2048) nil nil '(0) nil nil))))
 :rule-classes nil)
