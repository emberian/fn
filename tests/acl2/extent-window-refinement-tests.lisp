(in-package "ACL2")
(include-book "../../books/extent-window-refinement")
(include-book "extent-window-capture-tests")

; Literal positive, both retained and newly captured bytes, after a real
; concrete two-block execution. The immutable message exists only in tests.
(assert-event
 (let* ((s *ewpt-last*)
        (msg (append (make-list 60 :initial-element 200) '(0 1 2 3 4 5 6 7 8 9)))
        (input '(4 5 6 7 8 9)) (j 8)
        (before '(0 1 2 3 0 0 0 0 0 0))
        (after (ewct-capture)))
   (and (natp j) (natp (nth 4 s)) (natp (nth 5 s)) (natp (nth 7 s))
        (equal (nth 0 s) :scan) (< j (nth 5 s))
        (< (+ (nth 4 s) j) (+ (nth 7 s) (fn-ewp-demand s)))
        (equal input (fn-shr-win (nth 7 s) (fn-ewp-demand s) msg))
        (implies (< (+ (nth 4 s) j) (nth 7 s))
                 (equal (nth j before) (nth (+ (nth 4 s) j) msg)))
        (equal (nth j after) (nth (+ (nth 4 s) j) msg))
        (equal (nth 2 after) (nth 62 msg)))))

; Hypothesis-removal of faithful bounded source. The actual output is still
; from the real concrete reader fixture; the promised message is changed.
(assert-event
 (let* ((s *ewpt-last*)
        (msg (append (make-list 60 :initial-element 200) '(0 1 2 3 4 5 6 7 99 9)))
        (input '(4 5 6 7 8 9)) (j 8)
        (before '(0 1 2 3 0 0 0 0 0 0))
        (after (ewct-capture)))
   (and (natp j) (natp (nth 4 s)) (natp (nth 5 s)) (natp (nth 7 s))
        (equal (nth 0 s) :scan) (< j (nth 5 s))
        (< (+ (nth 4 s) j) (+ (nth 7 s) (fn-ewp-demand s)))
        (not (equal input (fn-shr-win (nth 7 s) (fn-ewp-demand s) msg)))
        (implies (< (+ (nth 4 s) j) (nth 7 s))
                 (equal (nth j before) (nth (+ (nth 4 s) j) msg)))
        (not (equal (nth j after) (nth (+ (nth 4 s) j) msg))))))
