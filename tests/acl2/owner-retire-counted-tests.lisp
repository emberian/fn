(in-package "ACL2")
(include-book "../../books/owner-retire-counted")

; Reachable input observation: before window, zero with both producer fences.
(assert-event
 (and (< (fn-osd-elapsed nil nil) 10000)
      (equal (fn-ort-drain-step-counted nil nil 10 0 t t) :drained)
      (equal 0 0) (equal t t)))
; Each omitted observation affirmatively fails while the other holds and
; pending remains zero; the unfenced success conclusion fails.
(assert-event
 (and (< (fn-osd-elapsed nil nil) 10000)
      (equal (fn-ort-drain-step-counted nil nil 10 0 nil t) :wait)
      (equal (fn-ort-drain-step-counted nil nil 10 0 t nil) :wait)
      (equal (fn-ort-drain-step-counted nil nil 10 1 t t) :wait)))
; Deadline antecedent/conclusion hold independently of pending and fences.
(assert-event
 (and (<= 0 (fn-osd-elapsed nil nil))
      (not (equal (fn-ort-drain-step-counted nil nil 0 99 nil nil) :wait))
      (equal (fn-ort-drain-step-counted nil nil 0 99 nil nil) :deadline)))
; Corrupted-state case is distinct: a negative count is never drained.
(assert-event
 (and (not (natp -1))
      (equal (fn-ort-drain-step-counted nil nil 10 -1 t t) :wait)))
; Actual clock-only precheck: no producer/count argument is available here.
(assert-event
 (and (< (fn-osd-elapsed nil nil) 10000)
      (equal (fn-ort-window-step nil nil 10) :wait)
      (not (equal (fn-ort-window-step nil nil 10) :drained))))
(assert-event
 (and (<= 0 (fn-osd-elapsed nil nil))
      (equal (fn-ort-window-step nil nil 0) :deadline)
      (not (equal (fn-ort-drain-step-counted nil nil 0 99 nil nil) :wait))))
