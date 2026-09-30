(in-package "ACL2")
(include-book "../../books/owner-retire-counted")

; Reachable publication and repeated/stale observer result: lifecycle record
; is fixed metadata, not a whole-state comparison or owner mutex wait.
(assert-event
 (and (equal (fn-ort-retire-observer-action '(0 10)) :observe)
      (equal (fn-ort-retire-publish '(0 10) :deadline)
             '((0 10 :deadline) t))
      (equal (fn-ort-retire-observer-action '(0 10 :deadline)) :done)
      (equal (fn-ort-retire-publish '(0 10 :deadline) :wait)
             '((0 10 :deadline) t))
      (equal (fn-ort-retire-publish
              (car (fn-ort-retire-publish '(0 10) :deadline)) :deadline)
             (fn-ort-retire-publish '(0 10) :deadline))))
; Remove completed-record hypothesis, preserve valid metadata/event: the
; original-record conclusion affirmatively fails after first publication.
(assert-event
 (and (not (equal (fn-ort-retire-observer-action '(0 10)) :done))
      (equal (fn-ort-retire-observer-action '(0 10)) :observe)
      (not (equal (car (fn-ort-retire-publish '(0 10) :deadline)) '(0 10)))))

; Current producer observation is explicitly unsettled, so the actual
; clock-only entry has the complete counted decision for any pending scalar.
(assert-event
 (and (equal (fn-ort-window-step nil nil 10)
             (fn-ort-drain-step-counted nil nil 10 137 t nil))
      (equal (fn-ort-window-step nil nil 0)
             (fn-ort-drain-step-counted nil nil 0 -9 nil nil))
      (equal (fn-ort-maintenance-action t) :skip)
      (equal (fn-ort-maintenance-action nil) :admit)))

(assert-event
 (and (equal (fn-ort-log-caller-action nil) :write-close)
      (not (equal t nil))
      (equal (fn-ort-log-caller-action t) :held)
      (not (equal (fn-ort-log-caller-action t) :write-close))))

(assert-event
 (and (equal (fn-ort-report-close-action :joined :closed) :joined)
      (equal (fn-ort-report-close-action :joined :absent) :joined)
      (not (equal :held :joined))
      (equal (fn-ort-report-close-action :held :closed) :held)
      (not (member-equal :uncertain '(:closed :absent)))
      (equal (fn-ort-report-close-action :joined :uncertain) :held)))

; Physical join observation and every zero-work observation are present.
(assert-event
 (and (equal (fn-ort-log-close-action :joined 0 0 nil) :joined)
      (equal (fn-ort-log-close-action :absent 0 0 nil) :joined)
      (equal (fn-ort-log-close-exit 0 75 :joined) 0)))
; Mutation witnesses remove one settlement observation at a time while
; preserving every other input, and affirmatively fail joined disposition.
(assert-event
 (and (not (member-equal :timeout '(:joined :absent)))
      (equal (fn-ort-log-close-action :timeout 0 0 nil) :held)
      (not (equal 1 0))
      (equal (fn-ort-log-close-action :joined 1 0 nil) :held)
      (equal (fn-ort-log-close-action :joined 0 1 nil) :held)
      (not (equal t nil))
      (equal (fn-ort-log-close-action :joined 0 0 t) :held)
      (equal (fn-ort-log-close-exit 0 75 :held) 75)))

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
