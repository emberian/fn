(in-package "ACL2")
(include-book "../../books/owner-retire-stream-space")

; Test-only traversal; the actual report cursor never evaluates this census.
(defun fn-orr-space-fixture (fuel cursor)
  (declare (xargs :guard (and (natp fuel) (fn-orr-invariant cursor))
                  :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable fn-orr-space-relationp)))
                  :guard-hints
                  (("Goal" :use fn-orr-step-preserves-invariant
                    :in-theory
                    (disable fn-orr-invariant fn-orr-step fn-orr-space-relationp
                             fn-orr-step-preserves-invariant)))))
  (if (zp fuel) (fn-orr-space-relationp cursor)
    (and (fn-orr-space-relationp cursor)
         (mv-let (next output done) (fn-orr-step cursor)
           (declare (ignore output done))
           (fn-orr-space-fixture (+ -1 fuel) next)))))

; Pure reachable report witness: actual nine-slot feed, unrelated BP pin,
; natural charge beyond any machine-word limit, and final release instruction.
(assert-event
 (let* ((feed (list nil nil '( ("a" (:dropped :retry-bound))
                              ("b" (:dropped :operator))) nil nil nil nil 2 1))
        (pin (list "forward-unrelated" "borrowed subject" :forward nil (expt 10 100)))
        (cursor (fn-orr-cursor :count-pins (list (list "peer" nil feed))
                               (list pin) (list pin) 0 0 456 :deadline nil nil)))
   (mv-let (next output done) (fn-orr-step cursor)
     (declare (ignore output done))
     (and (fn-feed-count-relationp feed) (fn-orr-pin-domainp pin)
          (fn-orr-space-relationp cursor) (fn-orr-space-relationp next)
          (fn-orr-space-fixture 1200 cursor)))))

(assert-event
 (and (fn-orr-space-relationp (fn-orr-start :drained nil))
      (fn-orr-space-fixture 256 (fn-orr-start :drained nil))))

; Corrupted-state complete removal tooth for actual report STEP. Its original
; ten-slot invariant still holds; omitted space relation and conclusion fail.
(assert-event
 (let* ((emitter (fn-orf-cursor :prepare '((:nat 0)) "" 0 0 '(48)))
        (cursor (fn-orr-cursor :emit nil nil nil 0 0 0 :drained emitter :done)))
   (mv-let (next output done) (fn-orr-step cursor)
     (declare (ignore output done))
     (and (fn-orr-invariant cursor) (fn-orf-invariant emitter)
          (not (fn-orr-space-relationp cursor))
          (not (fn-orr-space-relationp next))))))

; Corrupted-state guard separation: only the current descriptor is ready.
; A malformed later field makes the carried invariant false, so this is not
; installed-state evidence, but the fixed-prefix guard itself does not scan it.
(assert-event
 (let* ((emitter (fn-orf-cursor :field '((:text "") (:text 7)) "" 0 0 nil))
        (cursor (fn-orr-cursor :emit nil nil nil 0 0 0 :drained emitter :done)))
   (and (fn-orr-ready-p cursor) (not (fn-orr-invariant cursor))
        (mv-let (next output done) (fn-orr-step cursor)
          (declare (ignore output done))
          (fn-orr-ready-p next)))))
