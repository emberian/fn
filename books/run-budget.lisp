; Shared quantitative contract for a returned machine transition. Stopped and
; refusal outcomes have the same obligations as successful outcomes.
(in-package "ACL2")

(defun fn2-run-quantitiesp (bytes steps descriptors residual work-limit)
  (declare (xargs :guard t))
  (and (natp bytes) (natp steps) (natp descriptors)
       (<= (+ bytes steps) (nfix work-limit))
       (<= descriptors (nfix residual))))

; An arm only appends to the outbox. This relation ties its accounting to the
; actual effect, rather than trusting a self-reported descriptor count.
(defun fn2-run-effects-p (descriptors queued-before queued-after)
  (declare (xargs :guard t))
  (and (natp descriptors) (natp queued-before) (natp queued-after)
       (equal queued-after (+ queued-before descriptors))))

(defthm fn2-run-quantitiesp-residual
  (implies (fn2-run-quantitiesp bytes steps descriptors residual work-limit)
           (<= descriptors (nfix residual)))
  :rule-classes (:rewrite :linear))

(defthm fn2-run-quantitiesp-work
  (implies (fn2-run-quantitiesp bytes steps descriptors residual work-limit)
           (<= (+ bytes steps) (nfix work-limit)))
  :rule-classes (:rewrite :linear))

(defthm fn2-run-effects-within-residual
  (implies (and (fn2-run-quantitiesp bytes steps descriptors residual work-limit)
                (fn2-run-effects-p descriptors queued-before queued-after))
           (<= queued-after (+ queued-before (nfix residual))))
  :rule-classes (:rewrite :linear))
