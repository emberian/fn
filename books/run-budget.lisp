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

; One rule interface for children, core faces and constrained dispatch hooks.
; CAR is the canonical projection of result zero in the emitted bodies.
(defun fn2-run-quantity-terms (call residual work-limit descriptor-limit)
  (declare (xargs :verify-guards nil))
  `((natp (car ,call)) (natp (mv-nth 1 ,call)) (natp (mv-nth 2 ,call))
    (<= (+ (car ,call) (mv-nth 1 ,call)) ,work-limit)
    (<= (mv-nth 2 ,call) (nfix ,residual))
    (<= (mv-nth 2 ,call) ,descriptor-limit)))

(defun fn2-run-quantity-rewrites (hyps terms)
  (declare (xargs :verify-guards nil))
  (if (atom terms) nil
    (cons `(:rewrite :corollary (implies (and ,@hyps) ,(car terms)))
          (fn2-run-quantity-rewrites hyps (cdr terms)))))

(defun fn2-run-quantity-rules (hyps terms)
  (declare (xargs :verify-guards nil))
  (append (fn2-run-quantity-rewrites hyps terms)
    (list `(:type-prescription :corollary (implies (and ,@hyps) ,(nth 0 terms)))
          `(:type-prescription :corollary (implies (and ,@hyps) ,(nth 1 terms)))
          `(:type-prescription :corollary (implies (and ,@hyps) ,(nth 2 terms)))
          `(:linear :corollary (implies (and ,@hyps) ,(nth 3 terms)))
          `(:linear :corollary (implies (and ,@hyps) ,(nth 4 terms)))
          `(:linear :corollary (implies (and ,@hyps) ,(nth 5 terms))))))

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
