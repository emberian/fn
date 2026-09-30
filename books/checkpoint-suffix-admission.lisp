; PRF-1098. POST admission before identity allocation/prepare. K is the
; persisted operator's checkpoint suffix threshold, not a stored-data cap.
; This bounds the next accepted POST relative to the last durable checkpoint;
; it is not a bound on other publication kinds or a full rescue theorem.
(in-package "ACL2")

(defun fn-csa-post-admission (durable count k)
  (declare (xargs :guard t))
  (if (and (or (null durable) (natp durable)) (natp count) (posp k)
           (<= (nfix durable) count)
           (<= (+ 1 count) (+ (nfix durable) (* 2 k))))
      :ok
    :checkpoint-deferred))

(defthm fn-csa-admitted-post-keeps-twice-k-suffix
  (implies (equal (fn-csa-post-admission durable count k) :ok)
           (and (natp count) (posp k) (<= (nfix durable) count)
                (<= (- (+ 1 count) (nfix durable)) (* 2 k))))
  :rule-classes nil)

; No deferred/inflight observation authorizes borrowing the final slot.
(defthm fn-csa-post-beyond-twice-k-is-deferred
  (implies (< (* 2 k) (- (+ 1 count) (nfix durable)))
           (equal (fn-csa-post-admission durable count k) :checkpoint-deferred))
  :rule-classes nil)

(in-theory (disable fn-csa-post-admission))
