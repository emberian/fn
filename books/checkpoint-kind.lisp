; Checkpoint scratch capacity is an admission profile, not a stored-data cap.
(in-package "ACL2")
(include-book "machines-b")
(include-book "checkpoint")
(fn2-book-layer :b)
(defun fn2-checkpoint-capacity (profile)
 (declare (xargs :guard t))
 (nfix (fn2-b-capacity :checkpoint-candidates 4 profile)))
(defcorechild fn2-core-checkpoints fn2-checkpoints
 :init (fn2-checkpoints-init (fn2-checkpoint-capacity profile) fn2-checkpoints)
 :profilep (unsigned-byte-p 32 (* 192 (fn2-checkpoint-capacity profile)))
 :why "Bounded active checkpoint publication and recovery candidates; pressure refuses admission.")
(defcorechild fn2-core-checkpoint-refs fn2-checkpoint-refs
 :init (fn2-checkpoint-refs-init (* 6 (fn2-checkpoint-capacity profile)) fn2-checkpoint-refs)
 :profilep (unsigned-byte-p 32 (* 192 (fn2-checkpoint-capacity profile)))
 :why "Descriptor plus five root references for each active checkpoint candidate.")
(defcorechild fn2-core-checkpoint-bytes fn2-checkpoint-bytes
 :init (fn2-checkpoint-bytes-init (* 192 (fn2-checkpoint-capacity profile)) fn2-checkpoint-bytes)
 :profilep (unsigned-byte-p 32 (* 192 (fn2-checkpoint-capacity profile)))
 :why "Immutable owned digest bytes survive reuse of format checker scratch rows.")
