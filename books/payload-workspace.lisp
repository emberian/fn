; The existing dedicated streaming-payload stripe, independent of machines.
; Block proofs/commitments retain their separate synchronous scratch row.
(in-package "ACL2")
(include-book "declare")
(fn2-book-layer :b)
(defun fn2-b-payload-retention-row (rows)
 (declare (xargs :guard t))
 (nfix (- (nfix rows) 4)))

(defun fn2-b-payload-retention-field-base (rows)
 (declare (xargs :guard t))
 (* 128 (fn2-b-payload-retention-row rows)))
