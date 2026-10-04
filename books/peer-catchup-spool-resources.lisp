; The actual private bank's cursor/termination observations. Admission and
; settlement are literal fn-rl-draw/fn-rl-settle; these helpers mint no grant.
(in-package "ACL2")
(include-book "peer-flight-reservation")

(defun fn-csp-candidate (index policy)
  (declare (xargs :guard t))
  (if (not (fn-pfr-policy-p policy)) nil
    (let* ((max (fn-pfr-at 2 policy))
           (i (if (and (natp index) (< index max)) index 0)))
      (list i (if (< (1+ i) max) (1+ i) 0)
            (fn-pfr-flight-slot i) (fn-pfr-work-slot i)))))

(defun fn-csp-bank-idle-from (slot fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger
                  :guard (and (natp slot) (fn-rl-wfp fn-resource-ledger))
                  :measure (nfix (- (nfix (fn-rl-count fn-resource-ledger)) (nfix slot)))
                  :verify-guards nil))
  (if (or (not (natp slot))
          (not (natp (fn-rl-count fn-resource-ledger)))
          (<= (fn-rl-count fn-resource-ledger) slot)) t
    (and (equal (fn-rl-phasesi slot fn-resource-ledger) 0)
         (fn-csp-bank-idle-from (1+ slot) fn-resource-ledger))))
(verify-guards fn-csp-bank-idle-from :hints (("Goal" :in-theory (enable fn-rl-wfp))))

(defun fn-csp-bank-idle-p (fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard (fn-rl-wfp fn-resource-ledger)))
  (fn-csp-bank-idle-from 2 fn-resource-ledger))


; The spool allowance one drawn flight lease carries (policy field 4, below
; 2^63 by fn-pfr-policy-p): the LIMIT fn-csp-begin admits writes against.
(defun fn-csp-flight-spool (policy)
  (declare (xargs :guard t))
  (if (fn-pfr-policy-p policy) (fn-pfr-at 4 policy) nil))

; The hash cursor's lease identity: the exact flight slot and generation.
(defun fn-csp-hash-lease (slot generation)
  (declare (xargs :guard t))
  (list slot generation))
