; Internal peer-adoption receipts.  This leaf has no config dependency so
; config's mutation fold can invalidate receipts without a dependency cycle.
; These reserved rows are adoption evidence, never generic operator input.
(in-package "ACL2")

(defun fn-par-field (n row)
  (declare (xargs :guard (natp n)))
  (if (consp row)
      (if (zp n) (car row) (fn-par-field (1- n) (cdr row)))
    nil))

(defun fn-par-receipt-slotp (slot)
  (declare (xargs :guard t))
  (or (equal slot "internal-invite-source")
      (equal slot "internal-invite-store")
      (equal slot "internal-invite-key-generation")))

(defun fn-par-receipt-rowp (row)
  (declare (xargs :guard t))
  (fn-par-receipt-slotp (fn-par-field 1 row)))

(defun fn-par-without-receipts (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (fn-par-receipt-rowp (car rows))
          (fn-par-without-receipts (cdr rows))
        (cons (car rows) (fn-par-without-receipts (cdr rows))))
    nil))

(defun fn-par-only-receipts (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (fn-par-receipt-rowp (car rows))
          (cons (car rows) (fn-par-only-receipts (cdr rows)))
        (fn-par-only-receipts (cdr rows)))
    nil))

(defun fn-par-receipt-freep (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (not (fn-par-receipt-rowp (car rows)))
           (fn-par-receipt-freep (cdr rows)))
    (equal rows nil)))

; Mutation removes adoption evidence, including attacker-supplied copies.
(defthm fn-par-without-receipts-is-receipt-free
  (fn-par-receipt-freep (fn-par-without-receipts rows)))

; Public receipt-free row semantics remain exactly unchanged.
(defthm fn-par-without-receipts-preserves-receipt-free-rows
  (implies (fn-par-receipt-freep rows)
           (equal (fn-par-without-receipts rows) rows)))

(defthm fn-par-without-receipts-idempotent
  (equal (fn-par-without-receipts (fn-par-without-receipts rows))
         (fn-par-without-receipts rows)))

(defthm fn-par-without-receipts-of-append
  (equal (fn-par-without-receipts (append a b))
         (append (fn-par-without-receipts a)
                 (fn-par-without-receipts b))))
