; A-SELECTED-RUNTIME-SHIFT-RESULT: one positive ASH result allocation at count1/4.
; Internal fixnum intermediates, compiler/call/collector lifetimes remain open.
(in-package "ACL2")
(include-book "assumptions-selected-runtime-primitives")

(defun fn-srp-positive-shift-countp (count)
 (declare (xargs :guard t))
 (if (member-equal count '(1 4)) t nil))

(defun fn-srp-positive-shift-domain-p (count value limit)
 (declare (xargs :guard t))
 (and (fn-srp-positive-shift-countp count) (natp value) (natp limit)
      (<= value limit)))

; SBCL2.6.8 positive bignum ASH, shifts1/4, allocates inputdigits+1.
; Positive fixnum ASH allocates at most2digits. There is no copied negative
; operand, variable huge shift, right-shift or ratio path in this row.
; Normalization does not refund the pre-normalization allocation.
(encapsulate
 (((fn-assume-srp-positive-shift-result-octets * * *) => *))
 (local (defun fn-assume-srp-positive-shift-result-octets (count value coordinate)
          (declare (ignore count value coordinate)) 0))
 (defthm fn-assume-srp-positive-shift-result-octets-natural
  (natp (fn-assume-srp-positive-shift-result-octets count value coordinate))
  :rule-classes :type-prescription)
 (defthm fn-assume-srp-positive-shift-result-bound
  (implies (and (fn-srp-coordinate-p coordinate)
                (fn-srp-positive-shift-domain-p count value limit))
           (<= (fn-assume-srp-positive-shift-result-octets count value coordinate)
               (fn-crw-primitive-buffer-octets limit)))
  :rule-classes nil))

(defun fn-srp-positive-shift-demand (count value coordinate limit)
 (declare (xargs :guard t))
 (and (fn-srp-coordinate-p coordinate)
      (fn-srp-positive-shift-domain-p count value limit)
      (fn-crw-primitive-buffer-octets limit)))

(defthm fn-srp-positive-shift-demand-selects-exact-domain
 (iff (natp (fn-srp-positive-shift-demand count value coordinate limit))
      (and (fn-srp-coordinate-p coordinate)
           (fn-srp-positive-shift-domain-p count value limit)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-srp-positive-shift-demand))))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-srp-positive-shift-result-domain
 (implies (fn-srp-positive-shift-domain-p count value limit)
          (and (natp (ash value count)) (<= (ash value count) (* 16 limit))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-srp-positive-shift-domain-p
                                   fn-srp-positive-shift-countp ash)))))

(verify-guards fn-srp-positive-shift-countp)
(verify-guards fn-srp-positive-shift-domain-p)
(verify-guards fn-srp-positive-shift-demand)
(in-theory (disable fn-srp-positive-shift-countp fn-srp-positive-shift-domain-p
                    fn-srp-positive-shift-demand))
