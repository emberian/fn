; A-SELECTED-RUNTIME-POSITIVE: reviewed single positive fixed-factor
; multiplication path only. Source/compiler lowering is a separate obligation.
(in-package "ACL2")
(include-book "assumptions-selected-runtime-primitives")

(defun fn-srp-positive-factorp (factor)
  (declare (xargs :guard t))
  (if (member-equal factor '(2 16 256)) t nil))

(defun fn-srp-positive-operand-domain-p (factor value limit)
  (declare (xargs :guard t))
  (and (fn-srp-positive-factorp factor) (natp value) (natp limit) (<= value limit)))

; The pinned generic positive bignum/fixnum path allocates inputdigits+1
; and normalizes in place. These factors have at most8bits; their product
; fits that extra digit. Negative-input copies, ratios and general multiply
; are excluded. This is not a claim about a compiled constant-multiply site.
(encapsulate
 (((fn-assume-srp-positive-multiply-octets * * *) => *))
 (local (defun fn-assume-srp-positive-multiply-octets (factor value coordinate)
          (declare (ignore factor value coordinate)) 0))
 (defthm fn-assume-srp-positive-multiply-octets-natural
   (natp (fn-assume-srp-positive-multiply-octets factor value coordinate))
   :rule-classes :type-prescription)
 (defthm fn-assume-srp-positive-multiply-primitive-bound
   (implies (and (fn-srp-coordinate-p coordinate)
                 (fn-srp-positive-operand-domain-p factor value limit))
            (<= (fn-assume-srp-positive-multiply-octets factor value coordinate)
                (fn-crw-primitive-buffer-octets limit)))
   :rule-classes nil))

(defun fn-srp-positive-multiply-demand (factor value coordinate limit)
  (declare (xargs :guard t))
  (and (fn-srp-coordinate-p coordinate)
       (fn-srp-positive-operand-domain-p factor value limit)
       (fn-crw-primitive-buffer-octets limit)))

(defthm fn-srp-positive-multiply-demand-selects-exact-domain
  (iff (natp (fn-srp-positive-multiply-demand factor value coordinate limit))
       (and (fn-srp-coordinate-p coordinate)
            (fn-srp-positive-operand-domain-p factor value limit)))
  :hints (("Goal" :in-theory (enable fn-srp-positive-multiply-demand)))
  :rule-classes nil)

(defthm fn-srp-positive-positive-product-domain
  (implies (fn-srp-positive-operand-domain-p factor value limit)
           (and (natp (* factor value))
                (<= (* factor value) (* 256 limit))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-srp-positive-factorp fn-srp-positive-operand-domain-p))))

(verify-guards fn-srp-positive-factorp)
(verify-guards fn-srp-positive-operand-domain-p)
(verify-guards fn-srp-positive-multiply-demand)

(in-theory (disable fn-srp-positive-factorp fn-srp-positive-operand-domain-p
                    fn-srp-positive-multiply-demand))
