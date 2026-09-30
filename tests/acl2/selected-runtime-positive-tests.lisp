; Conditional single positive fixed-factor family, not compiled-site adequacy.
(in-package "ACL2")
(include-book "../../books/assumptions-selected-runtime-positive")
(defthm srpos-t-positive-full-domain
 (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
      (fn-srp-positive-operand-domain-p 256 9444732965739290427392 9444732965739290427392)
      (equal (fn-srp-positive-multiply-demand 256 9444732965739290427392
                                    *fn-srp-selected-coordinate*
                                    9444732965739290427392) 32)
      (natp (* 256 9444732965739290427392))
      (<= (* 256 9444732965739290427392) (* 256 9444732965739290427392))
      (<= (fn-assume-srp-positive-multiply-octets
           256 9444732965739290427392 *fn-srp-selected-coordinate*) 32))
 :hints (("Goal" :use ((:instance fn-assume-srp-positive-multiply-primitive-bound
     (coordinate *fn-srp-selected-coordinate*) (factor 256)
     (value 9444732965739290427392) (limit 9444732965739290427392)))
   :in-theory (enable fn-srp-positive-multiply-demand fn-srp-positive-operand-domain-p fn-srp-positive-factorp)))
 :rule-classes nil)
(defthm srpos-t-remove-coordinate
 (and (not (fn-srp-coordinate-p '(:wrong-compiler)))
      (fn-srp-positive-operand-domain-p 256 1 9444732965739290427392)
      (not (natp (fn-srp-positive-multiply-demand 256 1 '(:wrong-compiler)
                                        9444732965739290427392)))
      (equal (fn-srp-positive-multiply-demand 256 1 '(:wrong-compiler)
                                     9444732965739290427392) nil))
 :hints (("Goal" :in-theory (enable fn-srp-positive-multiply-demand fn-srp-positive-operand-domain-p fn-srp-positive-factorp)))
 :rule-classes nil)
(defthm srpos-t-remove-factor-domain
 (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
      (not (fn-srp-positive-factorp -256)) (natp 1) (natp 9444732965739290427392)
      (<= 1 9444732965739290427392)
      (not (natp (fn-srp-positive-multiply-demand -256 1 *fn-srp-selected-coordinate*
                                        9444732965739290427392))))
 :hints (("Goal" :in-theory (enable fn-srp-positive-multiply-demand fn-srp-positive-operand-domain-p fn-srp-positive-factorp)))
 :rule-classes nil)
(defthm srpos-t-remove-natural-value
 (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
      (fn-srp-positive-factorp 256) (not (natp -1)) (natp 9444732965739290427392)
      (<= -1 9444732965739290427392)
      (not (natp (fn-srp-positive-multiply-demand 256 -1 *fn-srp-selected-coordinate*
                                        9444732965739290427392))))
 :hints (("Goal" :in-theory (enable fn-srp-positive-multiply-demand fn-srp-positive-operand-domain-p fn-srp-positive-factorp)))
 :rule-classes nil)
(defthm srpos-t-remove-natural-limit
 (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
      (fn-srp-positive-factorp 256) (natp 1) (not (natp 3/2)) (<= 1 3/2)
      (not (natp (fn-srp-positive-multiply-demand 256 1 *fn-srp-selected-coordinate* 3/2))))
 :hints (("Goal" :in-theory (enable fn-srp-positive-multiply-demand fn-srp-positive-operand-domain-p fn-srp-positive-factorp)))
 :rule-classes nil)
(defthm srpos-t-remove-input-limit
 (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
      (fn-srp-positive-factorp 256) (natp 9444732965739290427393) (natp 9444732965739290427392)
      (not (<= 9444732965739290427393 9444732965739290427392))
      (not (natp (fn-srp-positive-multiply-demand 256 9444732965739290427393
                                       *fn-srp-selected-coordinate*
                                       9444732965739290427392))))
 :hints (("Goal" :in-theory (enable fn-srp-positive-multiply-demand fn-srp-positive-operand-domain-p fn-srp-positive-factorp)))
 :rule-classes nil)
; Product magnitude is not bounded by the input magnitude; the allocation
; row includes the extra result digit instead of truncating that product.
(defthm srpos-t-product-input-bound-mutation
 (and (fn-srp-positive-operand-domain-p 256 9444732965739290427392 9444732965739290427392)
      (< 9444732965739290427392 (* 256 9444732965739290427392)))
 :hints (("Goal" :in-theory (enable fn-srp-positive-operand-domain-p fn-srp-positive-factorp)))
 :rule-classes nil)
