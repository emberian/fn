; Conditional single positive fixed-factor family, not compiled-site adequacy.
(in-package "ACL2")
(include-book "../../books/assumptions-selected-runtime-positive")
(defthm sppt-positive-full-domain
 (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
      (fn-spp-operand-domain-p 256 9444732965739290427392 9444732965739290427392)
      (equal (fn-spp-multiply-demand 256 9444732965739290427392
                                    *fn-srp-selected-coordinate*
                                    9444732965739290427392) 32)
      (natp (* 256 9444732965739290427392))
      (<= (* 256 9444732965739290427392) (* 256 9444732965739290427392))
      (<= (fn-assume-spp-multiply-octets
           256 9444732965739290427392 *fn-srp-selected-coordinate*) 32))
 :hints (("Goal" :use ((:instance fn-assume-spp-multiply-primitive-bound
     (coordinate *fn-srp-selected-coordinate*) (factor 256)
     (value 9444732965739290427392) (limit 9444732965739290427392)))
   :in-theory (enable fn-spp-multiply-demand fn-spp-operand-domain-p fn-spp-factorp)))
 :rule-classes nil)
(defthm sppt-remove-coordinate
 (and (not (fn-srp-coordinate-p '(:wrong-compiler)))
      (fn-spp-operand-domain-p 256 1 9444732965739290427392)
      (not (natp (fn-spp-multiply-demand 256 1 '(:wrong-compiler)
                                        9444732965739290427392)))
      (equal (fn-spp-multiply-demand 256 1 '(:wrong-compiler)
                                     9444732965739290427392) nil))
 :hints (("Goal" :in-theory (enable fn-spp-multiply-demand fn-spp-operand-domain-p fn-spp-factorp)))
 :rule-classes nil)
(defthm sppt-remove-factor-domain
 (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
      (not (fn-spp-factorp -256)) (natp 1) (natp 9444732965739290427392)
      (<= 1 9444732965739290427392)
      (not (natp (fn-spp-multiply-demand -256 1 *fn-srp-selected-coordinate*
                                        9444732965739290427392))))
 :hints (("Goal" :in-theory (enable fn-spp-multiply-demand fn-spp-operand-domain-p fn-spp-factorp)))
 :rule-classes nil)
(defthm sppt-remove-natural-value
 (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
      (fn-spp-factorp 256) (not (natp -1)) (natp 9444732965739290427392)
      (<= -1 9444732965739290427392)
      (not (natp (fn-spp-multiply-demand 256 -1 *fn-srp-selected-coordinate*
                                        9444732965739290427392))))
 :hints (("Goal" :in-theory (enable fn-spp-multiply-demand fn-spp-operand-domain-p fn-spp-factorp)))
 :rule-classes nil)
(defthm sppt-remove-natural-limit
 (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
      (fn-spp-factorp 256) (natp 1) (not (natp 3/2)) (<= 1 3/2)
      (not (natp (fn-spp-multiply-demand 256 1 *fn-srp-selected-coordinate* 3/2))))
 :hints (("Goal" :in-theory (enable fn-spp-multiply-demand fn-spp-operand-domain-p fn-spp-factorp)))
 :rule-classes nil)
(defthm sppt-remove-input-limit
 (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
      (fn-spp-factorp 256) (natp 9444732965739290427393) (natp 9444732965739290427392)
      (not (<= 9444732965739290427393 9444732965739290427392))
      (not (natp (fn-spp-multiply-demand 256 9444732965739290427393
                                       *fn-srp-selected-coordinate*
                                       9444732965739290427392))))
 :hints (("Goal" :in-theory (enable fn-spp-multiply-demand fn-spp-operand-domain-p fn-spp-factorp)))
 :rule-classes nil)
; Product magnitude is not bounded by the input magnitude; the allocation
; row includes the extra result digit instead of truncating that product.
(defthm sppt-product-input-bound-mutation
 (and (fn-spp-operand-domain-p 256 9444732965739290427392 9444732965739290427392)
      (< 9444732965739290427392 (* 256 9444732965739290427392)))
 :hints (("Goal" :in-theory (enable fn-spp-operand-domain-p fn-spp-factorp)))
 :rule-classes nil)
