; Conditional single positive count1/4 ASH family, not compiled-site adequacy.
(in-package "ACL2")
(include-book "../../books/assumptions-selected-runtime-shift")
(defthm srshift-t-positive-full-domain
 (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
      (fn-srp-positive-shift-domain-p 4 9444732965739290427392 9444732965739290427392)
      (equal (fn-srp-positive-shift-demand 4 9444732965739290427392
                                    *fn-srp-selected-coordinate*
                                    9444732965739290427392) 32)
      (natp (ash 9444732965739290427392 4))
      (<= (ash 9444732965739290427392 4) (ash 9444732965739290427392 4))
      (<= (fn-assume-srp-positive-shift-result-octets
           4 9444732965739290427392 *fn-srp-selected-coordinate*) 32))
 :hints (("Goal" :use ((:instance fn-assume-srp-positive-shift-result-bound
     (coordinate *fn-srp-selected-coordinate*) (count 4)
     (value 9444732965739290427392) (limit 9444732965739290427392)))
   :in-theory (enable fn-srp-positive-shift-demand fn-srp-positive-shift-domain-p fn-srp-positive-shift-countp)))
 :rule-classes nil)
(defthm srshift-t-remove-coordinate
 (and (not (fn-srp-coordinate-p '(:wrong-compiler)))
      (fn-srp-positive-shift-domain-p 4 1 9444732965739290427392)
      (not (natp (fn-srp-positive-shift-demand 4 1 '(:wrong-compiler)
                                        9444732965739290427392)))
      (equal (fn-srp-positive-shift-demand 4 1 '(:wrong-compiler)
                                     9444732965739290427392) nil))
 :hints (("Goal" :in-theory (enable fn-srp-positive-shift-demand fn-srp-positive-shift-domain-p fn-srp-positive-shift-countp)))
 :rule-classes nil)
(defthm srshift-t-remove-factor-domain
 (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
      (not (fn-srp-positive-shift-countp -4)) (natp 1) (natp 9444732965739290427392)
      (<= 1 9444732965739290427392)
      (not (natp (fn-srp-positive-shift-demand -4 1 *fn-srp-selected-coordinate*
                                        9444732965739290427392))))
 :hints (("Goal" :in-theory (enable fn-srp-positive-shift-demand fn-srp-positive-shift-domain-p fn-srp-positive-shift-countp)))
 :rule-classes nil)
(defthm srshift-t-remove-natural-value
 (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
      (fn-srp-positive-shift-countp 4) (not (natp -1)) (natp 9444732965739290427392)
      (<= -1 9444732965739290427392)
      (not (natp (fn-srp-positive-shift-demand 4 -1 *fn-srp-selected-coordinate*
                                        9444732965739290427392))))
 :hints (("Goal" :in-theory (enable fn-srp-positive-shift-demand fn-srp-positive-shift-domain-p fn-srp-positive-shift-countp)))
 :rule-classes nil)
(defthm srshift-t-remove-natural-limit
 (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
      (fn-srp-positive-shift-countp 4) (natp 1) (not (natp 3/2)) (<= 1 3/2)
      (not (natp (fn-srp-positive-shift-demand 4 1 *fn-srp-selected-coordinate* 3/2))))
 :hints (("Goal" :in-theory (enable fn-srp-positive-shift-demand fn-srp-positive-shift-domain-p fn-srp-positive-shift-countp)))
 :rule-classes nil)
(defthm srshift-t-remove-input-limit
 (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
      (fn-srp-positive-shift-countp 4) (natp 9444732965739290427393) (natp 9444732965739290427392)
      (not (<= 9444732965739290427393 9444732965739290427392))
      (not (natp (fn-srp-positive-shift-demand 4 9444732965739290427393
                                       *fn-srp-selected-coordinate*
                                       9444732965739290427392))))
 :hints (("Goal" :in-theory (enable fn-srp-positive-shift-demand fn-srp-positive-shift-domain-p fn-srp-positive-shift-countp)))
 :rule-classes nil)
; Product magnitude is not bounded by the input magnitude; the allocation
; row includes the extra result digit instead of truncating that product.
(defthm srshift-t-product-input-bound-mutation
 (and (fn-srp-positive-shift-domain-p 4 9444732965739290427392 9444732965739290427392)
      (< 9444732965739290427392 (ash 9444732965739290427392 4)))
 :hints (("Goal" :in-theory (enable fn-srp-positive-shift-domain-p fn-srp-positive-shift-countp)))
 :rule-classes nil)
