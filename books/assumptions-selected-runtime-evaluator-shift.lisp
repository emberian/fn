; PRF-1174, actual evaluator's fitting positive ASH count3 objects only.
(in-package "ACL2")
(defconst *fn-sres-coordinate*
 '(:selected-evaluator-ash3
   :toolchain "fcedce7e3aa26e7ef93c7b3801bc39b2c56b7968cc1dfdf8e710a8931b349d52"
   :binary "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5"
   :saved-core "3f5b101bb9437d66366dc2a299b7f9cb98fdaf40d1add5caf8baef9e451dd07d"
   :primitive-artifact "04cb221b398b979d6e04b9fc846b7385bce45fe074f82e6e530c5b9fdd861777" :natural-input :count3 :fitting-result-primary-only))
(defun fn-sres-domain-p (value coordinate)
 (declare (xargs :guard t))
 (and (natp value) (<= (* 8 value) 4611686018427387903)
      (equal coordinate *fn-sres-coordinate*)))
(encapsulate
 (((fn-assume-sres-primary-object-octets * *) => *))
 (local (defun fn-assume-sres-primary-object-octets (value coordinate)
  (declare (ignore value coordinate)) 0))
 (defthm fn-assume-sres-primary-object-natural
  (natp (fn-assume-sres-primary-object-octets value coordinate))
  :rule-classes :type-prescription)
 (defthm fn-assume-sres-primary-object-zero
  (implies (fn-sres-domain-p value coordinate)
   (equal (fn-assume-sres-primary-object-octets value coordinate) 0))
  :rule-classes nil))
(defun fn-sres-primary-object-request (value coordinate)
 (declare (xargs :guard t))
 (if (fn-sres-domain-p value coordinate)
     (mv :primary-object 0 0) (mv :unavailable nil nil)))
(verify-guards fn-sres-domain-p)
(verify-guards fn-sres-primary-object-request)
; Input fit is derived, not an independent hypothesis or served validation.
(defthm fn-sres-domain-implies-input-immediate
 (implies (fn-sres-domain-p value coordinate)
          (and (integerp value) (<= 0 value)
               (<= value 4611686018427387903)))
 :hints (("Goal" :in-theory (enable fn-sres-domain-p)))
 :rule-classes nil)
