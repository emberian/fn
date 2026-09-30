; PRF-1173: A-SELECTED-RUNTIME-IMMEDIATE-ARITHMETIC, primary objects only.
(in-package "ACL2")
(defconst *fn-srif-coordinate*
 '(:sbcl "2.6.8" :x86-64-linux :saved-core-callback-policy
   :toolchain "fcedce7e3aa26e7ef93c7b3801bc39b2c56b7968cc1dfdf8e710a8931b349d52"
   :binary "b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5"
   :saved-core "3f5b101bb9437d66366dc2a299b7f9cb98fdaf40d1add5caf8baef9e451dd07d"
   :primitive-artifact "7a0d6da34d1d7d75f9e3cbbec66e25841f43b5e05b96f7fbc90222acf24dce8d"
   :actual-generic-add-subtract-multiply-and-floor1 :primary-result-path-only))
(defun fn-srif-immediatep (value)
 (declare (xargs :guard t))
 (and (integerp value) (<= -4611686018427387904 value)
      (<= value 4611686018427387903)))
(defun fn-srif-result (operation x y)
 (declare (xargs :guard t))
 (if (and (integerp x) (integerp y)
          (or (not (eq operation :floor)) (not (equal y 0))))
     (case operation (:add (+ x y)) (:subtract (- x y))
           (:multiply (* x y)) (:floor (floor x y)) (otherwise 0))
   0))
(defun fn-srif-domain-p (operation x y coordinate)
 (declare (xargs :guard t))
 (and (equal coordinate *fn-srif-coordinate*)
      (member-eq operation '(:add :subtract :multiply :floor))
      (fn-srif-immediatep x) (fn-srif-immediatep y)
      (or (not (eq operation :floor)) (and (<= 0 x) (< 0 y)))
      (fn-srif-immediatep (fn-srif-result operation x y))))
; This model selector must not become an unfunded served check: caller source
; proofs establish its operand/result conditions, and installation qualifies
; exact executed primitive targets. It does not cover arbitrary compiler
; lowering, bignums, division by zero, errors, asynchronous participants,
; collector, first-use, call/control frames or operation admission.
(encapsulate
 (((fn-assume-srif-primary-object-octets * * * *) => *))
 (local (defun fn-assume-srif-primary-object-octets (op x y coordinate)
          (declare (ignore op x y coordinate)) 0))
 (defthm fn-assume-srif-primary-object-natural
  (natp (fn-assume-srif-primary-object-octets op x y coordinate))
  :rule-classes :type-prescription)
 (defthm fn-assume-srif-primary-object-zero
  (implies (fn-srif-domain-p op x y coordinate)
           (equal (fn-assume-srif-primary-object-octets op x y coordinate) 0))
  :rule-classes nil))
(defun fn-srif-primary-object-request (operation x y coordinate)
 (declare (xargs :guard t))
 (if (fn-srif-domain-p operation x y coordinate)
     (mv :primary-object 0 0) (mv :unavailable nil nil)))
(verify-guards fn-srif-immediatep)
(verify-guards fn-srif-result)
(verify-guards fn-srif-domain-p)
(verify-guards fn-srif-primary-object-request)
