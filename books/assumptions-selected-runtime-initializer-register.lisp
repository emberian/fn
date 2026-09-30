; A-SELECTED-RUNTIME-INITIALIZER-REGISTER, PRF-1166; primary setter object only.
(in-package "ACL2")
(defconst *fn-srir-coordinate*
 '(:sbcl "2.6.8" :x86-64-linux :saved-core-callback-policy
   :toolchain "fcedce7e3aa26e7ef93c7b3801bc39b2c56b7968cc1dfdf8e710a8931b349d52"
   :policy ((inhibit-warnings 3) (speed 3) (space 1) (safety 0) (debug 1) (compilation-speed 0))
   :fn-zin-set-form "62ad1c5e760eb1bdf915cad1c6331456c29c33b7a5f575d2266145ee69dd3a70"
   :component "0a31062b01e3ae586cad641ac981c4eb9b7efd96ed63734775942370ff7aa8b4"
   :genuine-register-vector20 :borrowed-value :installed-hons-association-nil
   :standalone-setter-primary-object-only))
(defun fn-srir-domain-p (index value coordinate)
 (declare (xargs :guard t))
 (and (equal coordinate *fn-srir-coordinate*)
      (natp index) (< index 20) (natp value) (<= value 32768)))
; Value bound is the exact initializer operand domain, not a general data cap.
; Qualifiers need genuine installation/caller evidence; shape is no authority.
(encapsulate
 (((fn-assume-srir-primary-object-octets * * *) => *))
 (local (defun fn-assume-srir-primary-object-octets (i v c)
          (declare (ignore i v c)) 0))
 (defthm fn-assume-srir-primary-object-natural
  (natp (fn-assume-srir-primary-object-octets i v c))
  :rule-classes :type-prescription)
 (defthm fn-assume-srir-qualified-primary-object-bound
  (implies (fn-srir-domain-p i v c)
           (equal (fn-assume-srir-primary-object-octets i v c) 0))
  :rule-classes nil))
(defun fn-srir-primary-object-request (index value coordinate)
 (declare (xargs :guard t))
 (if (fn-srir-domain-p index value coordinate)
     (mv :primary-object 0 0) (mv :unavailable nil nil)))
(verify-guards fn-srir-domain-p)
(verify-guards fn-srir-primary-object-request)
