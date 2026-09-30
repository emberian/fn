; PRF-1169, A-SELECTED-RUNTIME-INITIALIZER-ARRAY: primary objects only.
(in-package "ACL2")
(defconst *fn-sria-coordinate*
 '(:sbcl "2.6.8" :x86-64-linux :saved-core-callback-policy
   :toolchain "fcedce7e3aa26e7ef93c7b3801bc39b2c56b7968cc1dfdf8e710a8931b349d52"
   :policy ((inhibit-warnings 3) (speed 3) (space 1) (safety 0) (debug 1) (compilation-speed 0))
   :foundation "3fbd390317fe7c3527add9c3d831ec967e8dccd3247142f2fa37fa29423697c4"
   :generated-macros "0532159809598bc45f39b9ae9615f35ddffd7e96b82ae4fe9dc9275473b79585"
   :standalone-callers "6d838ea8c7527fbf93c3fc5f125f64e4e3e9fe174beb4ee4ae698e3c45bcc941"
   :genuine-simple-ub8 :installed-hons-association-nil :primary-store-only))
(defun fn-sria-byte-domain-p (index value capacity coordinate)
 (declare (xargs :guard t))
 (and (equal coordinate *fn-sria-coordinate*)
      (natp index) (< index 65536) (natp value) (< value 256)
      (natp capacity) (< capacity 17592186044416) (< index capacity)))
(defun fn-sria-fill-domain-p (fill-value capacity coordinate)
 (declare (xargs :guard t))
 (and (equal coordinate *fn-sria-coordinate*)
      (natp fill-value) (<= fill-value 65536)
      (natp capacity) (< capacity 17592186044416) (<= fill-value capacity)))
; The coordinate requires genuine installed representation facts, not a shape
; assertion. The scalar bounds select actual initializer stores; they impose
; no data truncation. Existing larger backing capacities remain retained.
; Caller inlining/control, argument arithmetic, error/memoization, first-use,
; collector, backing constructor and lifetime costs are outside this unit.
(encapsulate
 (((fn-assume-sria-byte-primary-octets * * * *) => *)
  ((fn-assume-sria-fill-primary-octets * * *) => *))
 (local (defun fn-assume-sria-byte-primary-octets (i v c r)
          (declare (ignore i v c r)) 0))
 (local (defun fn-assume-sria-fill-primary-octets (f c r)
          (declare (ignore f c r)) 0))
 (defthm fn-assume-sria-byte-primary-natural
  (natp (fn-assume-sria-byte-primary-octets i v c r))
  :rule-classes :type-prescription)
 (defthm fn-assume-sria-fill-primary-natural
  (natp (fn-assume-sria-fill-primary-octets f c r))
  :rule-classes :type-prescription)
 (defthm fn-assume-sria-byte-primary-zero
  (implies (fn-sria-byte-domain-p i v c r)
           (equal (fn-assume-sria-byte-primary-octets i v c r) 0))
  :rule-classes nil)
 (defthm fn-assume-sria-fill-primary-zero
  (implies (fn-sria-fill-domain-p f c r)
           (equal (fn-assume-sria-fill-primary-octets f c r) 0))
  :rule-classes nil))
(defun fn-sria-byte-primary-request (index value capacity coordinate)
 (declare (xargs :guard t))
 (if (fn-sria-byte-domain-p index value capacity coordinate)
     (mv :primary-object 0 0) (mv :unavailable nil nil)))
(defun fn-sria-fill-primary-request (fill-value capacity coordinate)
 (declare (xargs :guard t))
 (if (fn-sria-fill-domain-p fill-value capacity coordinate)
     (mv :primary-object 0 0) (mv :unavailable nil nil)))
(verify-guards fn-sria-byte-domain-p)
(verify-guards fn-sria-fill-domain-p)
(verify-guards fn-sria-byte-primary-request)
(verify-guards fn-sria-fill-primary-request)
