; A-SELECTED-RUNTIME-RX-COPY-COST, PRF-1160: conditional successful typed RX component cost, not whole turn.
(in-package "ACL2")
(defconst *fn-srxc-coordinate*
 '(:sbcl "2.6.8" :x86-64-linux :saved-core-callback-policy
   :toolchain "fcedce7e3aa26e7ef93c7b3801bc39b2c56b7968cc1dfdf8e710a8931b349d52"
   :policy ((inhibit-warnings 3) (speed 3) (space 1) (safety 0) (debug 1) (compilation-speed 0))
   :source "8dd305c7556ab984d301aa84f029a3cb248b69d807afac34f42acbd0db9d8b49" :copy-component "8192f1c5fb6645aa7f2b53982eee496fe9c3a7166317d9365259e92d121acbb4"
   :ub8-component "05e80c522ca8ed45d8be7962900357b355df94114c34c9e0ea7b631aa8ffdbe7" :libc "6791cc9bdc08295aafcfae01a7d66d788ee5577cbe94db00ace5f1ee04ef2b09"
   :memmove-offset 1776384 :memmove-limit 1778368
   :typed-simple-ub8 :stable-distinct-backings :component-only-participants-separately-charged))
(defun fn-srxc-domain-p (start end source-capacity destination-capacity coordinate)
 (declare (xargs :guard t))
 (and (equal coordinate *fn-srxc-coordinate*)
      (natp start) (natp end) (<= start end) (<= end 4096)
      (natp source-capacity) (< source-capacity (expt 2 44))
      (natp destination-capacity) (< destination-capacity (expt 2 44))
      (<= end source-capacity) (<= end destination-capacity)))
; Coordinate qualifiers require genuine installed source/provider identities
; and carried UB8/range relation. This predicate is not such an attestation.
(encapsulate
 (((fn-assume-srxc-success-object-octets * * * * *) => *)
  ((fn-assume-srxc-success-stack-octets * * * * *) => *))
 (local (defun fn-assume-srxc-success-object-octets (a b c d e)
          (declare (ignore a b c d e)) 0))
 (local (defun fn-assume-srxc-success-stack-octets (a b c d e)
          (declare (ignore a b c d e)) 0))
 (defthm fn-assume-srxc-success-object-natural
  (natp (fn-assume-srxc-success-object-octets a b c d e))
  :rule-classes :type-prescription)
 (defthm fn-assume-srxc-success-stack-natural
  (natp (fn-assume-srxc-success-stack-octets a b c d e))
  :rule-classes :type-prescription)
 (defthm fn-assume-srxc-success-component-bound
  (implies (fn-srxc-domain-p a b c d e)
   (and (equal (fn-assume-srxc-success-object-octets a b c d e) 0)
        (<= (fn-assume-srxc-success-stack-octets a b c d e) 192)))
  :rule-classes nil))
; Scalar three-MV candidate, never a grant/admission decision. Runtime uses
; the installed family relation; diagnostic mismatch gives unavailable.
(defun fn-srxc-success-component-request (start end source-capacity destination-capacity coordinate)
 (declare (xargs :guard t))
 (if (fn-srxc-domain-p start end source-capacity destination-capacity coordinate)
     (mv :success-component 0 192)
   (mv :unavailable nil nil)))
(verify-guards fn-srxc-domain-p)
(verify-guards fn-srxc-success-component-request)
