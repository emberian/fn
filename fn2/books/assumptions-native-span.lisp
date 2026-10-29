(in-package "ACL2")

; The native zero-prefix primitive returns the ACL2 first-nonzero offset and
; leaves the pool unchanged. Startup and differential checks qualify this
; assumption; it is not a cryptographic collision assumption or a C proof.
(encapsulate
 (((fn2-a-native-span * *) => *))
 (local (defun fn2-a-native-span (reference native) (equal reference native)))
 (defthm fn2-a-native-span-correspondence
  (implies (fn2-a-native-span reference native) (equal reference native))
  :rule-classes nil))
