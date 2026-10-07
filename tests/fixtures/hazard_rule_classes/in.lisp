(in-package "ACL2")
; a comment that stays
(defthm a-plain (implies (foop x) (consp x)))
(local (defthm b-rewrite (implies (foop x) (car x)) :rule-classes :rewrite))
(encapsulate ()
 (defthm c-mixed (implies (foop x) (consp x))
   :rule-classes (:rewrite :forward-chaining)))
(defthmd d-only-list (implies (foop x) (consp x)) :rule-classes ((:rewrite)))
(defthm e-already (implies (foop x) (consp x)) :rule-classes nil)
