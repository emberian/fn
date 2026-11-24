(in-package "ACL2")
(include-book "cns-draining-contract")
(include-book "owed-discharge")
(local (include-book "cns-draining-composition"))

(defthm fn2-cns-draining-counted-independent-proved
  (fn2-cns-draining-counted-independent$owed id budget core)
  :rule-classes nil
  :hints (("Goal"
           :use fn2-cns-draining-counted-independent-composed
           :in-theory '(fn2-cns-draining-counted-independent$owed))))

(fn2-owed-discharge fn2-cns-draining-counted-independent
                    fn2-cns-draining-counted-independent-proved)
