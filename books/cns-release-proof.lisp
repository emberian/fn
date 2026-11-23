; Discharge the core release obligation with the refinement book's theorem.
(in-package "ACL2")
(include-book "cns-release-refinement")
(include-book "owed-discharge")

(defthm fn2-cns-core-release-independent-proved
  (fn2-cns-core-release-independent$owed slot gen id ogen core)
  :rule-classes nil
  :hints (("Goal" :use fn2-cns-core-release-independent
                  :in-theory (union-theories
                              (theory 'minimal-theory)
                              '(fn2-cns-core-release-independent$owed)))))

(fn2-owed-discharge fn2-cns-core-release-independent
                    fn2-cns-core-release-independent-proved)
