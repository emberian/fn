; Explicit lowered ASH roster conditional teeth; no compiled-call adequacy.
(in-package "ACL2")
(include-book "../../books/payload-budget-shift-workspace")
(include-book "selected-runtime-shift-tests")

(defthm pbs-t-budget-full-positive
 (let* ((compressed 9223372036854775807)
        (expected (fn-zin-stored-allowance compressed))
        (trace (fn-pbs-lower-budget-trace
                (cdr (fn-pzt-pzd-budget compressed expected)))))
  (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
       (< (nfix compressed) 9223372036854775808)
       (< (nfix expected) 4722366482869645213696)
       (fn-pzw-stored-admissiblep compressed expected)
       (fn-pbs-trace-domain-p trace 18889465931478580854784)
       (equal (fn-pzt-count :positive-shift trace) 2)
       (equal (fn-pzt-count :add trace) 2)
       (equal (fn-pzt-count :unsupported trace) 0)
       (<= (fn-pbs-trace-octets trace *fn-srp-selected-coordinate*) 128)))
 :rule-classes nil
 :hints (("Goal"
   :use ((:instance fn-pbs-actual-budget-lowered-domain
            (compressed 9223372036854775807)
            (expected (fn-zin-stored-allowance 9223372036854775807)))
         (:instance fn-pbs-actual-budget-lowered-counts
            (compressed 9223372036854775807)
            (expected (fn-zin-stored-allowance 9223372036854775807)))
         (:instance fn-pbs-actual-budget-shift-result-and-add-workspace
            (coordinate *fn-srp-selected-coordinate*)
            (compressed 9223372036854775807)
            (expected (fn-zin-stored-allowance 9223372036854775807))))
   :in-theory (disable fn-pbs-lower-budget-trace fn-pzt-pzd-budget
                       fn-pbs-trace-domain-p fn-pbs-trace-octets))))

(defthm pbs-t-budget-domain-remove-compressed-bound
 (let* ((compressed 18889465931478580854785) (expected 1)
        (trace (fn-pbs-lower-budget-trace
                (cdr (fn-pzt-pzd-budget compressed expected)))))
  (and (not (< (nfix compressed) 9223372036854775808))
       (< (nfix expected) 4722366482869645213696)
       (not (fn-pbs-trace-domain-p trace 18889465931478580854784))))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (enable fn-pzt-pzd-budget fn-pbs-lower-budget-trace
                  fn-pbs-trace-domain-p fn-srp-positive-shift-domain-p
                  fn-srp-positive-shift-countp fn-srp-operand-domain-p
                  fn-srp-integer-inputs-fit))))

(defthm pbs-t-budget-domain-remove-decoded-bound
 (let* ((compressed 1) (expected 18889465931478580854785)
        (trace (fn-pbs-lower-budget-trace
                (cdr (fn-pzt-pzd-budget compressed expected)))))
  (and (< (nfix compressed) 9223372036854775808)
       (not (< (nfix expected) 4722366482869645213696))
       (not (fn-pbs-trace-domain-p trace 18889465931478580854784))))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (enable fn-pzt-pzd-budget fn-pbs-lower-budget-trace
                  fn-pbs-trace-domain-p fn-srp-positive-shift-domain-p
                  fn-srp-positive-shift-countp fn-srp-operand-domain-p
                  fn-srp-integer-inputs-fit))))

(defthm pbs-t-unsupported-factor-not-dropped-mutation
 (let ((trace (fn-pbs-lower-budget-trace '((:multiply (256 1) :wrong-site)))))
  (and (equal (len trace) 1)
       (equal (caar trace) :positive-shift)
       (equal (car (cadar trace)) :unsupported)
       (not (fn-pbs-trace-domain-p trace 18889465931478580854784))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pbs-lower-budget-trace
                          fn-pbs-trace-domain-p fn-srp-positive-shift-domain-p
                          fn-srp-positive-shift-countp))))
