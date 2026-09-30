; PRF-1132: actual profile-helper arithmetic under named single-primitive
; assumptions. Borrowed getter values, wrapper/constructor costs are separate.
(in-package "ACL2")
(include-book "payload-profile-source-trace")
(include-book "assumptions-selected-runtime-positive")

(defun fn-ppr-scale-factor (inputs)
  (if (fn-spp-factorp (car inputs)) (car inputs) (cadr inputs)))
(defun fn-ppr-scale-value (inputs)
  (if (fn-spp-factorp (car inputs)) (cadr inputs) (car inputs)))

(defun fn-ppr-arithmetic-domain (trace limit)
  (if (consp trace)
      (and (case (caar trace)
             (:negate (fn-srp-operand-domain-p :neg (cadar trace) limit))
             (:add (fn-srp-operand-domain-p :add (cadar trace) limit))
             (:multiply (and (true-listp (cadar trace))
                             (equal (len (cadar trace)) 2)
                             (fn-spp-operand-domain-p
                              (fn-ppr-scale-factor (cadar trace))
                              (fn-ppr-scale-value (cadar trace)) limit)))
             ((:borrow :multiple-value) t)
             (otherwise nil))
           (fn-ppr-arithmetic-domain (cdr trace) limit))
    (natp limit)))

(defun fn-ppr-arithmetic-octets (trace coordinate)
  (if (consp trace)
      (+ (case (caar trace)
           (:negate (fn-assume-srp-primitive-octets :neg (cadar trace) coordinate))
           (:add (fn-assume-srp-primitive-octets :add (cadar trace) coordinate))
           (:multiply (fn-assume-spp-multiply-octets
                       (fn-ppr-scale-factor (cadar trace))
                       (fn-ppr-scale-value (cadar trace)) coordinate))
           (otherwise 0))
         (fn-ppr-arithmetic-octets (cdr trace) coordinate))
    0))

(defthm fn-ppr-arithmetic-domain-natural-limit
  (implies (fn-ppr-arithmetic-domain trace limit) (natp limit))
  :rule-classes :forward-chaining)

(defthm fn-ppr-arithmetic-family-primitive-bound
  (implies (and (fn-srp-coordinate-p coordinate)
                (fn-ppr-arithmetic-domain trace limit))
           (<= (fn-ppr-arithmetic-octets trace coordinate)
               (* (+ (fn-pzt-count :negate trace) (fn-pzt-count :add trace)
                     (fn-pzt-count :multiply trace))
                  (fn-crw-primitive-buffer-octets limit))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-ppr-arithmetic-octets trace coordinate)
           :in-theory (enable fn-ppr-arithmetic-octets fn-ppr-arithmetic-domain))
          ("Subgoal *1/1"
           :use ((:instance fn-assume-srp-primitive-bound
                    (op :neg) (inputs (cadar trace)))
                 (:instance fn-assume-srp-primitive-bound
                    (op :add) (inputs (cadar trace)))
                 (:instance fn-assume-spp-multiply-primitive-bound
                    (factor (fn-ppr-scale-factor (cadar trace)))
                    (value (fn-ppr-scale-value (cadar trace)))))
           :in-theory (e/d (fn-ppr-arithmetic-octets fn-ppr-arithmetic-domain
                            fn-pzt-count)
                       (fn-srp-coordinate-p fn-crw-primitive-buffer-octets
                        fn-srp-operand-domain-p fn-spp-operand-domain-p
                        fn-ppr-scale-factor fn-ppr-scale-value)))))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-ppr-actual-stored-allowance-arithmetic-domain
   (implies (< (nfix compressed) 9223372036854775808)
            (fn-ppr-arithmetic-domain
             (cdr (fn-pzt-zin-stored-allowance compressed))
             18889465931478580854784))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (enable fn-pzt-zin-stored-allowance fn-ppr-arithmetic-domain
                    fn-ppr-scale-factor fn-ppr-scale-value
                    fn-spp-factorp fn-spp-operand-domain-p
                    fn-srp-operand-domain-p fn-srp-integer-inputs-fit))))
 (defthm fn-ppr-actual-budget-arithmetic-domain
   (implies (and (< (nfix compressed) 9223372036854775808)
                 (< (nfix expected) 4722366482869645213696))
            (fn-ppr-arithmetic-domain
             (cdr (fn-pzt-pzd-budget compressed expected))
             18889465931478580854784))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (enable fn-pzt-pzd-budget fn-ppr-arithmetic-domain
                    fn-ppr-scale-factor fn-ppr-scale-value
                    fn-spp-factorp fn-spp-operand-domain-p
                    fn-srp-operand-domain-p fn-srp-integer-inputs-fit)))))

(defthm fn-ppr-actual-stored-allowance-primitive-workspace
  (implies (and (fn-srp-coordinate-p coordinate)
                (< (nfix compressed) 9223372036854775808))
           (<= (fn-ppr-arithmetic-octets
                (cdr (fn-pzt-zin-stored-allowance compressed)) coordinate) 64))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-ppr-actual-stored-allowance-arithmetic-domain)
                       (:instance fn-pzt-zin-stored-allowance-source-counts)
                       (:instance fn-ppr-arithmetic-family-primitive-bound
                         (limit 18889465931478580854784)
                         (trace (cdr (fn-pzt-zin-stored-allowance compressed)))))
                  :in-theory (e/d (fn-crw-primitive-buffer-octets fn-crl-align16)
                      (fn-pzt-zin-stored-allowance fn-ppr-arithmetic-domain
                       fn-ppr-arithmetic-octets fn-srp-coordinate-p)))))

(defthm fn-ppr-actual-budget-primitive-workspace
  (implies (and (fn-srp-coordinate-p coordinate)
                (< (nfix compressed) 9223372036854775808)
                (< (nfix expected) 4722366482869645213696))
           (<= (fn-ppr-arithmetic-octets
                (cdr (fn-pzt-pzd-budget compressed expected)) coordinate) 128))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-ppr-actual-budget-arithmetic-domain)
                       (:instance fn-pzt-pzd-budget-source-counts
                         (clen compressed) (n expected))
                       (:instance fn-ppr-arithmetic-family-primitive-bound
                         (limit 18889465931478580854784)
                         (trace (cdr (fn-pzt-pzd-budget compressed expected)))))
                  :in-theory (e/d (fn-crw-primitive-buffer-octets fn-crl-align16)
                      (fn-pzt-pzd-budget fn-ppr-arithmetic-domain
                       fn-ppr-arithmetic-octets fn-srp-coordinate-p)))))

(in-theory (disable fn-ppr-scale-factor fn-ppr-scale-value
                    fn-ppr-arithmetic-domain fn-ppr-arithmetic-octets))
