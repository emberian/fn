; Actual budget's selected compiled constant factors become ASH count4/1.
; This roster prices shift RESULT storage and add primitives separately.
; Possible fixnum shift intermediates and whole call adequacy remain open.
(in-package "ACL2")
(include-book "payload-profile-source-trace")
(include-book "assumptions-selected-runtime-shift")

(defun fn-pbs-lower-budget-trace (trace)
 (if (consp trace)
     (cons (case (caar trace)
             (:multiply (list :positive-shift
                          (list (case (car (cadar trace)) (16 4) (2 1)
                                      (otherwise :unsupported))
                                (cadr (cadar trace)))
                          (caddar trace)))
             (:add (list :add (cadar trace) (caddar trace)))
             (:borrow (car trace))
             (otherwise (list :unsupported (cadar trace) (caddar trace))))
           (fn-pbs-lower-budget-trace (cdr trace)))
   nil))

(defun fn-pbs-trace-domain-p (trace limit)
 (if (consp trace)
     (and (case (caar trace)
            (:positive-shift
             (and (true-listp (cadar trace)) (equal (len (cadar trace)) 2)
                  (fn-srp-positive-shift-domain-p
                   (car (cadar trace)) (cadr (cadar trace)) limit)))
            (:add (fn-srp-operand-domain-p :add (cadar trace) limit))
            (:borrow t)
            (otherwise nil))
          (fn-pbs-trace-domain-p (cdr trace) limit))
   (natp limit)))

(defun fn-pbs-trace-octets (trace coordinate)
 (if (consp trace)
     (+ (case (caar trace)
          (:positive-shift (fn-assume-srp-positive-shift-result-octets
                            (car (cadar trace)) (cadr (cadar trace)) coordinate))
          (:add (fn-assume-srp-primitive-octets :add (cadar trace) coordinate))
          (otherwise 0))
        (fn-pbs-trace-octets (cdr trace) coordinate))
   0))

(defthm fn-pbs-trace-domain-natural-limit
 (implies (fn-pbs-trace-domain-p trace limit) (natp limit))
 :rule-classes :forward-chaining)

(defthm fn-pbs-trace-result-and-add-bound
 (implies (and (fn-srp-coordinate-p coordinate)
               (fn-pbs-trace-domain-p trace limit))
          (<= (fn-pbs-trace-octets trace coordinate)
              (* (+ (fn-pzt-count :positive-shift trace)
                    (fn-pzt-count :add trace))
                 (fn-crw-primitive-buffer-octets limit))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-pbs-trace-octets trace coordinate)
                  :in-theory (enable fn-pbs-trace-domain-p fn-pbs-trace-octets))
         ("Subgoal *1/1"
          :use ((:instance fn-assume-srp-positive-shift-result-bound
                  (count (car (cadar trace))) (value (cadr (cadar trace))))
                (:instance fn-assume-srp-primitive-bound
                  (op :add) (inputs (cadar trace))))
          :in-theory (e/d (fn-pbs-trace-domain-p fn-pbs-trace-octets fn-pzt-count)
                       (fn-srp-coordinate-p fn-crw-primitive-buffer-octets
                        fn-srp-positive-shift-domain-p fn-srp-operand-domain-p)))))

(defthm fn-pbs-actual-budget-lowered-counts
 (let ((trace (fn-pbs-lower-budget-trace (cdr (fn-pzt-pzd-budget compressed expected)))))
  (and (equal (fn-pzt-count :positive-shift trace) 2)
       (equal (fn-pzt-count :add trace) 2)
       (equal (fn-pzt-count :unsupported trace) 0)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-pzt-pzd-budget fn-pbs-lower-budget-trace))))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-pbs-actual-budget-lowered-domain
  (implies (and (< (nfix compressed) 9223372036854775808)
                (< (nfix expected) 4722366482869645213696))
           (fn-pbs-trace-domain-p
            (fn-pbs-lower-budget-trace (cdr (fn-pzt-pzd-budget compressed expected)))
            18889465931478580854784))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (enable fn-pzt-pzd-budget fn-pbs-lower-budget-trace fn-pbs-trace-domain-p
                   fn-srp-positive-shift-domain-p fn-srp-positive-shift-countp
                   fn-srp-operand-domain-p fn-srp-integer-inputs-fit)))))

(defthm fn-pbs-actual-budget-shift-result-and-add-workspace
 (implies (and (fn-srp-coordinate-p coordinate)
               (< (nfix compressed) 9223372036854775808)
               (< (nfix expected) 4722366482869645213696))
          (<= (fn-pbs-trace-octets
               (fn-pbs-lower-budget-trace
                (cdr (fn-pzt-pzd-budget compressed expected))) coordinate) 128))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-pbs-actual-budget-lowered-counts)
                (:instance fn-pbs-actual-budget-lowered-domain)
                (:instance fn-pbs-trace-result-and-add-bound
                  (limit 18889465931478580854784)
                  (trace (fn-pbs-lower-budget-trace
                          (cdr (fn-pzt-pzd-budget compressed expected))))))
          :in-theory (e/d (fn-crw-primitive-buffer-octets fn-crl-align16)
                       (fn-pzt-pzd-budget fn-pbs-lower-budget-trace
                        fn-pbs-trace-domain-p fn-pbs-trace-octets
                        fn-srp-coordinate-p)))))
