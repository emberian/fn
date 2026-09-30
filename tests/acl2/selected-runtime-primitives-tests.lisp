(in-package "ACL2")
(include-book "../../books/assumptions-selected-runtime-primitives")
(defthm fn-srpt-selected-table-positive
 (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
      (natp (expt 2 72))
      (equal (fn-srp-primitive-table *fn-srp-selected-coordinate* (expt 2 72))
             '((:constructor . 16) (:neg . 32) (:add . 32)))
      (equal (fn-srp-counted-heap-demand *fn-srp-selected-coordinate*
                                       (expt 2 72) 20 1 2) 416)
      (equal (fn-srp-counted-heap-demand *fn-srp-selected-coordinate*
                                       (- (expt 2 63) 33) 4 1 1) 128))
 :rule-classes nil)
(defthm fn-srpt-coordinate-refusal
 (and (not (fn-srp-coordinate-p '(:wrong-compiler)))
      (natp (expt 2 72)) (natp 20) (natp 1) (natp 2)
      (equal (fn-srp-primitive-table '(:wrong-compiler) (expt 2 72)) nil)
      (equal (fn-srp-counted-heap-demand '(:wrong-compiler)
                                       (expt 2 72) 20 1 2) nil))
 :rule-classes nil)
(defthm fn-srpt-scalar-domain-refusal
 (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
      (not (natp -1)) (natp 20) (natp 1) (natp 2)
      (equal (fn-srp-primitive-table *fn-srp-selected-coordinate* -1) nil)
      (equal (fn-srp-counted-heap-demand *fn-srp-selected-coordinate*
                                       -1 20 1 2) nil))
 :rule-classes nil)
(defthm fn-srpt-count-domain-refusal
 (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*) (natp (expt 2 72))
      (not (natp -1)) (natp 1) (natp 2)
      (equal (fn-srp-counted-heap-demand *fn-srp-selected-coordinate*
                                       (expt 2 72) -1 1 2) nil))
 :rule-classes nil)
(defthm fn-srpt-neg-domain-positive
 (let ((limit (expt 2 72)) (inputs (list (- (expt 2 72)))))
  (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
       (fn-srp-operand-domain-p :neg inputs limit)
       (<= (fn-assume-srp-primitive-octets :neg inputs *fn-srp-selected-coordinate*)
           (fn-crw-primitive-buffer-octets limit))))
 :hints (("Goal" :use ((:instance fn-assume-srp-primitive-bound
    (coordinate *fn-srp-selected-coordinate*) (op :neg)
    (inputs (list (- (expt 2 72)))) (limit (expt 2 72))))))
 :rule-classes nil)
(defthm fn-srpt-add-result-exceeds-input-domain-positive
 (let ((limit (expt 2 72)) (inputs (list (expt 2 72) (expt 2 72))))
  (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*)
       (fn-srp-operand-domain-p :add inputs limit)
       (< limit (+ (car inputs) (cadr inputs)))
       (<= (fn-assume-srp-primitive-octets :add inputs *fn-srp-selected-coordinate*)
           (fn-crw-primitive-buffer-octets limit))))
 :hints (("Goal" :use ((:instance fn-assume-srp-primitive-bound
    (coordinate *fn-srp-selected-coordinate*) (op :add)
    (inputs (list (expt 2 72) (expt 2 72))) (limit (expt 2 72))))))
 :rule-classes nil)
(defthm fn-srpt-counted-roster-positive
 (let* ((limit (expt 2 72)) (cells 20)
        (trace (list (list :neg (list (- limit)))
                     (list :add (list limit limit))
                     (list :add '(10 -1)))))
  (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*) (natp cells)
       (fn-srp-operation-trace-domain-p trace limit)
       (equal (fn-srp-operation-count :neg trace) 1)
       (equal (fn-srp-operation-count :add trace) 2)
       (equal (fn-srp-counted-heap-demand *fn-srp-selected-coordinate*
                                         limit cells 1 2) 416)
       (<= (+ (fn-assume-srp-constructor-octets cells *fn-srp-selected-coordinate*)
              (fn-srp-operation-trace-octets trace *fn-srp-selected-coordinate*))
           (fn-srp-counted-heap-demand *fn-srp-selected-coordinate*
                                      limit cells 1 2))))
 :hints (("Goal" :use ((:instance fn-srp-constructors-and-roster-within-counted-demand
   (coordinate *fn-srp-selected-coordinate*) (cells 20) (limit (expt 2 72))
   (trace (list (list :neg (list (- (expt 2 72))))
                (list :add (list (expt 2 72) (expt 2 72)))
                (list :add '(10 -1))))))
  :in-theory (disable fn-srp-operation-trace-octets)))
 :rule-classes nil)
(defthm fn-srpt-unsupported-operation-refusal
 (and (fn-srp-coordinate-p *fn-srp-selected-coordinate*) (natp (expt 2 72))
      (not (fn-srp-operand-domain-p :multiply '(2 3) (expt 2 72)))
      (equal (assoc-eq :multiply
               (fn-srp-primitive-table *fn-srp-selected-coordinate* (expt 2 72))) nil))
 :rule-classes nil)
