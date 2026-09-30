; A-SELECTED-RUNTIME-PRIMITIVES: allocated constructor and single signed
; NEG/ADD pre-normalization cost only. Not compiler/job/GC adequacy. The
; selected coordinate is a qualification requirement, not an attestation.
(in-package "ACL2")
(include-book "cold-read-window")
(local (include-book "arithmetic-5/top" :dir :system))

(defconst *fn-srp-selected-runtime*
 '("SBCL" "2.6.8" "X86-64" "Linux" 16 8 16 64
   "3c2e8e72846c5d5f5b359dba0d4c8ca45d2f4d32645bc2a435f49a860ba2d385"
   "ba8b9e29978637ba1fd38f78b5bbce5e1adcaf6a2bcf00b38804483865a1a710"))
(defconst *fn-srp-selected-compiler*
 '("ACL2" "8.7"
   "fcedce7e3aa26e7ef93c7b3801bc39b2c56b7968cc1dfdf8e710a8931b349d52"
   :saved-core-callback-policy
   ((compilation-speed 0) (speed 3) (space 1) (safety 0) (debug 1))))
(defconst *fn-srp-selected-attachment*
 '(fn-arena fn-arena-extent
   "b85578166e8a95cc85f6ed8cdc3fce5061a25e950d694c6baa11db6030f43875"
   "2fa48f94ce78c255b8946ab1dc08c97ac8c59a716a0f38b29313f086af0f426d"
   "4f7156dde0b8fba3dd87c502002ff0e345fa914f6ac7ada53e92a07aa49553c7"
   "b92756ab74520c90f7e8a75f57ed9126ffc7c4151bb0cdeb3d130d3927bb143c"
   "a9483a0abf4dd620"
   "67065e8585f7532a3216b488a02f2423374242dfe60d1c83d8fae9873ce38af6"))
(defconst *fn-srp-selected-coordinate*
 (list *fn-srp-selected-runtime* *fn-srp-selected-compiler*
       *fn-srp-selected-attachment*))
(defun fn-srp-coordinate-p (coordinate)
 (declare (xargs :guard t))
 (equal coordinate *fn-srp-selected-coordinate*))
(defun fn-srp-integer-inputs-fit (xs limit)
 (declare (xargs :guard t))
 (if (consp xs)
  (and (integerp (car xs)) (<= (- (ifix limit)) (car xs))
       (<= (car xs) (ifix limit))
       (fn-srp-integer-inputs-fit (cdr xs) limit)) t))
(defun fn-srp-operand-domain-p (op inputs limit)
 (declare (xargs :guard t))
 (and (natp limit) (true-listp inputs)
      (case op (:neg (equal (len inputs) 1))
               (:add (equal (len inputs) 2)) (otherwise nil))
      (fn-srp-integer-inputs-fit inputs limit)))

(defthm fn-srp-primitive-buffer-natural
 (natp (fn-crw-primitive-buffer-octets limit))
 :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :in-theory (enable fn-crw-primitive-buffer-octets fn-crl-align16))))

(encapsulate
 (((fn-assume-srp-constructor-octets * *) => *)
  ((fn-assume-srp-primitive-octets * * *) => *))
 (local (defun fn-assume-srp-constructor-octets (cells coordinate)
  (declare (ignore cells coordinate)) 0))
 (local (defun fn-assume-srp-primitive-octets (op inputs coordinate)
  (declare (ignore op inputs coordinate)) 0))
 (defthm fn-assume-srp-constructor-octets-natural
  (natp (fn-assume-srp-constructor-octets cells coordinate))
  :rule-classes :type-prescription)
 (defthm fn-assume-srp-primitive-octets-natural
  (natp (fn-assume-srp-primitive-octets op inputs coordinate))
  :rule-classes :type-prescription)
 (defthm fn-assume-srp-constructor-bound
  (implies (fn-srp-coordinate-p coordinate)
   (<= (fn-assume-srp-constructor-octets cells coordinate)
       (* 16 (nfix cells))))
  :rule-classes nil)
 (defthm fn-assume-srp-primitive-bound
  (implies (and (fn-srp-coordinate-p coordinate)
                (fn-srp-operand-domain-p op inputs limit))
   (<= (fn-assume-srp-primitive-octets op inputs coordinate)
       (fn-crw-primitive-buffer-octets limit)))
  :rule-classes nil))

; LIMIT bounds supplied operands. The buffer includes an extra result digit,
; not a promise that a signed result still lies inside that input domain.
; No division/multiply, conditions, frames, cache/TLS or first-use row exists.
(defun fn-srp-primitive-table (coordinate limit)
 (declare (xargs :guard t))
 (and (fn-srp-coordinate-p coordinate) (natp limit)
  (list (cons :constructor 16)
        (cons :neg (fn-crw-primitive-buffer-octets limit))
        (cons :add (fn-crw-primitive-buffer-octets limit)))))
(defun fn-srp-counted-heap-demand (coordinate limit cells negates adds)
 (declare (xargs :guard t))
 (and (fn-srp-coordinate-p coordinate) (natp limit)
      (natp cells) (natp negates) (natp adds)
      (+ (* 16 cells)
         (* (+ negates adds) (fn-crw-primitive-buffer-octets limit)))))

 ; Proof-only lowered-operation roster. A real caller supplies its actual
; source-to-roster and operand-domain theorem; this list is not constructed
; on a hot path.
(defun fn-srp-head (x)
 (declare (xargs :guard t)) (if (consp x) (car x) nil))
(defun fn-srp-tail (x)
 (declare (xargs :guard t)) (if (consp x) (cdr x) nil))
(defun fn-srp-operation-trace-domain-p (trace limit)
 (declare (xargs :guard t))
 (if (consp trace)
  (and (fn-srp-operand-domain-p (fn-srp-head (car trace))
         (fn-srp-head (fn-srp-tail (car trace))) limit)
       (fn-srp-operation-trace-domain-p (cdr trace) limit)) (natp limit)))
(defun fn-srp-operation-count (op trace)
 (declare (xargs :guard t))
 (if (consp trace)
  (+ (if (equal (fn-srp-head (car trace)) op) 1 0)
     (fn-srp-operation-count op (cdr trace))) 0))
(defun fn-srp-operation-trace-octets (trace coordinate)
 (declare (xargs :guard t))
 (if (consp trace)
  (+ (fn-assume-srp-primitive-octets (fn-srp-head (car trace))
         (fn-srp-head (fn-srp-tail (car trace))) coordinate)
     (fn-srp-operation-trace-octets (cdr trace) coordinate)) 0))
(defthm fn-srp-operation-trace-domain-implies-natural-limit
 (implies (fn-srp-operation-trace-domain-p trace limit) (natp limit))
 :hints (("Goal" :induct (fn-srp-operation-trace-domain-p trace limit)
          :in-theory (enable fn-srp-operation-trace-domain-p fn-srp-operand-domain-p)))
 :rule-classes :forward-chaining)
(defthm fn-srp-operation-trace-primitive-bound
 (implies (and (fn-srp-coordinate-p coordinate)
               (fn-srp-operation-trace-domain-p trace limit))
  (<= (fn-srp-operation-trace-octets trace coordinate)
      (* (+ (fn-srp-operation-count :neg trace)
            (fn-srp-operation-count :add trace))
         (fn-crw-primitive-buffer-octets limit))))
 :hints (("Goal" :induct (fn-srp-operation-trace-octets trace coordinate)
          :in-theory (enable fn-srp-operation-trace-octets
             fn-srp-operation-trace-domain-p fn-srp-operation-count))
         ("Subgoal *1/1"
          :use ((:instance fn-assume-srp-primitive-bound
              (op (fn-srp-head (car trace)))
              (inputs (fn-srp-head (fn-srp-tail (car trace))))))
          :in-theory (e/d (fn-srp-operation-trace-octets
              fn-srp-operation-trace-domain-p fn-srp-operation-count
              fn-srp-operand-domain-p)
             (fn-srp-coordinate-p fn-crw-primitive-buffer-octets))))
 :rule-classes nil)
(defthm fn-srp-constructors-and-roster-within-counted-demand
 (implies (and (fn-srp-coordinate-p coordinate) (natp cells)
               (fn-srp-operation-trace-domain-p trace limit))
  (<= (+ (fn-assume-srp-constructor-octets cells coordinate)
         (fn-srp-operation-trace-octets trace coordinate))
      (fn-srp-counted-heap-demand coordinate limit cells
         (fn-srp-operation-count :neg trace)
         (fn-srp-operation-count :add trace))))
 :hints (("Goal"
          :use ((:instance fn-assume-srp-constructor-bound)
                (:instance fn-srp-operation-trace-primitive-bound))
          :in-theory (e/d (fn-srp-counted-heap-demand)
             (fn-srp-coordinate-p fn-crw-primitive-buffer-octets
              fn-srp-operation-trace-domain-p fn-srp-operation-trace-octets
              fn-srp-operation-count))))
 :rule-classes nil)
