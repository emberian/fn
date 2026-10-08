; Teeth for fn-wmc-core-codepoint-start-work-bound (PRF-016): the cursor
; machine the host steps (fn-wmc-one from fn-wmc-start-codepoints) starts
; with at most a polynomial number of remaining steps.  The bound has no
; hypothesis, so there is no removal witness; its teeth are a positive
; witness from an actual run of the machine (the steps it takes are the
; remaining count, one per accepted microstep) and mutations of the bound
; the statement refutes.
(in-package "ACL2")
(include-book "../../books/wildmat-cursor")
(include-book "../../books/defkeystone")

(defconst *wcb-patterns*
  (fn-wildmat-result-value
   (fn-wildmat-parse (fn-nntp-string-octets "fn.*,!fn.block,fn.block.good"))))
(defconst *wcb-target* '(102 110 46 98 108 111 99 107 46 103 111 111 100))

; An actual run of the machine: fn-wmc-core-one until the match is decided.
(defun wcb-run (s fuel)
  (declare (xargs :measure (nfix fuel) :verify-guards nil))
  (if (or (zp fuel) (fn-wmc-decidedp s)) 0 (1+ (wcb-run (fn-wmc-core-one s) (1- fuel)))))
(defun wcb-end (s fuel)
  (declare (xargs :measure (nfix fuel) :verify-guards nil))
  (if (or (zp fuel) (fn-wmc-decidedp s)) s (wcb-end (fn-wmc-core-one s) (1- fuel))))

(defconst *wcb-start* (fn-wmc-start-codepoints *wcb-patterns* *wcb-target*))
(defconst *wcb-bound*
  (+ 3 (* 12 (len *wcb-patterns*)) (* 4 (len *wcb-patterns*) (len *wcb-target*))
     (* (fn-wm-total-items *wcb-patterns*) (+ 6 (* 2 (len *wcb-target*))))))

; The run decides the match, takes exactly the remaining count of microsteps
; (one per step; 486 fuel does not finish it), and stays under the bound the
; keystone states.  The bound is not tight here (487 of 995): it is a
; polynomial in the pattern and target sizes, not the cost of this input.
(assert-event
 (and (fn-wmc-decidedp (wcb-end *wcb-start* 100000))
      (fn-wmc-matchedp (wcb-end *wcb-start* 100000))
      (equal (fn-wm-work-value (fn-wm-match-codepoints-work *wcb-patterns* *wcb-target*)) t)
      (equal (wcb-run *wcb-start* 100000) (fn-wmc-core-remaining *wcb-start*))
      (equal (wcb-run *wcb-start* 100000) 487)
      (not (fn-wmc-decidedp (wcb-end *wcb-start* 486)))
      (<= (wcb-run *wcb-start* 100000) *wcb-bound*)))

(defteeth fn-wmc-core-codepoint-start-work-bound
  :claim (()
          (<= (fn-wmc-core-remaining (fn-wmc-start-codepoints patterns target))
              (+ 3 (* 12 (len patterns)) (* 4 (len patterns) (len target))
                 (* (fn-wm-total-items patterns) (+ 6 (* 2 (len target)))))))
  :subject fn-wmc-start-codepoints
  :witness ((patterns *wcb-patterns*) (target *wcb-target*))
  :breaks ()
  :mutations ((items-term-dropped
               (:conclusion
                (<= (fn-wmc-core-remaining (fn-wmc-start-codepoints patterns target))
                    (+ 3 (* 12 (len patterns)) (* 4 (len patterns) (len target)))))
               ((patterns *wcb-patterns*) (target *wcb-target*))
               :fault "the bound forgets the per-item term, which dominates a pattern list with stars")
              (constant-bound
               (:conclusion
                (<= (fn-wmc-core-remaining (fn-wmc-start-codepoints patterns target)) 3))
               ((patterns *wcb-patterns*) (target *wcb-target*))
               :fault "the bound does not grow with the patterns or the target")))
