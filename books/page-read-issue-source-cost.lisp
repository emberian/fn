; Proof-only observation of the actual pre-admission resource issuer.
; These rosters are never constructed on the served path and are not a grant.
; Count explicit vector CONS and source ADD operations, separately from
; recognizer, comparison, call-frame, result-MV and collector obligations.
(in-package "ACL2")
(include-book "page-read-resources")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-prsc-at (n x)
 (declare (xargs :guard (natp n)))
 (if (consp x) (if (zp n) (car x) (fn-prsc-at (- n 1) (cdr x))) nil))
(defun fn-prsc-value (x) (declare (xargs :guard t)) (fn-prsc-at 0 x))
(defun fn-prsc-cells (x) (declare (xargs :guard t)) (nfix (fn-prsc-at 1 x)))
(defun fn-prsc-trace (x) (declare (xargs :guard t)) (fn-prsc-at 2 x))

; An observation is (actual-result explicit-vector-cells ordered-ADD-roster).
; Its own proof scaffolding is not included in the observed source cost.
(defun fn-prsc-plus (a b)
 (declare (xargs :guard t))
 (if (consp a)
  (let* ((left (nfix (car a)))
         (right (if (consp b) (nfix (car b)) 0))
         (value (+ left right))
         (rest (fn-prsc-plus (cdr a) (if (consp b) (cdr b) nil))))
   (list (cons value (fn-prsc-value rest))
         (+ 1 (fn-prsc-cells rest))
         (cons (list :add (list left right)) (fn-prsc-trace rest))))
  (list nil 0 nil)))

(defthm fn-prsc-plus-observes-actual-plus
 (equal (fn-prsc-value (fn-prsc-plus a b)) (fn-prs-plus a b))
 :hints (("Goal" :induct (fn-prsc-plus a b)
          :in-theory (enable fn-prsc-plus fn-prsc-value fn-prsc-at fn-prs-plus))))
(defthm fn-prsc-plus-cells
 (equal (fn-prsc-cells (fn-prsc-plus a b)) (len a))
 :hints (("Goal" :induct (fn-prsc-plus a b)
          :in-theory (enable fn-prsc-plus fn-prsc-cells fn-prsc-at))))
(defthm fn-prsc-plus-trace-length
 (equal (len (fn-prsc-trace (fn-prsc-plus a b))) (len a))
 :hints (("Goal" :induct (fn-prsc-plus a b)
          :in-theory (enable fn-prsc-plus fn-prsc-trace fn-prsc-at))))
(defthm fn-prsc-plus-trace-true-list
 (true-listp (fn-prsc-trace (fn-prsc-plus a b)))
 :hints (("Goal" :induct (fn-prsc-plus a b)
          :in-theory (enable fn-prsc-plus fn-prsc-trace fn-prsc-at))))

(local
 (defthm fn-prsc-trace-of-constructor
  (equal (fn-prsc-trace (list value cells trace)) trace)
  :hints (("Goal" :in-theory (enable fn-prsc-trace fn-prsc-at)))))
(local
 (defthm fn-prsc-true-list-append
  (implies (true-listp b) (true-listp (append a b)))
  :hints (("Goal" :induct (append a b)))))

(defun fn-prsc-funded (budget used rescue charged)
 (declare (xargs :guard t :guard-hints
  (("Goal" :in-theory (disable fn-prsc-plus fn-prsc-trace)))))
 (if (and (fn-prs-vectorp budget) (fn-prs-vectorp used)
          (fn-prs-vectorp rescue) (fn-prs-vectorp charged))
  (let* ((inner (fn-prsc-plus rescue charged))
         (outer (fn-prsc-plus used (fn-prsc-value inner))))
   (list (fn-prs-below (fn-prsc-value outer) budget)
         (+ (fn-prsc-cells inner) (fn-prsc-cells outer))
         (append (fn-prsc-trace inner) (fn-prsc-trace outer))))
  (list nil 0 nil)))

(defthm fn-prsc-funded-observes-actual-fundedp
 (equal (fn-prsc-value (fn-prsc-funded budget used rescue charged))
        (fn-prs-fundedp budget used rescue charged))
 :hints (("Goal" :in-theory
          (e/d (fn-prsc-funded fn-prsc-value fn-prsc-at fn-prs-fundedp)
               (fn-prsc-plus fn-prs-plus fn-prs-vectorp fn-prs-below)))))
(defthm fn-prsc-funded-trace-true-list
 (true-listp (fn-prsc-trace (fn-prsc-funded budget used rescue charged)))
 :hints (("Goal" :in-theory
          (e/d (fn-prsc-funded)
               (fn-prsc-plus fn-prsc-trace fn-prs-vectorp fn-prs-below)))))

(defun fn-prsc-issue (budget used rescue charged next limit demand)
 (declare (xargs :guard t :guard-hints
  (("Goal" :in-theory (disable fn-prsc-plus fn-prsc-funded fn-prsc-trace)))))
 (let ((initial (fn-prsc-funded budget used rescue charged)))
  (cond
   ((not (and (fn-prsc-value initial) (fn-prs-vectorp demand)
              (natp next) (natp limit)))
    (list (list :invalid-resource-state next charged)
          (fn-prsc-cells initial) (fn-prsc-trace initial)))
   ((>= next limit)
    (list (list :read-identities-exhausted next charged)
          (fn-prsc-cells initial) (fn-prsc-trace initial)))
   (t
    (let* ((proposed (fn-prsc-plus charged demand))
           (checked (fn-prsc-funded budget used rescue (fn-prsc-value proposed)))
           (cells (+ (fn-prsc-cells initial) (fn-prsc-cells proposed)
                     (fn-prsc-cells checked)))
           (trace (append (fn-prsc-trace initial)
                          (fn-prsc-trace proposed) (fn-prsc-trace checked))))
     (if (not (fn-prsc-value checked))
         (list (list :read-resources-unavailable next charged) cells trace)
       (let* ((issued (+ 1 next))
              (final (fn-prsc-plus charged demand)))
        (list (list :admitted issued (fn-prsc-value final))
              (+ cells (fn-prsc-cells final))
              (append trace (cons (list :add (list 1 next))
                                  (fn-prsc-trace final)))))))))))

(defthm fn-prsc-issue-observes-complete-actual-result
 (equal (fn-prsc-value (fn-prsc-issue budget used rescue charged next limit demand))
        (fn-prs-issue budget used rescue charged next limit demand))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (e/d (fn-prsc-issue fn-prsc-value fn-prsc-at fn-prs-issue)
               (fn-prsc-funded fn-prs-fundedp fn-prsc-plus fn-prs-plus
                fn-prs-vectorp fn-prsc-cells fn-prsc-trace)))))

(local
 (defthm fn-prsc-observation-fields
  (and (equal (fn-prsc-value (list value cells trace)) value)
       (equal (fn-prsc-cells (list value cells trace)) (nfix cells))
       (equal (fn-prsc-trace (list value cells trace)) trace))
  :hints (("Goal" :in-theory
           (enable fn-prsc-value fn-prsc-cells fn-prsc-trace fn-prsc-at)))))
(local
 (defthm fn-prsc-prs-plus-length
  (equal (len (fn-prs-plus a b)) (len a))
  :hints (("Goal" :induct (fn-prs-plus a b)
           :in-theory (enable fn-prs-plus)))))
(local
 (defthm fn-prsc-len-append
  (equal (len (append a b)) (+ (len a) (len b)))
  :hints (("Goal" :induct (append a b)))))

; Every successful issue executes both five-coordinate funding checks, the
; proposed charged-vector construction, and the final charged-vector rebuild.
; The arithmetic roster also includes the one actual nonce increment.
(defthm fn-prsc-admitted-issue-source-roster
 (implies
  (equal (mv-nth 0 (fn-prs-issue budget used rescue charged next limit demand)) :admitted)
  (and
   (equal (fn-prsc-cells (fn-prsc-issue budget used rescue charged next limit demand)) 30)
   (equal (len (fn-prsc-trace
                  (fn-prsc-issue budget used rescue charged next limit demand))) 31)))
 :rule-classes nil
 :hints (("Goal" :in-theory
   (e/d (fn-prsc-issue fn-prs-issue fn-prsc-funded fn-prs-fundedp
         fn-prs-vectorp)
        (fn-prsc-plus fn-prs-plus fn-prs-nats-p fn-prs-below fn-prsc-value
         fn-prsc-cells fn-prsc-trace)))))
