; Work accounting for the executable Wildmat dynamic-programming hot path.
;
; This book starts after successful parsing and UTF-8 decoding: PATTERNS is a
; parsed list and TARGET is its decoded scalar list.  It counts the recursive
; pattern, target-row, and rightmost-pattern list walks that the frozen matcher
; actually performs.  The RFC 3977 base grammar has exact items, * and ? only;
; it has no class, range, inversion, membership, reverse, append, nth, or len
; traversal in this hot path.

(in-package "ACL2")
(include-book "wildmat")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-wm-work-result (value cost) (list value cost))
(defun fn-wm-work-value (result) (car result))
(defun fn-wm-work-cost (result) (car (cdr result)))

(defthm fn-wm-work-value-result
  (equal (fn-wm-work-value (fn-wm-work-result value cost)) value))

(defthm fn-wm-work-cost-result
  (equal (fn-wm-work-cost (fn-wm-work-result value cost)) cost))

; One unit counts one actual recursive list-cell visit or output-row cons.
; Scalar comparison, tag tests, arithmetic, and list CAR/CDR at a visited cell
; are charged to that visit.  No unmodified matcher is assigned a budget: each
; worker below repeats its branch structure and returns its computed cost.

(defun fn-wm-false-row-work (target)
  (if (consp target)
      (let ((tail (fn-wm-false-row-work (cdr target))))
        (fn-wm-work-result (cons nil (fn-wm-work-value tail))
                           (1+ (fn-wm-work-cost tail))))
    (fn-wm-work-result nil 0)))

(defun fn-wm-initial-row-work (target)
  (let ((tail (fn-wm-false-row-work target)))
    (fn-wm-work-result (cons t (fn-wm-work-value tail))
                       (1+ (fn-wm-work-cost tail)))))

(defun fn-wm-step-character-aux-work (target previous item)
  (if (consp target)
      (let ((tail (fn-wm-step-character-aux-work (cdr target)
                                                  (cdr previous) item)))
        (fn-wm-work-result
         (cons (if (and (consp previous)
                         (fn-wildmat-item-character-matchp item (car target)))
                   (if (car previous) t nil)
                 nil)
               (fn-wm-work-value tail))
         (1+ (fn-wm-work-cost tail))))
    (fn-wm-work-result nil 0)))

(defun fn-wm-step-character-work (target previous item)
  (let ((tail (fn-wm-step-character-aux-work target previous item)))
    (fn-wm-work-result (cons nil (fn-wm-work-value tail))
                       (1+ (fn-wm-work-cost tail)))))

(defun fn-wm-step-star-aux-work (target previous-tail carry)
  (if (consp target)
      (let* ((next (fn-wildmat-bool-or (car previous-tail) carry))
             (tail (fn-wm-step-star-aux-work (cdr target)
                                              (cdr previous-tail) next)))
        (fn-wm-work-result (cons next (fn-wm-work-value tail))
                           (1+ (fn-wm-work-cost tail))))
    (fn-wm-work-result nil 0)))

(defun fn-wm-step-star-work (target previous)
  (let ((tail (fn-wm-step-star-aux-work target (cdr previous) (car previous))))
    (fn-wm-work-result (cons (car previous) (fn-wm-work-value tail))
                       (1+ (fn-wm-work-cost tail)))))

(defun fn-wm-pattern-row-work (items target row)
  (if (consp items)
      (let ((step (if (equal (car items) 42)
                      (fn-wm-step-star-work target row)
                    (fn-wm-step-character-work target row (car items)))))
        (let ((tail (fn-wm-pattern-row-work (cdr items) target
                                            (fn-wm-work-value step))))
          (fn-wm-work-result (fn-wm-work-value tail)
                             (+ 1 (fn-wm-work-cost step)
                                (fn-wm-work-cost tail)))))
    (fn-wm-work-result row 0)))

(defun fn-wm-row-last-work (row)
  (if (consp (cdr row))
      (let ((tail (fn-wm-row-last-work (cdr row))))
        (fn-wm-work-result (fn-wm-work-value tail)
                           (1+ (fn-wm-work-cost tail))))
    (fn-wm-work-result (car row) (if (consp row) 1 0))))

(defun fn-wm-pattern-match-work (items target)
  (let* ((initial (fn-wm-initial-row-work target))
         (row (fn-wm-pattern-row-work items target (fn-wm-work-value initial)))
         (last (fn-wm-row-last-work (fn-wm-work-value row))))
    (fn-wm-work-result (if (fn-wm-work-value last) t nil)
                       (+ (fn-wm-work-cost initial)
                          (fn-wm-work-cost row)
                          (fn-wm-work-cost last)))))

(defun fn-wm-rightmost-match-work (patterns target)
  (if (consp patterns)
      (let ((right (fn-wm-rightmost-match-work (cdr patterns) target)))
        (if (fn-wm-work-value right)
            (fn-wm-work-result (fn-wm-work-value right)
                               (1+ (fn-wm-work-cost right)))
          (let ((matched (fn-wm-pattern-match-work
                          (fn-wildmat-pattern-items (car patterns)) target)))
            (fn-wm-work-result
             (if (fn-wm-work-value matched) (car patterns) nil)
             (+ 1 (fn-wm-work-cost right) (fn-wm-work-cost matched))))))
    (fn-wm-work-result nil 0)))

(defun fn-wm-match-codepoints-work (patterns target)
  (let ((right (fn-wm-rightmost-match-work patterns target)))
    (fn-wm-work-result
     (if (fn-wm-work-value right)
         (if (fn-wildmat-pattern-positivep (fn-wm-work-value right)) t nil)
       nil)
     (1+ (fn-wm-work-cost right)))))

; ----------------------------------------------------------------------------
; Exact value projections to the frozen executable matcher.

(defthm fn-wm-false-row-work-value
  (equal (fn-wm-work-value (fn-wm-false-row-work target))
         (fn-wildmat-false-row target))
  :hints (("Goal" :induct (fn-wm-false-row-work target)
           :in-theory (enable fn-wm-false-row-work fn-wm-work-value))))

(defthm fn-wm-initial-row-work-value
  (equal (fn-wm-work-value (fn-wm-initial-row-work target))
         (fn-wildmat-initial-row target))
  :hints (("Goal" :in-theory (enable fn-wm-initial-row-work
                                      fn-wildmat-initial-row
                                      fn-wm-work-value))))

(defthm fn-wm-step-character-aux-work-value
  (equal (fn-wm-work-value (fn-wm-step-character-aux-work target previous item))
         (fn-wildmat-step-character-aux target previous item))
  :hints (("Goal" :induct (fn-wm-step-character-aux-work target previous item)
           :in-theory (enable fn-wm-step-character-aux-work
                              fn-wildmat-step-character-aux fn-wm-work-value))))

(defthm fn-wm-step-character-work-value
  (equal (fn-wm-work-value (fn-wm-step-character-work target previous item))
         (fn-wildmat-step-character target previous item))
  :hints (("Goal" :in-theory (enable fn-wm-step-character-work
                                      fn-wildmat-step-character fn-wm-work-value))))

(defthm fn-wm-step-star-aux-work-value
  (equal (fn-wm-work-value (fn-wm-step-star-aux-work target previous carry))
         (fn-wildmat-step-star-aux target previous carry))
  :hints (("Goal" :induct (fn-wm-step-star-aux-work target previous carry)
           :in-theory (enable fn-wm-step-star-aux-work
                              fn-wildmat-step-star-aux fn-wm-work-value))))

(defthm fn-wm-step-star-work-value
  (equal (fn-wm-work-value (fn-wm-step-star-work target previous))
         (fn-wildmat-step-star target previous))
  :hints (("Goal" :in-theory (enable fn-wm-step-star-work
                                      fn-wildmat-step-star fn-wm-work-value))))

(defthm fn-wm-step-character-aux-work-car
  (equal (car (fn-wm-step-character-aux-work target previous item))
         (fn-wildmat-step-character-aux target previous item))
  :hints (("Goal" :in-theory (enable fn-wm-work-value))))

(defthm fn-wm-step-star-aux-work-car
  (equal (car (fn-wm-step-star-aux-work target previous carry))
         (fn-wildmat-step-star-aux target previous carry))
  :hints (("Goal" :in-theory (enable fn-wm-work-value))))

(defthm fn-wm-pattern-row-work-car
  (equal (car (fn-wm-pattern-row-work items target row))
         (fn-wildmat-pattern-row items target row))
  :hints (("Goal" :induct (fn-wm-pattern-row-work items target row)
           :in-theory (enable fn-wm-pattern-row-work fn-wildmat-pattern-row)
           :do-not '(generalize fertilize))))

(defthm fn-wm-pattern-row-work-value
  (equal (fn-wm-work-value (fn-wm-pattern-row-work items target row))
         (fn-wildmat-pattern-row items target row))
  :hints (("Goal" :in-theory (enable fn-wm-work-value))))

(defthm fn-wm-row-last-work-value
  (equal (fn-wm-work-value (fn-wm-row-last-work row))
         (fn-wildmat-row-last row))
  :hints (("Goal" :induct (fn-wm-row-last-work row)
           :in-theory (enable fn-wm-row-last-work fn-wildmat-row-last
                              fn-wm-work-value))))

(defthm fn-wm-pattern-match-work-value
  (equal (fn-wm-work-value (fn-wm-pattern-match-work items target))
         (fn-wildmat-pattern-matchp items target))
  :hints (("Goal" :in-theory (enable fn-wm-pattern-match-work
                                      fn-wildmat-pattern-matchp fn-wm-work-value))))

(defthm fn-wm-rightmost-match-work-value
  (equal (fn-wm-work-value (fn-wm-rightmost-match-work patterns target))
         (fn-wildmat-rightmost-match patterns target))
  :hints (("Goal" :induct (fn-wm-rightmost-match-work patterns target)
           :in-theory (enable fn-wm-rightmost-match-work
                              fn-wildmat-rightmost-match fn-wm-work-value))))

(defthm fn-wm-rightmost-match-work-car
  (equal (car (fn-wm-rightmost-match-work patterns target))
         (fn-wildmat-rightmost-match patterns target))
  :hints (("Goal" :in-theory (enable fn-wm-work-value))))

(defthm fn-wm-match-codepoints-work-car
  (equal (car (fn-wm-match-codepoints-work patterns target))
         (fn-wildmat-match-codepoints patterns target))
  :hints (("Goal" :in-theory (enable fn-wm-match-codepoints-work
                                      fn-wildmat-match-codepoints))))

(defthm fn-wm-match-codepoints-work-value
  (equal (fn-wm-work-value (fn-wm-match-codepoints-work patterns target))
         (fn-wildmat-match-codepoints patterns target))
  :hints (("Goal" :in-theory (enable fn-wm-work-value))))

; ----------------------------------------------------------------------------
; Exact row costs and polynomial budgets.

(defthm fn-wm-false-row-work-cost
  (equal (fn-wm-work-cost (fn-wm-false-row-work target)) (len target))
  :hints (("Goal" :induct (fn-wm-false-row-work target)
           :in-theory (enable fn-wm-false-row-work fn-wm-work-cost))))

(defthm fn-wm-initial-row-work-cost
  (equal (fn-wm-work-cost (fn-wm-initial-row-work target)) (1+ (len target)))
  :hints (("Goal" :in-theory (enable fn-wm-initial-row-work fn-wm-work-cost))))

(defthm fn-wm-step-character-aux-work-cost
  (equal (fn-wm-work-cost (fn-wm-step-character-aux-work target previous item))
         (len target))
  :hints (("Goal" :induct (fn-wm-step-character-aux-work target previous item)
           :in-theory (enable fn-wm-step-character-aux-work fn-wm-work-cost))))

(defthm fn-wm-step-star-aux-work-cost
  (equal (fn-wm-work-cost (fn-wm-step-star-aux-work target previous carry))
         (len target))
  :hints (("Goal" :induct (fn-wm-step-star-aux-work target previous carry)
           :in-theory (enable fn-wm-step-star-aux-work fn-wm-work-cost))))

(defthm fn-wm-step-character-work-cost
  (equal (fn-wm-work-cost (fn-wm-step-character-work target previous item))
         (1+ (len target)))
  :hints (("Goal" :in-theory (enable fn-wm-step-character-work fn-wm-work-cost))))

(defthm fn-wm-step-star-work-cost
  (equal (fn-wm-work-cost (fn-wm-step-star-work target previous))
         (1+ (len target)))
  :hints (("Goal" :in-theory (enable fn-wm-step-star-work fn-wm-work-cost))))

(defthm fn-wm-pattern-row-work-cost
  (equal (fn-wm-work-cost (fn-wm-pattern-row-work items target row))
         (* (len items) (+ 2 (len target))))
  :hints (("Goal" :induct (fn-wm-pattern-row-work items target row)
           :in-theory (enable fn-wm-pattern-row-work fn-wm-work-cost))))

(defthm fn-wm-initial-row-work-nonempty
  (consp (fn-wm-work-value (fn-wm-initial-row-work target)))
  :hints (("Goal" :in-theory (enable fn-wm-initial-row-work fn-wm-work-value))))

(defthm fn-wm-step-character-work-nonempty
  (consp (fn-wm-work-value (fn-wm-step-character-work target previous item)))
  :hints (("Goal" :in-theory (enable fn-wm-step-character-work fn-wm-work-value))))

(defthm fn-wm-step-star-work-nonempty
  (consp (fn-wm-work-value (fn-wm-step-star-work target previous)))
  :hints (("Goal" :in-theory (enable fn-wm-step-star-work fn-wm-work-value))))

(defthm fn-wm-pattern-row-work-nonempty
  (implies (consp row)
           (consp (fn-wm-work-value (fn-wm-pattern-row-work items target row))))
  :hints (("Goal" :induct (fn-wm-pattern-row-work items target row)
           :in-theory (enable fn-wm-pattern-row-work fn-wm-work-value))))

(defthm fn-wm-row-last-work-cost
  (equal (fn-wm-work-cost (fn-wm-row-last-work row)) (len row))
  :hints (("Goal" :induct (fn-wm-row-last-work row)
           :in-theory (enable fn-wm-row-last-work fn-wm-work-cost))))

(defthm fn-wm-initial-row-work-length
  (equal (len (fn-wm-work-value (fn-wm-initial-row-work target)))
         (1+ (len target)))
  :hints (("Goal" :in-theory (enable fn-wm-initial-row-work
                                      fn-wm-work-value))))

(defthm fn-wm-step-character-work-length
  (equal (len (fn-wm-work-value
               (fn-wm-step-character-work target previous item)))
         (1+ (len target)))
  :hints (("Goal" :in-theory (enable fn-wm-step-character-work
                                      fn-wm-step-character-aux-work
                                      fn-wm-work-value))))

(defthm fn-wm-step-star-work-length
  (equal (len (fn-wm-work-value (fn-wm-step-star-work target previous)))
         (1+ (len target)))
  :hints (("Goal" :in-theory (enable fn-wm-step-star-work
                                      fn-wm-step-star-aux-work
                                      fn-wm-work-value))))

(defthm fn-wm-step-character-aux-work-length
  (equal (len (fn-wm-work-value
               (fn-wm-step-character-aux-work target previous item)))
         (len target))
  :hints (("Goal" :induct (fn-wm-step-character-aux-work target previous item)
           :in-theory (enable fn-wm-step-character-aux-work fn-wm-work-value))))

(defthm fn-wm-step-star-aux-work-length
  (equal (len (fn-wm-work-value
               (fn-wm-step-star-aux-work target previous carry)))
         (len target))
  :hints (("Goal" :induct (fn-wm-step-star-aux-work target previous carry)
           :in-theory (enable fn-wm-step-star-aux-work fn-wm-work-value))))

(defthm fn-wildmat-step-character-aux-length
  (equal (len (fn-wildmat-step-character-aux target previous item))
         (len target))
  :hints (("Goal" :induct (fn-wildmat-step-character-aux target previous item)
           :in-theory (enable fn-wildmat-step-character-aux))))

(defthm fn-wildmat-step-star-aux-length
  (equal (len (fn-wildmat-step-star-aux target previous carry))
         (len target))
  :hints (("Goal" :induct (fn-wildmat-step-star-aux target previous carry)
           :in-theory (enable fn-wildmat-step-star-aux))))

(defthm fn-wildmat-false-row-length
  (equal (len (fn-wildmat-false-row target)) (len target))
  :hints (("Goal" :induct (fn-wildmat-false-row target)
           :in-theory (enable fn-wildmat-false-row))))

(defthm fn-wildmat-initial-row-length
  (equal (len (fn-wildmat-initial-row target)) (1+ (len target)))
  :hints (("Goal" :in-theory (enable fn-wildmat-initial-row))))

(defthm fn-wildmat-step-character-length
  (equal (len (fn-wildmat-step-character target previous item))
         (1+ (len target)))
  :hints (("Goal" :in-theory (enable fn-wildmat-step-character))))

(defthm fn-wildmat-step-star-length
  (equal (len (fn-wildmat-step-star target previous))
         (1+ (len target)))
  :hints (("Goal" :in-theory (enable fn-wildmat-step-star))))

(defthm fn-wildmat-pattern-row-length
  (implies (equal (len row) (1+ (len target)))
           (equal (len (fn-wildmat-pattern-row items target row))
                  (1+ (len target))))
  :hints (("Goal" :induct (fn-wildmat-pattern-row items target row)
           :in-theory (enable fn-wildmat-pattern-row))))

(defthm fn-wm-pattern-row-work-length
  (implies (equal (len row) (1+ (len target)))
           (equal (len (fn-wm-work-value
                        (fn-wm-pattern-row-work items target row)))
                  (1+ (len target))))
  :hints (("Goal" :induct (fn-wm-pattern-row-work items target row)
           :in-theory (enable fn-wm-pattern-row-work fn-wm-work-value))))

; Keep the row value abstract while accounting for the actual final
; fn-wildmat-row-last scan.  The preceding row-length theorem supplies the
; only fact that scan needs; expanding the DP table here is unnecessary.
(defthm fn-wm-final-row-last-work-cost
  (equal
   (fn-wm-work-cost
    (fn-wm-row-last-work
     (fn-wm-work-value
      (fn-wm-pattern-row-work
       items target (fn-wm-work-value (fn-wm-initial-row-work target))))))
   (1+ (len target)))
  :hints (("Goal"
           :use ((:instance fn-wm-row-last-work-cost
                            (row
                             (fn-wm-work-value
                              (fn-wm-pattern-row-work
                               items target
                               (fn-wm-work-value
                                (fn-wm-initial-row-work target))))))
                 (:instance fn-wm-pattern-row-work-length
                            (row (fn-wm-work-value
                                  (fn-wm-initial-row-work target)))))
           :in-theory (disable fn-wm-row-last-work-cost
                               fn-wm-pattern-row-work-length
                               fn-wm-row-last-work
                               fn-wm-pattern-row-work
                               fn-wm-initial-row-work))))

(defthm fn-wm-pattern-match-work-cost-decomposition
  (equal (fn-wm-work-cost (fn-wm-pattern-match-work items target))
         (+ (fn-wm-work-cost (fn-wm-initial-row-work target))
            (fn-wm-work-cost
             (fn-wm-pattern-row-work
              items target (fn-wm-work-value (fn-wm-initial-row-work target))))
            (fn-wm-work-cost
             (fn-wm-row-last-work
              (fn-wm-work-value
               (fn-wm-pattern-row-work
                items target
                (fn-wm-work-value (fn-wm-initial-row-work target))))))))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-wm-pattern-match-work fn-wm-work-cost-result)))))

(defthm fn-wm-pattern-match-work-cost
  (equal (fn-wm-work-cost (fn-wm-pattern-match-work items target))
         (+ (* 2 (1+ (len target)))
            (* (len items) (+ 2 (len target)))))
  :hints (("Goal"
           :use ((:instance fn-wm-pattern-match-work-cost-decomposition)
                 (:instance fn-wm-initial-row-work-cost)
                 (:instance fn-wm-pattern-row-work-cost
                            (row (fn-wm-work-value
                                  (fn-wm-initial-row-work target))))
                 (:instance fn-wm-final-row-last-work-cost))
           :in-theory
           (e/d ()
                (fn-wm-work-cost fn-wm-work-value fn-wm-work-result
                 fn-wm-initial-row-work fn-wm-pattern-row-work
                 fn-wm-row-last-work)))))

; Sum item counts across the parsed list.  The rightmost implementation walks
; the complete list from the right and, in the worst case, runs the DP matcher
; for every pattern.
(defun fn-wm-total-items (patterns)
  (if (consp patterns)
      (+ (len (fn-wildmat-pattern-items (car patterns)))
         (fn-wm-total-items (cdr patterns)))
    0))

(defun fn-wm-rightmost-work-budget (patterns target)
  (if (consp patterns)
      (+ 1
         (+ (* 2 (1+ (len target)))
            (* (len (fn-wildmat-pattern-items (car patterns)))
               (+ 2 (len target))))
         (fn-wm-rightmost-work-budget (cdr patterns) target))
    0))

(defthm fn-wm-rightmost-match-work-cost-decomposition
  (equal (fn-wm-work-cost (fn-wm-rightmost-match-work patterns target))
         (if (consp patterns)
             (let ((right (fn-wm-rightmost-match-work (cdr patterns) target)))
               (if (fn-wm-work-value right)
                   (1+ (fn-wm-work-cost right))
                 (+ 1 (fn-wm-work-cost right)
                    (fn-wm-work-cost
                     (fn-wm-pattern-match-work
                      (fn-wildmat-pattern-items (car patterns)) target)))))
           0))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-wm-rightmost-match-work fn-wm-work-cost-result))))
  :rule-classes nil)

(defun fn-wm-pattern-list-induct (patterns)
  (if (consp patterns)
      (cons (car patterns) (fn-wm-pattern-list-induct (cdr patterns)))
    nil))

(defthm fn-wm-rightmost-match-work-cost-bound
  (<= (fn-wm-work-cost (fn-wm-rightmost-match-work patterns target))
      (fn-wm-rightmost-work-budget patterns target))
  :hints (("Goal" :induct (fn-wm-pattern-list-induct patterns)
           :in-theory (e/d (fn-wm-rightmost-match-work
                             fn-wm-rightmost-work-budget
                             fn-wm-work-cost fn-wm-work-value)
                            (fn-wm-pattern-match-work
                             fn-wm-pattern-row-work
                             fn-wm-row-last-work
                             fn-wm-initial-row-work)))))

(defthm fn-wm-rightmost-work-budget-polynomial
  (equal (fn-wm-rightmost-work-budget patterns target)
         (+ (len patterns)
            (* (len patterns) (* 2 (1+ (len target))))
            (* (fn-wm-total-items patterns) (+ 2 (len target)))))
  :hints (("Goal" :induct (fn-wm-rightmost-work-budget patterns target)
           :in-theory (enable fn-wm-rightmost-work-budget fn-wm-total-items))))

(defthm fn-wm-match-codepoints-work-cost-decomposition
  (equal (fn-wm-work-cost (fn-wm-match-codepoints-work patterns target))
         (1+ (fn-wm-work-cost
              (fn-wm-rightmost-match-work patterns target))))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-wm-match-codepoints-work fn-wm-work-cost-result))))
  :rule-classes nil)

(defthm fn-wm-add-one-monotone
  (implies (<= left right)
           (<= (1+ left) (1+ right))))

(defthm fn-wm-match-codepoints-work-cost-bound
  (<= (fn-wm-work-cost (fn-wm-match-codepoints-work patterns target))
      (1+ (fn-wm-rightmost-work-budget patterns target)))
  :hints (("Goal"
           :use ((:instance fn-wm-match-codepoints-work-cost-decomposition)
                 (:instance fn-wm-rightmost-match-work-cost-bound))
           :in-theory
           (e/d ()
                (fn-wm-work-cost fn-wm-match-codepoints-work
                 fn-wm-rightmost-match-work
                 fn-wm-rightmost-work-budget-polynomial)))))
