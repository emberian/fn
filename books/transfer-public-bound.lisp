; Polynomial work bound for the total public missing-range read.
;
; The costed implementation counts recursive list-cell visits plus primitive
; numeric checks.  Its structural equality worker charges every compared cons
; and atom node.  FN-TRANSFER-TREE-SIZE counts cons cells throughout an
; arbitrary ACL2 value; atoms have structural size zero.

(in-package "ACL2")
(include-book "transfer-public-work")
(include-book "transfer-invariants")
(local (include-book "arithmetic/top" :dir :system))
(local
 (in-theory
  (disable fn-transfer-true-list-work-value
           fn-transfer-at-most-work-value
           fn-transfer-octet-list-work-value
           fn-transfer-true-list-work-car-value
           fn-transfer-at-most-work-car-value
           fn-transfer-octet-list-work-car-value
           fn-transfer-profile-work-value
           fn-transfer-label-work-value
           fn-transfer-chunk-input-work-value
           fn-transfer-chunk-work-value
           fn-transfer-ranges-overlap-work-value
           fn-transfer-no-overlaps-work-value
           fn-transfer-chunk-list-work-value
           fn-transfer-chunk-list-work-car-value
           fn-transfer-entry-work-value
           fn-transfer-entries-work-value
           fn-transfer-entries-work-car-value
           fn-transfer-equal-work-value
           fn-transfer-equal-work-car-value
           fn-transfer-label-absent-work-value
           fn-transfer-distinct-labels-work-value
           fn-transfer-distinct-labels-work-car-value
           fn-transfer-reserved-bytes-work-value
           fn-transfer-reserved-bytes-work-car-value
           fn-transfer-state-work-value
           fn-transfer-find-entry-work-value
           fn-transfer-find-entry-work-car-value
           fn-transfer-missing-ranges-work-value)))

(defun fn-transfer-tree-size (x)
  (if (consp x)
      (+ 1
         (fn-transfer-tree-size (car x))
         (fn-transfer-tree-size (cdr x)))
    0))

(defthm fn-transfer-tree-size-natp
  (natp (fn-transfer-tree-size x))
  :rule-classes :type-prescription)

(defthm fn-transfer-tree-size-car-bound
  (<= (fn-transfer-tree-size (car x))
      (fn-transfer-tree-size x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-transfer-tree-size))))

(defthm fn-transfer-tree-size-cdr-bound
  (<= (fn-transfer-tree-size (cdr x))
      (fn-transfer-tree-size x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-transfer-tree-size))))

(defthm fn-transfer-tree-size-cadr-bound
  (<= (fn-transfer-tree-size (car (cdr x)))
      (fn-transfer-tree-size x))
  :rule-classes :linear
  :hints (("Goal"
           :use ((:instance fn-transfer-tree-size-car-bound (x (cdr x)))
                 (:instance fn-transfer-tree-size-cdr-bound)))))

(defthm fn-transfer-tree-size-caddr-bound
  (<= (fn-transfer-tree-size (car (cdr (cdr x))))
      (fn-transfer-tree-size x))
  :rule-classes :linear
  :hints (("Goal"
           :use ((:instance fn-transfer-tree-size-cadr-bound (x (cdr x)))
                 (:instance fn-transfer-tree-size-cdr-bound)))))

(defthm fn-transfer-len-tree-size-bound
  (<= (len x) (fn-transfer-tree-size x))
  :rule-classes :linear
  :hints (("Goal" :induct (len x)
           :in-theory (enable fn-transfer-tree-size))))

(defthm fn-transfer-true-list-work-tree-bound
  (<= (fn-transfer-work-cost (fn-transfer-true-list-work x))
      (fn-transfer-tree-size x))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-transfer-true-list-work x)
           :in-theory (enable fn-transfer-true-list-work
                              fn-transfer-work-cost
                              fn-transfer-tree-size))))

(defthm fn-transfer-at-most-work-tree-bound
  (<= (fn-transfer-work-cost (fn-transfer-at-most-work xs bound))
      (1+ (fn-transfer-tree-size xs)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-transfer-at-most-work xs bound)
           :in-theory (enable fn-transfer-at-most-work
                              fn-transfer-work-cost
                              fn-transfer-tree-size))))

(defthm fn-transfer-octet-list-work-tree-bound
  (<= (fn-transfer-work-cost (fn-transfer-octet-list-work xs))
      (fn-transfer-tree-size xs))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-transfer-octet-list-work xs)
           :in-theory (enable fn-transfer-octet-list-work
                              fn-transfer-work-cost
                              fn-transfer-tree-size))))

(defthm fn-transfer-true-list-work-cost-natp
  (natp (cadr (fn-transfer-true-list-work x)))
  :rule-classes :type-prescription
  :hints (("Goal"
           :induct (fn-transfer-true-list-work x)
           :in-theory (enable fn-transfer-true-list-work))))

(defthm fn-transfer-at-most-work-cost-natp
  (natp (cadr (fn-transfer-at-most-work xs bound)))
  :rule-classes :type-prescription
  :hints (("Goal"
           :induct (fn-transfer-at-most-work xs bound)
           :in-theory (enable fn-transfer-at-most-work))))

(defthm fn-transfer-octet-list-work-cost-natp
  (natp (cadr (fn-transfer-octet-list-work xs)))
  :rule-classes :type-prescription
  :hints (("Goal"
           :induct (fn-transfer-octet-list-work xs)
           :in-theory (enable fn-transfer-octet-list-work))))

(defthm fn-transfer-profile-work-tree-bound
  (<= (fn-transfer-work-cost (fn-transfer-profile-work profile))
      (* 9 (1+ (fn-transfer-tree-size profile))))
  :hints (("Goal"
           :in-theory (enable fn-transfer-profile-work
                              fn-transfer-work-cost)
           :use ((:instance fn-transfer-len-tree-size-bound (x profile))))))

(defthm fn-transfer-label-work-tree-bound
  (<= (fn-transfer-work-cost (fn-transfer-label-work label profile))
      (+ 1 (* 2 (fn-transfer-tree-size label))))
  :hints (("Goal"
           :in-theory (enable fn-transfer-label-work
                              fn-transfer-work-cost)
           :use ((:instance fn-transfer-at-most-work-tree-bound
                            (xs label)
                            (bound (fn-transfer-max-label profile)))
                 (:instance fn-transfer-octet-list-work-tree-bound
                            (xs label))))))

(defthm fn-transfer-label-work-cost-natp
  (natp (cadr (fn-transfer-label-work label profile)))
  :rule-classes :type-prescription
  :hints (("Goal"
           :in-theory (e/d (fn-transfer-label-work)
                            (fn-transfer-at-most-work
                             fn-transfer-octet-list-work)))))

(defthm fn-transfer-chunk-input-work-tree-bound
  (<= (fn-transfer-work-cost
       (fn-transfer-chunk-input-work octets profile))
      (+ 1 (* 2 (fn-transfer-tree-size octets))))
  :hints (("Goal"
           :in-theory (enable fn-transfer-chunk-input-work
                              fn-transfer-work-cost)
           :use ((:instance fn-transfer-at-most-work-tree-bound
                            (xs octets)
                            (bound (fn-transfer-max-chunk profile)))
                 (:instance fn-transfer-octet-list-work-tree-bound
                            (xs octets))))))

(defthm fn-transfer-chunk-input-work-cost-natp
  (natp (cadr (fn-transfer-chunk-input-work octets profile)))
  :rule-classes :type-prescription
  :hints (("Goal"
           :in-theory (e/d (fn-transfer-chunk-input-work)
                            (fn-transfer-at-most-work
                             fn-transfer-octet-list-work)))))

(defthm fn-transfer-chunk-work-ambient-bound
  (implies (and (natp ambient)
                (<= (fn-transfer-tree-size chunk) ambient))
           (<= (fn-transfer-work-cost
                (fn-transfer-chunk-work chunk declared-length profile))
               (+ 5 (* 5 ambient))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (enable fn-transfer-chunk-work
                              fn-transfer-work-cost)
           :use ((:instance fn-transfer-true-list-work-tree-bound (x chunk))
                 (:instance fn-transfer-len-tree-size-bound (x chunk))
                 (:instance fn-transfer-len-tree-size-bound
                            (x (fn-transfer-chunk-octets chunk)))
                 (:instance fn-transfer-chunk-input-work-tree-bound
                            (octets (fn-transfer-chunk-octets chunk)))))))

(defthm fn-transfer-chunk-work-cadr-ambient-bound
  (implies (and (natp ambient)
                (<= (fn-transfer-tree-size chunk) ambient))
           (<= (cadr (fn-transfer-chunk-work
                      chunk declared-length profile))
               (+ 5 (* 5 ambient))))
  :hints (("Goal"
           :in-theory (enable fn-transfer-work-cost)
           :use ((:instance fn-transfer-chunk-work-ambient-bound)))))

(defthm fn-transfer-chunk-work-cost-natp
  (natp (cadr (fn-transfer-chunk-work chunk declared-length profile)))
  :rule-classes :type-prescription
  :hints (("Goal"
           :in-theory (e/d (fn-transfer-chunk-work)
                            (fn-transfer-true-list-work
                             fn-transfer-len-work
                             fn-transfer-chunk-input-work
                             fn-transfer-octet-list-work)))))

(defthm fn-transfer-ranges-overlap-work-ambient-bound
  (implies (and (natp ambient)
                (<= (fn-transfer-tree-size left) ambient)
                (<= (fn-transfer-tree-size right) ambient))
           (<= (fn-transfer-work-cost
                (fn-transfer-ranges-overlap-work left right))
               (+ 2 (* 2 ambient))))
  :hints (("Goal"
           :in-theory (enable fn-transfer-ranges-overlap-work
                              fn-transfer-work-cost)
           :use ((:instance fn-transfer-len-tree-size-bound
                            (x (fn-transfer-chunk-octets left)))
                 (:instance fn-transfer-len-tree-size-bound
                            (x (fn-transfer-chunk-octets right)))))))

(defthm fn-transfer-ranges-overlap-work-cadr-ambient-bound
  (implies (and (natp ambient)
                (<= (fn-transfer-tree-size left) ambient)
                (<= (fn-transfer-tree-size right) ambient))
           (<= (cadr (fn-transfer-ranges-overlap-work left right))
               (+ 2 (* 2 ambient))))
  :hints (("Goal"
           :in-theory (enable fn-transfer-work-cost)
           :use ((:instance fn-transfer-ranges-overlap-work-ambient-bound)))))

(defthm fn-transfer-ranges-overlap-work-cost-natp
  (natp (cadr (fn-transfer-ranges-overlap-work left right)))
  :rule-classes :type-prescription
  :hints (("Goal"
           :in-theory (enable fn-transfer-ranges-overlap-work))))

(defun fn-transfer-public-overlap-budget (ambient)
  (+ 2 (* 2 (nfix ambient))))

(defun fn-transfer-public-chunk-list-step-budget (ambient)
  (+ 5
     (* 5 (nfix ambient))
     (* (nfix ambient) (fn-transfer-public-overlap-budget ambient))))

(defun fn-transfer-public-entry-budget (ambient)
  (+ 5
     (* 5 (nfix ambient))
     (* (nfix ambient)
        (fn-transfer-public-chunk-list-step-budget ambient))))

(defun fn-transfer-public-state-validation-budget (ambient)
  (+ 16
     (* 16 (nfix ambient))
     (* (nfix ambient) (fn-transfer-public-entry-budget ambient))
     (* (nfix ambient)
        (nfix ambient)
        (1+ (* 2 (nfix ambient))))))

(defthm fn-transfer-public-overlap-budget-natp
  (natp (fn-transfer-public-overlap-budget ambient))
  :rule-classes :type-prescription)

(defthm fn-transfer-public-chunk-list-step-budget-natp
  (natp (fn-transfer-public-chunk-list-step-budget ambient))
  :rule-classes :type-prescription)

(defthm fn-transfer-public-entry-budget-natp
  (natp (fn-transfer-public-entry-budget ambient))
  :rule-classes :type-prescription)

(defthm fn-transfer-scale-at-least-one
  (implies (and (natp value)
                (natp factor)
                (natp unit)
                (<= value unit)
                (<= 1 factor))
           (<= value (* factor unit)))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t)))

(defthm fn-transfer-scale-monotone
  (implies (and (natp smaller)
                (natp larger)
                (natp unit)
                (<= smaller larger))
           (<= (* smaller unit) (* larger unit)))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t)))

(defun fn-transfer-public-work-budget
  (state-size query-size max-chunks max-chunk declared-length)
  (+ (fn-transfer-public-state-validation-budget state-size)
     (* (nfix state-size) (1+ (* 2 (nfix query-size))))
     (* (nfix declared-length)
        (1+ (nfix max-chunks))
        (1+ (nfix max-chunk)))))

(defthm fn-transfer-public-state-validation-budget-natp
  (natp (fn-transfer-public-state-validation-budget ambient))
  :rule-classes :type-prescription)

(defthm fn-transfer-public-work-budget-natp
  (natp (fn-transfer-public-work-budget
         state-size query-size max-chunks max-chunk declared-length))
  :rule-classes :type-prescription)

(defthm fn-transfer-ranges-overlap-work-cadr-head-bound
  (implies (and (consp chunks)
                (natp ambient)
                (<= (fn-transfer-tree-size chunk) ambient)
                (<= (fn-transfer-tree-size chunks) ambient))
           (<= (cadr (fn-transfer-ranges-overlap-work
                      chunk (car chunks)))
               (fn-transfer-public-overlap-budget ambient)))
  :rule-classes :linear
  :hints (("Goal"
           :in-theory (enable fn-transfer-public-overlap-budget)
           :use ((:instance fn-transfer-ranges-overlap-work-cadr-ambient-bound
                            (left chunk)
                            (right (car chunks)))))))

(defthm fn-transfer-no-overlaps-work-ambient-bound
  (implies (and (natp ambient)
                (<= (fn-transfer-tree-size chunk) ambient)
                (<= (fn-transfer-tree-size chunks) ambient))
           (<= (fn-transfer-work-cost
                (fn-transfer-no-overlaps-work chunk chunks))
               (* (len chunks)
                  (fn-transfer-public-overlap-budget ambient))))
  :hints (("Goal"
           :induct (fn-transfer-no-overlaps-work chunk chunks)
           :in-theory (e/d (fn-transfer-no-overlaps-work
                             fn-transfer-work-cost)
                            (fn-transfer-ranges-overlap-work
                             fn-transfer-public-overlap-budget)))
          ("Subgoal *1/1''"
           :use ((:instance fn-transfer-scale-at-least-one
                            (value
                             (cadr (fn-transfer-ranges-overlap-work
                                    chunk (car chunks))))
                            (factor (len chunks))
                            (unit
                             (fn-transfer-public-overlap-budget ambient)))))))

(defthm fn-transfer-no-overlaps-work-cadr-ambient-bound
  (implies (and (natp ambient)
                (<= (fn-transfer-tree-size chunk) ambient)
                (<= (fn-transfer-tree-size chunks) ambient))
           (<= (cadr (fn-transfer-no-overlaps-work chunk chunks))
               (* (len chunks)
                  (fn-transfer-public-overlap-budget ambient))))
  :hints (("Goal"
           :in-theory (enable fn-transfer-work-cost)
           :use ((:instance fn-transfer-no-overlaps-work-ambient-bound)))))

(defthm fn-transfer-no-overlaps-work-cost-natp
  (natp (cadr (fn-transfer-no-overlaps-work chunk chunks)))
  :rule-classes :type-prescription
  :hints (("Goal"
           :induct (fn-transfer-no-overlaps-work chunk chunks)
           :in-theory (enable fn-transfer-no-overlaps-work))))

(defthm fn-transfer-chunk-work-cadr-head-step-bound
  (implies (and (consp chunks)
                (natp ambient)
                (<= (fn-transfer-tree-size chunks) ambient))
           (<= (cadr (fn-transfer-chunk-work
                      (car chunks) declared-length profile))
               (fn-transfer-public-chunk-list-step-budget ambient)))
  :rule-classes :linear
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-transfer-public-chunk-list-step-budget
                             fn-transfer-public-overlap-budget)
                            (fn-transfer-chunk-work
                             fn-transfer-chunk-work-cadr-ambient-bound))
           :use ((:instance fn-transfer-chunk-work-cadr-ambient-bound
                            (chunk (car chunks)))
                 (:instance fn-transfer-tree-size-car-bound
                            (x chunks))))))

(defthm fn-transfer-chunk-list-head-step-bound
  (implies (and (consp chunks)
                (natp ambient)
                (<= (fn-transfer-tree-size chunks) ambient))
           (<= (+ (cadr (fn-transfer-chunk-work
                         (car chunks) declared-length profile))
                  (cadr (fn-transfer-no-overlaps-work
                         (car chunks) (cdr chunks))))
               (fn-transfer-public-chunk-list-step-budget ambient)))
  :rule-classes :linear
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-transfer-public-chunk-list-step-budget
                             fn-transfer-public-overlap-budget)
                            (fn-transfer-chunk-work
                             fn-transfer-no-overlaps-work
                             fn-transfer-chunk-work-cadr-ambient-bound
                             fn-transfer-no-overlaps-work-cadr-ambient-bound))
           :use ((:instance fn-transfer-chunk-work-cadr-ambient-bound
                            (chunk (car chunks)))
                 (:instance fn-transfer-no-overlaps-work-cadr-ambient-bound
                            (chunk (car chunks))
                            (chunks (cdr chunks)))
                 (:instance fn-transfer-len-tree-size-bound
                            (x (cdr chunks)))
                 (:instance fn-transfer-tree-size-car-bound
                            (x chunks))
                 (:instance fn-transfer-tree-size-cdr-bound
                            (x chunks))
                 (:instance fn-transfer-scale-monotone
                            (smaller (len (cdr chunks)))
                            (larger ambient)
                            (unit (fn-transfer-public-overlap-budget
                                   ambient)))))))

(defthm fn-transfer-chunk-list-work-ambient-bound
  (implies (and (natp ambient)
                (<= (fn-transfer-tree-size chunks) ambient))
           (<= (fn-transfer-work-cost
                (fn-transfer-chunk-list-work
                 chunks declared-length profile))
               (* (len chunks)
                  (fn-transfer-public-chunk-list-step-budget ambient))))
  :hints (("Goal"
           :induct (fn-transfer-chunk-list-work
                    chunks declared-length profile)
           :in-theory (e/d (fn-transfer-chunk-list-work
                             fn-transfer-work-cost)
                            (fn-transfer-chunk-work
                             fn-transfer-no-overlaps-work
                             fn-transfer-public-chunk-list-step-budget)))
          ("Subgoal *1/1''"
           :use ((:instance fn-transfer-scale-at-least-one
                            (value
                             (cadr (fn-transfer-chunk-work
                                    (car chunks) declared-length profile)))
                            (factor (len chunks))
                            (unit
                             (fn-transfer-public-chunk-list-step-budget
                              ambient)))))
          ("Subgoal *1/2''"
           :use ((:instance fn-transfer-scale-at-least-one
                            (value
                             (+ (cadr (fn-transfer-chunk-work
                                       (car chunks)
                                       declared-length profile))
                                (cadr (fn-transfer-no-overlaps-work
                                       (car chunks) (cdr chunks)))))
                            (factor (len chunks))
                            (unit
                             (fn-transfer-public-chunk-list-step-budget
                              ambient)))))))

(defthm fn-transfer-chunk-list-work-cadr-ambient-bound
  (implies (and (natp ambient)
                (<= (fn-transfer-tree-size chunks) ambient))
           (<= (cadr (fn-transfer-chunk-list-work
                      chunks declared-length profile))
               (* (len chunks)
                  (fn-transfer-public-chunk-list-step-budget ambient))))
  :hints (("Goal"
           :in-theory (enable fn-transfer-work-cost)
           :use ((:instance fn-transfer-chunk-list-work-ambient-bound)))))

(defthm fn-transfer-chunk-list-work-cost-natp
  (natp (cadr (fn-transfer-chunk-list-work
               chunks declared-length profile)))
  :rule-classes :type-prescription
  :hints (("Goal"
           :induct (fn-transfer-chunk-list-work
                    chunks declared-length profile)
           :in-theory (e/d (fn-transfer-chunk-list-work)
                            (fn-transfer-chunk-work
                             fn-transfer-no-overlaps-work)))))

(defthm fn-transfer-entry-work-ambient-bound
  (implies (and (natp ambient)
                (<= (fn-transfer-tree-size entry) ambient))
           (<= (fn-transfer-work-cost
                (fn-transfer-entry-work entry profile))
               (fn-transfer-public-entry-budget ambient)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-transfer-entry-work
                             fn-transfer-work-cost
                             fn-transfer-public-entry-budget)
                            (fn-transfer-true-list-work
                             fn-transfer-len-work
                             fn-transfer-label-work
                             fn-transfer-at-most-work
                             fn-transfer-chunk-list-work))
           :use ((:instance fn-transfer-true-list-work-tree-bound (x entry))
                 (:instance fn-transfer-len-tree-size-bound (x entry))
                 (:instance fn-transfer-label-work-tree-bound
                            (label (fn-transfer-entry-label entry)))
                 (:instance fn-transfer-at-most-work-tree-bound
                            (xs (fn-transfer-entry-chunks entry))
                            (bound (fn-transfer-max-chunks profile)))
                 (:instance fn-transfer-chunk-list-work-ambient-bound
                            (chunks (fn-transfer-entry-chunks entry))
                            (declared-length
                             (fn-transfer-entry-length entry)))
                 (:instance fn-transfer-len-tree-size-bound
                            (x (fn-transfer-entry-chunks entry)))
                 (:instance fn-transfer-scale-monotone
                            (smaller
                             (len (fn-transfer-entry-chunks entry)))
                            (larger ambient)
                            (unit
                             (fn-transfer-public-chunk-list-step-budget
                              ambient)))))))

(defthm fn-transfer-entry-work-cadr-ambient-bound
  (implies (and (natp ambient)
                (<= (fn-transfer-tree-size entry) ambient))
           (<= (cadr (fn-transfer-entry-work entry profile))
               (fn-transfer-public-entry-budget ambient)))
  :hints (("Goal"
           :in-theory (enable fn-transfer-work-cost)
           :use ((:instance fn-transfer-entry-work-ambient-bound)))))

(defthm fn-transfer-entry-work-cost-natp
  (natp (cadr (fn-transfer-entry-work entry profile)))
  :rule-classes :type-prescription
  :hints (("Goal"
           :in-theory (e/d (fn-transfer-entry-work)
                            (fn-transfer-true-list-work
                             fn-transfer-len-work
                             fn-transfer-label-work
                             fn-transfer-at-most-work
                             fn-transfer-chunk-list-work)))))

(defthm fn-transfer-entry-work-cadr-head-ambient-bound
  (implies (and (consp entries)
                (natp ambient)
                (<= (fn-transfer-tree-size entries) ambient))
           (<= (cadr (fn-transfer-entry-work (car entries) profile))
               (fn-transfer-public-entry-budget ambient)))
  :rule-classes :linear
  :hints (("Goal"
           :in-theory (disable fn-transfer-entry-work
                               fn-transfer-entry-work-cadr-ambient-bound)
           :use ((:instance fn-transfer-entry-work-cadr-ambient-bound
                            (entry (car entries)))
                 (:instance fn-transfer-tree-size-car-bound
                            (x entries))))))

(defthm fn-transfer-entries-work-ambient-bound
  (implies (and (natp ambient)
                (<= (fn-transfer-tree-size entries) ambient))
           (<= (fn-transfer-work-cost
                (fn-transfer-entries-work entries profile))
               (* (len entries)
                  (fn-transfer-public-entry-budget ambient))))
  :hints (("Goal"
           :induct (fn-transfer-entries-work entries profile)
           :in-theory (e/d (fn-transfer-entries-work
                             fn-transfer-work-cost)
                            (fn-transfer-entry-work
                             fn-transfer-public-entry-budget)))
          ("Subgoal *1/1''"
           :use ((:instance fn-transfer-scale-at-least-one
                            (value
                             (cadr (fn-transfer-entry-work
                                    (car entries) profile)))
                            (factor (len entries))
                            (unit
                             (fn-transfer-public-entry-budget ambient)))))))

(defthm fn-transfer-equal-work-tree-bound
  (<= (fn-transfer-work-cost (fn-transfer-equal-work left right))
      (1+ (* 2 (fn-transfer-tree-size left))))
  :hints (("Goal"
           :induct (fn-transfer-equal-work left right)
           :in-theory (enable fn-transfer-equal-work
                              fn-transfer-work-cost
                              fn-transfer-tree-size))))

(defthm fn-transfer-equal-work-cadr-tree-bound
  (<= (cadr (fn-transfer-equal-work left right))
      (1+ (* 2 (fn-transfer-tree-size left))))
  :rule-classes :linear
  :hints (("Goal"
           :in-theory (enable fn-transfer-work-cost)
           :use ((:instance fn-transfer-equal-work-tree-bound)))))

(defthm fn-transfer-equal-work-cost-natp
  (natp (cadr (fn-transfer-equal-work left right)))
  :rule-classes :type-prescription
  :hints (("Goal"
           :induct (fn-transfer-equal-work left right)
           :in-theory (enable fn-transfer-equal-work))))

(defthm fn-transfer-label-absent-work-size-bound
  (<= (fn-transfer-work-cost
       (fn-transfer-label-absent-work label entries))
      (* (len entries)
         (1+ (* 2 (fn-transfer-tree-size label)))))
  :hints (("Goal"
           :induct (fn-transfer-label-absent-work label entries)
           :in-theory (e/d (fn-transfer-label-absent-work
                             fn-transfer-work-cost)
                            (fn-transfer-equal-work)))
          ("Subgoal *1/1''"
           :use ((:instance fn-transfer-scale-at-least-one
                            (value
                             (cadr (fn-transfer-equal-work
                                    label
                                    (fn-transfer-entry-label
                                     (car entries)))))
                            (factor (len entries))
                            (unit
                             (1+ (* 2
                                    (fn-transfer-tree-size label)))))))))

(defthm fn-transfer-label-absent-work-cadr-size-bound
  (<= (cadr (fn-transfer-label-absent-work label entries))
      (* (len entries)
         (1+ (* 2 (fn-transfer-tree-size label)))))
  :hints (("Goal"
           :in-theory (enable fn-transfer-work-cost)
           :use ((:instance fn-transfer-label-absent-work-size-bound)))))

(defthm fn-transfer-label-absent-work-cost-natp
  (natp (cadr (fn-transfer-label-absent-work label entries)))
  :rule-classes :type-prescription
  :hints (("Goal"
           :induct (fn-transfer-label-absent-work label entries)
           :in-theory (e/d (fn-transfer-label-absent-work)
                            (fn-transfer-equal-work)))))

(defthm fn-transfer-label-absent-work-cadr-head-ambient-bound
  (implies (and (consp entries)
                (natp ambient)
                (<= (fn-transfer-tree-size entries) ambient))
           (<= (cadr
                (fn-transfer-label-absent-work
                 (fn-transfer-entry-label (car entries))
                 (cdr entries)))
               (* (len (cdr entries))
                  (1+ (* 2 ambient)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable fn-transfer-label-absent-work
                               fn-transfer-label-absent-work-cadr-size-bound)
           :use ((:instance fn-transfer-label-absent-work-cadr-size-bound
                            (label (fn-transfer-entry-label (car entries)))
                            (entries (cdr entries)))
                 (:instance fn-transfer-tree-size-car-bound
                            (x entries))
                 (:instance fn-transfer-tree-size-car-bound
                            (x (car entries)))
                 (:instance fn-transfer-scale-monotone
                            (smaller
                             (1+ (* 2
                                    (fn-transfer-tree-size
                                     (fn-transfer-entry-label
                                      (car entries))))))
                            (larger (1+ (* 2 ambient)))
                            (unit (len (cdr entries))))))))

(defthm fn-transfer-label-absent-work-distinct-step-bound
  (implies (and (consp entries)
                (natp ambient)
                (<= (fn-transfer-tree-size entries) ambient))
           (<= (cadr
                (fn-transfer-label-absent-work
                 (fn-transfer-entry-label (car entries))
                 (cdr entries)))
               (* ambient (1+ (* 2 ambient)))))
  :rule-classes :linear
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable fn-transfer-label-absent-work)
           :use ((:instance
                  fn-transfer-label-absent-work-cadr-head-ambient-bound)
                 (:instance fn-transfer-len-tree-size-bound
                            (x (cdr entries)))
                 (:instance fn-transfer-tree-size-cdr-bound
                            (x entries))
                 (:instance fn-transfer-scale-monotone
                            (smaller (len (cdr entries)))
                            (larger ambient)
                            (unit (1+ (* 2 ambient))))))))

(defthm fn-transfer-distinct-labels-work-ambient-bound
  (implies (and (natp ambient)
                (<= (fn-transfer-tree-size entries) ambient))
           (<= (fn-transfer-work-cost
                (fn-transfer-distinct-labels-work entries))
               (* (len entries)
                  ambient
                  (1+ (* 2 ambient)))))
  :hints (("Goal"
           :induct (fn-transfer-distinct-labels-work entries)
           :in-theory (e/d (fn-transfer-distinct-labels-work
                             fn-transfer-work-cost)
                            (fn-transfer-label-absent-work)))
          ("Subgoal *1/1''"
           :use ((:instance fn-transfer-scale-at-least-one
                            (value
                             (cadr
                              (fn-transfer-label-absent-work
                               (fn-transfer-entry-label (car entries))
                               (cdr entries))))
                            (factor (len entries))
                            (unit
                             (* ambient (1+ (* 2 ambient)))))))
          ("Subgoal *1/2.1"
           :use ((:instance
                  fn-transfer-label-absent-work-distinct-step-bound)))))

(defthm fn-transfer-reserved-bytes-work-len-bound
  (equal (fn-transfer-work-cost
          (fn-transfer-reserved-bytes-work entries))
         (len entries))
  :hints (("Goal"
           :induct (fn-transfer-reserved-bytes-work entries)
           :in-theory (enable fn-transfer-reserved-bytes-work
                              fn-transfer-work-cost))))

(defthm fn-transfer-find-entry-work-size-bound
  (<= (fn-transfer-work-cost
       (fn-transfer-find-entry-work label entries))
      (* (len entries)
         (1+ (* 2 (fn-transfer-tree-size label)))))
  :hints (("Goal"
           :induct (fn-transfer-find-entry-work label entries)
           :in-theory (e/d (fn-transfer-find-entry-work
                             fn-transfer-work-cost)
                            (fn-transfer-equal-work)))))

(defthm fn-transfer-find-entry-work-cadr-size-bound
  (<= (cadr (fn-transfer-find-entry-work label entries))
      (* (len entries)
         (1+ (* 2 (fn-transfer-tree-size label)))))
  :hints (("Goal"
           :in-theory (enable fn-transfer-work-cost)
           :use ((:instance fn-transfer-find-entry-work-size-bound)))))

(defthm fn-transfer-state-work-ambient-bound
  (implies (and (natp ambient)
                (<= (fn-transfer-tree-size st) ambient))
           (<= (fn-transfer-work-cost (fn-transfer-state-work st))
               (fn-transfer-public-state-validation-budget ambient)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-transfer-state-work
                             fn-transfer-work-cost
                             fn-transfer-public-state-validation-budget)
                            (fn-transfer-true-list-work
                             fn-transfer-len-work
                             fn-transfer-profile-work
                             fn-transfer-at-most-work
                             fn-transfer-entries-work
                             fn-transfer-distinct-labels-work
                             fn-transfer-reserved-bytes-work))
           :use ((:instance fn-transfer-true-list-work-tree-bound (x st))
                 (:instance fn-transfer-len-tree-size-bound (x st))
                 (:instance fn-transfer-profile-work-tree-bound
                            (profile (fn-transfer-state-profile st)))
                 (:instance fn-transfer-at-most-work-tree-bound
                            (xs (fn-transfer-state-entries st))
                            (bound
                             (fn-transfer-max-reservations
                              (fn-transfer-state-profile st))))
                 (:instance fn-transfer-entries-work-ambient-bound
                            (entries (fn-transfer-state-entries st))
                            (profile (fn-transfer-state-profile st)))
                 (:instance fn-transfer-distinct-labels-work-ambient-bound
                            (entries (fn-transfer-state-entries st)))
                 (:instance fn-transfer-reserved-bytes-work-len-bound
                            (entries (fn-transfer-state-entries st)))
                 (:instance fn-transfer-len-tree-size-bound
                            (x (fn-transfer-state-entries st)))
                 (:instance fn-transfer-scale-monotone
                            (smaller
                             (len (fn-transfer-state-entries st)))
                            (larger ambient)
                            (unit (fn-transfer-public-entry-budget
                                   ambient)))
                 (:instance fn-transfer-scale-monotone
                            (smaller
                             (len (fn-transfer-state-entries st)))
                            (larger ambient)
                            (unit
                             (* ambient (1+ (* 2 ambient)))))))))

(defthm fn-transfer-octet-listp-implies-true-listp
  (implies (fn-transfer-octet-listp xs)
           (true-listp xs))
  :hints (("Goal"
           :induct (fn-transfer-octet-listp xs)
           :in-theory (enable fn-transfer-octet-listp))))

(defthm fn-transfer-chunk-inputp-length-bound
  (implies (and (fn-transfer-profilep profile)
                (fn-transfer-chunk-inputp octets profile))
           (and (true-listp octets)
                (<= (len octets) (fn-transfer-max-chunk profile))))
  :hints (("Goal"
           :in-theory (enable fn-transfer-chunk-inputp)
           :use ((:instance fn-transfer-at-mostp-is-length-bound
                            (xs octets)
                            (bound (fn-transfer-max-chunk profile)))))))

(defthm fn-transfer-chunk-listp-implies-length-profile
  (implies (and (fn-transfer-profilep profile)
                (fn-transfer-chunk-listp chunks declared-length profile))
           (fn-transfer-chunks-at-most-lengthp
            chunks (fn-transfer-max-chunk profile)))
  :hints (("Goal"
           :induct (fn-transfer-chunk-listp
                    chunks declared-length profile)
           :in-theory (enable fn-transfer-chunk-listp
                              fn-transfer-chunkp
                              fn-transfer-chunks-at-most-lengthp))))

(defthm fn-transfer-chunk-listp-implies-true-listp
  (implies (fn-transfer-chunk-listp chunks declared-length profile)
           (true-listp chunks))
  :hints (("Goal"
           :induct (fn-transfer-chunk-listp
                    chunks declared-length profile)
           :in-theory (enable fn-transfer-chunk-listp))))

(defthm fn-transfer-entryp-implies-missing-work-profile-bound
  (implies (and (fn-transfer-profilep profile)
                (fn-transfer-entryp entry profile))
           (<= (fn-transfer-work-cost
                (fn-transfer-missing-from-work
                 0
                 (fn-transfer-entry-length entry)
                 (fn-transfer-entry-chunks entry)))
               (* (fn-transfer-entry-length entry)
                  (1+ (fn-transfer-max-chunks profile))
                  (1+ (fn-transfer-max-chunk profile)))))
  :hints (("Goal"
           :nonlinearp t
           :in-theory (disable fn-transfer-missing-from-work)
           :use ((:instance fn-transfer-missing-work-cost-bound
                            (declared-length
                             (fn-transfer-entry-length entry))
                            (chunks (fn-transfer-entry-chunks entry))
                            (maximum (fn-transfer-max-chunk profile)))
                 (:instance fn-transfer-entryp-implies-chunk-listp)
                 (:instance fn-transfer-chunk-listp-implies-length-profile
                            (chunks (fn-transfer-entry-chunks entry))
                            (declared-length
                             (fn-transfer-entry-length entry)))
                 (:instance fn-transfer-chunk-listp-implies-true-listp
                            (chunks (fn-transfer-entry-chunks entry))
                            (declared-length
                             (fn-transfer-entry-length entry)))
                 (:instance fn-transfer-at-mostp-is-length-bound
                            (xs (fn-transfer-entry-chunks entry))
                            (bound (fn-transfer-max-chunks profile)))))))

(defun fn-transfer-public-bound-for (st label)
  (let* ((profile (fn-transfer-state-profile st))
         (entry (fn-transfer-find-entry
                 label (fn-transfer-state-entries st))))
    (fn-transfer-public-work-budget
     (fn-transfer-tree-size st)
     (fn-transfer-tree-size label)
     (fn-transfer-max-chunks profile)
     (fn-transfer-max-chunk profile)
     (fn-transfer-entry-length entry))))

(defthm fn-transfer-find-entry-work-public-bound
  (<= (fn-transfer-work-cost
       (fn-transfer-find-entry-work
        label (fn-transfer-state-entries st)))
      (* (fn-transfer-tree-size st)
         (1+ (* 2 (fn-transfer-tree-size label)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable fn-transfer-find-entry-work
                               fn-transfer-find-entry-work-size-bound
                               fn-transfer-find-entry-work-cadr-size-bound)
           :use ((:instance fn-transfer-find-entry-work-cadr-size-bound
                            (entries (fn-transfer-state-entries st)))
                 (:instance fn-transfer-len-tree-size-bound
                            (x (fn-transfer-state-entries st)))
                 (:instance fn-transfer-tree-size-cadr-bound (x st))
                 (:instance fn-transfer-scale-monotone
                            (smaller
                             (len (fn-transfer-state-entries st)))
                            (larger (fn-transfer-tree-size st))
                            (unit
                             (1+ (* 2
                                    (fn-transfer-tree-size label)))))))))

(defthm fn-transfer-statep-find-entry-missing-work-bound
  (implies
   (and (fn-transfer-statep st)
        (consp (fn-transfer-find-entry
                label (fn-transfer-state-entries st))))
   (<= (fn-transfer-work-cost
        (fn-transfer-missing-from-work
         0
         (fn-transfer-entry-length
          (fn-transfer-find-entry label (fn-transfer-state-entries st)))
         (fn-transfer-entry-chunks
          (fn-transfer-find-entry label (fn-transfer-state-entries st)))))
       (* (fn-transfer-entry-length
           (fn-transfer-find-entry label (fn-transfer-state-entries st)))
          (1+ (fn-transfer-max-chunks
               (fn-transfer-state-profile st)))
          (1+ (fn-transfer-max-chunk
               (fn-transfer-state-profile st))))))
  :hints (("Goal"
           :use ((:instance fn-transfer-entryp-implies-missing-work-profile-bound
                            (entry
                             (fn-transfer-find-entry
                              label (fn-transfer-state-entries st)))
                            (profile (fn-transfer-state-profile st)))
                 (:instance fn-transfer-statep-implies-profilep)
                 (:instance fn-transfer-statep-implies-entriesp)
                 (:instance fn-transfer-find-entry-is-entryp
                            (entries (fn-transfer-state-entries st))
                            (profile (fn-transfer-state-profile st)))))))

(defthm fn-transfer-state-work-public-bound
  (<= (fn-transfer-work-cost (fn-transfer-state-work st))
      (fn-transfer-public-bound-for st label))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-transfer-public-bound-for
                             fn-transfer-public-work-budget)
                            (fn-transfer-state-work
                             fn-transfer-public-state-validation-budget))
           :use ((:instance fn-transfer-state-work-ambient-bound
                            (ambient (fn-transfer-tree-size st)))))))

(defthm fn-transfer-state-find-work-public-bound
  (<= (+ (fn-transfer-work-cost (fn-transfer-state-work st))
         (fn-transfer-work-cost
          (fn-transfer-find-entry-work
           label (fn-transfer-state-entries st))))
      (fn-transfer-public-bound-for st label))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-transfer-public-bound-for
                             fn-transfer-public-work-budget)
                            (fn-transfer-state-work
                             fn-transfer-find-entry-work
                             fn-transfer-public-state-validation-budget))
           :use ((:instance fn-transfer-state-work-ambient-bound
                            (ambient (fn-transfer-tree-size st)))
                 (:instance fn-transfer-find-entry-work-public-bound)))))

(defthm fn-transfer-entryp-implies-numeric-length
  (implies (fn-transfer-entryp entry profile)
           (natp (fn-transfer-entry-length entry)))
  :hints (("Goal" :in-theory (enable fn-transfer-entryp))))

(defthm fn-transfer-profilep-implies-numeric-work-fields
  (implies (fn-transfer-profilep profile)
           (and (natp (fn-transfer-max-chunks profile))
                (natp (fn-transfer-max-chunk profile))))
  :hints (("Goal" :in-theory (enable fn-transfer-profilep))))

(defthm fn-transfer-statep-find-entry-numeric-fields
  (implies
   (and (fn-transfer-statep st)
        (consp (fn-transfer-find-entry
                label (fn-transfer-state-entries st))))
   (and (natp
         (fn-transfer-entry-length
          (fn-transfer-find-entry label (fn-transfer-state-entries st))))
        (natp (fn-transfer-max-chunks (fn-transfer-state-profile st)))
        (natp (fn-transfer-max-chunk (fn-transfer-state-profile st)))))
  :hints (("Goal"
           :in-theory (disable fn-transfer-statep
                               fn-transfer-entryp
                               fn-transfer-profilep)
           :use ((:instance fn-transfer-statep-implies-profilep)
                 (:instance fn-transfer-statep-implies-entriesp)
                 (:instance fn-transfer-find-entry-is-entryp
                            (entries (fn-transfer-state-entries st))
                            (profile (fn-transfer-state-profile st)))
                 (:instance fn-transfer-entryp-implies-numeric-length
                            (entry
                             (fn-transfer-find-entry
                              label (fn-transfer-state-entries st)))
                            (profile (fn-transfer-state-profile st)))
                 (:instance fn-transfer-profilep-implies-numeric-work-fields
                            (profile (fn-transfer-state-profile st)))))))

(defthm fn-transfer-state-find-missing-work-public-bound
  (implies
   (and (fn-transfer-statep st)
        (consp (fn-transfer-find-entry
                label (fn-transfer-state-entries st))))
   (<= (+ (fn-transfer-work-cost (fn-transfer-state-work st))
          (fn-transfer-work-cost
           (fn-transfer-find-entry-work
            label (fn-transfer-state-entries st)))
          (fn-transfer-work-cost
           (fn-transfer-missing-from-work
            0
            (fn-transfer-entry-length
             (fn-transfer-find-entry
              label (fn-transfer-state-entries st)))
            (fn-transfer-entry-chunks
             (fn-transfer-find-entry
              label (fn-transfer-state-entries st))))))
       (fn-transfer-public-bound-for st label)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-transfer-public-bound-for
                             fn-transfer-public-work-budget)
                            (fn-transfer-state-work
                             fn-transfer-find-entry-work
                             fn-transfer-missing-from-work
                             fn-transfer-public-state-validation-budget))
           :use ((:instance fn-transfer-state-work-ambient-bound
                            (ambient (fn-transfer-tree-size st)))
                 (:instance fn-transfer-find-entry-work-public-bound)
                 (:instance fn-transfer-statep-find-entry-missing-work-bound)
                 (:instance fn-transfer-statep-find-entry-numeric-fields)))))

(defthm fn-transfer-missing-ranges-work-public-bound
  (<= (fn-transfer-work-cost
       (fn-transfer-missing-ranges-work st label))
      (fn-transfer-public-bound-for st label))
  :hints (("Goal"
           :cases ((fn-transfer-statep st)
                   (consp (fn-transfer-find-entry
                           label (fn-transfer-state-entries st))))
           :in-theory
           (e/d (fn-transfer-missing-ranges-work
                  fn-transfer-work-cost
                  fn-transfer-state-work-value
                  fn-transfer-find-entry-work-value)
                (fn-transfer-state-work
                 fn-transfer-find-entry-work
                 fn-transfer-missing-from-work
                 fn-transfer-work-value
                 fn-transfer-public-bound-for))
           :use ((:instance fn-transfer-state-work-public-bound)
                 (:instance fn-transfer-state-find-work-public-bound)
                 (:instance
                  fn-transfer-state-find-missing-work-public-bound)))))
