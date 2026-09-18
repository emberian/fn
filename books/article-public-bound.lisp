; Complete public parser work bound, including malformed inputs.
(in-package "ACL2")
(include-book "article-public-work")
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (disable fn-aw-r fn-aw-v fn-aw-c fn-aw-charge)))
(defthm fn-aw-header-add-cost-natural
  (natp (fn-aw-c (fn-aw-header-add header-rev line)))
  :hints (("Goal" :in-theory (disable fn-aw-reverse fn-aw-append)))
  :rule-classes :type-prescription)
(defthm fn-aw-finish-fields-cost-natural
  (natp (fn-aw-c (fn-aw-finish-fields fields-rev current)))
  :hints (("Goal" :in-theory (disable fn-aw-reverse fn-aw-append)))
  :rule-classes :type-prescription)
; These linear rules retain the cost projections as opaque numeric terms.
(defthm fn-aw-new-field-cost-natural
  (natp (fn-aw-c (fn-aw-new-field line)))
  :hints (("Goal" :in-theory (disable fn-aw-split-colon fn-aw-name
                   fn-aw-header-bytes fn-aw-has-vchar fn-aw-downcase
                   fn-article-split-colon-aux fn-article-namep
                   fn-article-header-bytes-p fn-article-has-vcharp
                   fn-article-ascii-downcase fn-article-line-okp
                   fn-article-line-value fn-article-line-rest)))
  :rule-classes :type-prescription)
(defthm fn-aw-fold-line-cost-natural
  (natp (fn-aw-c (fn-aw-fold-line line)))
  :hints (("Goal" :in-theory (disable fn-aw-header-bytes fn-aw-has-vchar
                         fn-article-header-bytes-p fn-article-has-vcharp)))
  :rule-classes :type-prescription)
(local (defthm fn-aw-next-line-cost-linear
  (<= (fn-aw-c (fn-aw-next-line octets)) (+ 3 (* 2 (len octets))))
  :hints (("Goal" :by fn-aw-next-line-cost-bound))
  :rule-classes :linear))
(local (defthm fn-aw-body-cost-linear
  (<= (fn-aw-c (fn-aw-body xs)) (1+ (len xs)))
  :hints (("Goal" :by fn-aw-body-cost-bound))
  :rule-classes :linear))
(local (defthm fn-aw-new-field-cost-linear
  (<= (fn-aw-c (fn-aw-new-field line)) (+ 8 (* 6 (len line))))
  :hints (("Goal" :by fn-aw-new-field-cost-bound))
  :rule-classes :linear))
(local (defthm fn-aw-fold-line-cost-linear
  (<= (fn-aw-c (fn-aw-fold-line line)) (+ 3 (* 2 (len line))))
  :hints (("Goal" :by fn-aw-fold-line-cost-bound))
  :rule-classes :linear))
(local (defthm fn-aw-next-line-line-linear
  (<= (len (fn-article-line-value (fn-article-next-line octets))) (len octets))
  :hints (("Goal" :by fn-aw-next-line-line-bound)) :rule-classes :linear))
(local (defthm fn-aw-next-line-rest-linear
  (<= (len (fn-article-line-rest (fn-article-next-line octets))) (len octets))
  :hints (("Goal" :by fn-aw-next-line-rest-bound)) :rule-classes :linear))
(local (in-theory
 (disable fn-aw-next-line fn-article-next-line fn-aw-body fn-article-body-crlfp
          fn-aw-reverse fn-aw-finish-fields fn-article-finish-fields fn-aw-len
          fn-aw-fold-line fn-article-fold-linep fn-aw-add-fold fn-article-add-fold
          fn-aw-header-add fn-article-header-rev-add-line fn-aw-new-field
          fn-article-new-field fn-article-line-okp fn-article-line-value
          fn-article-line-rest fn-aw-current-size fn-aw-state-size
          fn-aw-budget fn-aw-budget-polynomial fn-aw-budget-monotone)))
(defthm fn-aw-budget-covers-local
  (implies (and (not (zp fuel)) (natp n) (natp s))
           (<= (* 32 (+ 1 n s)) (fn-aw-budget fuel n s)))
  :hints (("Goal" :expand ((fn-aw-budget fuel n s))
           :in-theory (disable fn-aw-budget fn-aw-budget-polynomial)))
  :rule-classes :linear)
(defthm fn-aw-budget-step
  (implies (and (not (zp fuel)) (natp n) (natp s) (natp n2) (natp s2)
                (<= n2 n) (<= s2 (+ s (* 2 n) 4)))
           (<= (+ (* 32 (+ 1 n s)) (fn-aw-budget (1- fuel) n2 s2))
               (fn-aw-budget fuel n s)))
  :hints (("Goal" :expand ((fn-aw-budget fuel n s))
           :use ((:instance fn-aw-budget-monotone (fuel (1- fuel))
                    (n n2) (s s2) (n2 n) (s2 (+ s (* 2 n) 4))))
           :in-theory (disable fn-aw-budget fn-aw-budget-polynomial
                               fn-aw-budget-monotone))))
(defthm fn-aw-parse-lines-cost-natural
  (natp (fn-aw-c (fn-aw-parse-lines octets lines-left header-bytes fields-rev current header-rev)))
  :hints (("Goal" :induct (fn-aw-parse-lines octets lines-left header-bytes fields-rev current header-rev)
           :in-theory (enable fn-aw-parse-lines)))
  :rule-classes :type-prescription)
(defthm fn-aw-parse-lines-cost-bound
  (implies (and (true-listp octets) (true-listp fields-rev) (true-listp header-rev))
           (<= (fn-aw-c (fn-aw-parse-lines octets lines-left header-bytes fields-rev current header-rev))
               (fn-aw-budget lines-left (len octets)
                             (fn-aw-state-size fields-rev current header-rev))))
  :hints (("Goal" :induct (fn-aw-parse-lines octets lines-left header-bytes fields-rev current header-rev)
            :in-theory (enable fn-aw-parse-lines fn-aw-state-size fn-aw-current-size))
          ("Subgoal *1/11" :use
            ((:instance fn-aw-budget-step (fuel lines-left) (n (len octets)) (s (fn-aw-state-size fields-rev current header-rev)) (n2 (len (fn-article-line-rest (fn-article-next-line octets)))) (s2 (fn-aw-state-size (if current (cons current fields-rev) fields-rev) (fn-article-line-value (fn-article-new-field (fn-article-line-value (fn-article-next-line octets)))) (fn-article-header-rev-add-line header-rev (fn-article-line-value (fn-article-next-line octets))))))
             (:instance fn-aw-new-state-growth (line (fn-article-line-value (fn-article-next-line octets)))))
             :in-theory (e/d (fn-aw-state-size fn-aw-current-size)
               (fn-aw-budget-step fn-aw-new-state-growth fn-aw-fold-state-growth
                fn-article-field-raw-lines fn-article-field-unfolded-value)))
          ("Subgoal *1/8" :use
            ((:instance fn-aw-budget-step (fuel lines-left) (n (len octets)) (s (fn-aw-state-size fields-rev current header-rev)) (n2 (len (fn-article-line-rest (fn-article-next-line octets)))) (s2 (fn-aw-state-size fields-rev (fn-article-add-fold current (fn-article-line-value (fn-article-next-line octets))) (fn-article-header-rev-add-line header-rev (fn-article-line-value (fn-article-next-line octets))))))
             (:instance fn-aw-fold-state-growth (line (fn-article-line-value (fn-article-next-line octets)))))
             :in-theory (e/d (fn-aw-state-size fn-aw-current-size)
               (fn-aw-budget-step fn-aw-new-state-growth fn-aw-fold-state-growth
                fn-article-field-raw-lines fn-article-field-unfolded-value)))
          ("Subgoal *1/1" :in-theory (enable fn-aw-budget))))

; Public preflight caps traversed input even for non-octet and improper objects.
(defthm fn-aw-parse-cost-natural
  (natp (fn-aw-c (fn-aw-parse octets)))
  :hints (("Goal" :in-theory (disable fn-aw-at-most fn-aw-octets
               fn-aw-parse-lines fn-cbor-at-mostp fn-cbor-octet-listp)))
  :rule-classes :type-prescription)

(defun fn-article-parse-work-budget (octets)
  (let ((n (min (len octets) *fn-article-max-octets*)))
    (+ 3 (* 2 n) (fn-aw-budget (1+ *fn-article-max-header-lines*) n 0))))

(defthm fn-article-parse-work-input-bound
  (<= (fn-aw-c (fn-aw-parse octets)) (fn-article-parse-work-budget octets))
  :hints (("Goal"
    :use ((:instance fn-aw-at-most-cost-input-bound (xs octets) (bound *fn-article-max-octets*))
          (:instance fn-aw-at-most-cost-bound (xs octets) (bound *fn-article-max-octets*))
          (:instance fn-aw-octets-cost-bound (xs octets))
          (:instance fn-aw-parse-lines-cost-bound
             (lines-left (1+ *fn-article-max-header-lines*)) (header-bytes 0)
             (fields-rev nil) (current nil) (header-rev nil)))
    :in-theory (e/d (fn-aw-parse fn-article-parse-work-budget
                      fn-aw-state-size fn-aw-current-size)
                    (fn-aw-at-most fn-aw-octets fn-aw-parse-lines
                     fn-cbor-at-mostp fn-cbor-octet-listp
                     fn-aw-at-most-cost-input-bound fn-aw-at-most-cost-bound
                     fn-aw-octets-cost-bound fn-aw-parse-lines-cost-bound)))))

(defthm fn-article-parse-work-profile-bound
  (<= (fn-aw-c (fn-aw-parse octets))
      (+ 3 (* 2 *fn-article-max-octets*)
         (fn-aw-budget (1+ *fn-article-max-header-lines*)
                       *fn-article-max-octets* 0)))
  :hints (("Goal"
    :use (fn-article-parse-work-input-bound
          (:instance fn-aw-budget-monotone
             (fuel (1+ *fn-article-max-header-lines*))
             (n (min (len octets) *fn-article-max-octets*)) (s 0)
             (n2 *fn-article-max-octets*) (s2 0)))
    :in-theory (e/d (fn-article-parse-work-budget)
                    (fn-aw-parse fn-article-parse-work-input-bound
                     fn-aw-budget-monotone)))))
