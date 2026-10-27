; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-log-new-range-readback")

(local (defthm fn-lblrl-offset-lower-bound
 (implies (and (natp lower) (natp upper) (fn-lb-log-entries-layoutp entries lower upper)
               (member-equal e entries))
  (and (natp (nth 3 e)) (<= lower (nth 3 e))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lb-log-entries-layoutp entries lower upper)
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lb-log-entries-layoutp member-equal)) '(nth true-listp))))))

(defthm fn-lb-log-range-entry-of-layout-member
 (implies (and (natp lower) (natp upper) (fn-lb-log-entries-layoutp entries lower upper)
               (member-equal e entries))
  (equal (fn-lb-log-model-range-entry (nth 3 e) entries) e))
 :hints (("Goal" :induct (fn-lb-log-entries-layoutp entries lower upper)
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lb-log-entries-layoutp fn-lb-log-model-range-entry member-equal)) '(nth true-listp)))
  ("Subgoal *1/1" :use ((:instance fn-lblrl-offset-lower-bound
    (entries (cdr entries)) (lower (+ (nth 1 (car entries)) (nth 2 (car entries)) 32)))))))

(local (defthm fn-lblrl-row-segment-member
 (implies (fn-lb-log-model-row-entry row log)
  (member-equal (fn-lb-log-model-row-segment row log) (fn-lb-log-layout-ids log)))
 :hints (("Goal" :induct (fn-lb-log-model-row-entry row log)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lb-log-model-row-entry fn-lb-log-model-row-segment fn-lb-log-layout-ids member-equal))))))

(defthm fn-lb-log-range-entry-of-row-locator
 (implies (and (fn-lb-log-layoutp log) (fn-lb-log-model-row-entry row log))
  (equal (fn-lb-log-model-range-entry (nth 3 (fn-lb-log-model-row-entry row log))
    (caddr (fn-lb-log-model-segment (fn-lb-log-model-row-segment row log) log)))
   (fn-lb-log-model-row-entry row log)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lblrl-row-segment-member)
       (:instance fn-lb-log-selected-segment-has-layout (seg (fn-lb-log-model-row-segment row log)))
       (:instance fn-lb-log-row-entry-is-in-selected-segment)
       (:instance fn-lb-log-row-entry-in-is-member
        (sequence (fn-record-sequence row)) (handle (fn-record-payload row))
        (entries (caddr (fn-lb-log-model-segment (fn-lb-log-model-row-segment row log) log))))
       (:instance fn-lb-log-range-entry-of-layout-member
        (entries (caddr (fn-lb-log-model-segment (fn-lb-log-model-row-segment row log) log)))
        (e (fn-lb-log-model-row-entry row log)) (lower 0)
        (upper (len (cadr (fn-lb-log-model-segment (fn-lb-log-model-row-segment row log) log))))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-segment-layoutp)))))

(defthm fn-lb-log-fresh-append-binds-homes
 (implies (and (natp (fn-record-payload row)) (not (fn-lb-log-model-row-entry row log)))
 (equal (nth 7 (fn-lb-log-model-row-entry row (fn-lb-log-model-append row payload target log))) (fn-lb-log-model-homes row)))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero) '(fn-lb-log-append-fresh-row-entry fn-lb-log-next-entry-homes-by-definition)))))

(defthm fn-lb-log-fresh-append-binds-payload
 (implies (and (natp (fn-record-payload row)) (not (fn-lb-log-model-row-entry row log)))
 (equal (fn-lb-log-payload row (fn-lb-log-model-append row payload target log)) payload))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero) '(fn-lb-log-append-fresh-row-entry fn-lb-log-payload fn-lb-log-next-entry-payload-by-definition)))))
