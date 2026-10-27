; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-log-append-views")

(local (defthm fn-lblfd-entry-in-append
 (implies (natp handle)
  (equal (fn-lb-log-model-row-entry-in sequence handle (append entries tail))
         (or (fn-lb-log-model-row-entry-in sequence handle entries)
             (fn-lb-log-model-row-entry-in sequence handle tail))))
 :hints (("Goal" :induct (fn-lb-log-model-row-entry-in sequence handle entries)
  :in-theory (union-theories (theory 'ground-zero) '(fn-lb-log-model-row-entry-in binary-append nth natp))))))

(local (defthm fn-lblfd-entry-in-next-singleton
 (equal (fn-lb-log-model-row-entry-in sequence handle (list (fn-lb-log-model-next-entry row payload segment)))
        (and (equal sequence (fn-record-sequence row)) (equal handle (fn-record-payload row))
             (fn-lb-log-model-next-entry row payload segment)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-log-model-row-entry-in fn-lb-log-next-entry-handle-by-definition
     fn-lb-log-next-entry-sequence-by-definition car-cons cdr-cons (:executable-counterpart consp)))))))

(local (defthm fn-lblfd-entry-in-appended-segment
 (implies (natp handle)
  (equal (fn-lb-log-model-row-entry-in sequence handle
           (caddr (fn-lb-log-model-append-to-segment row payload segment)))
         (or (fn-lb-log-model-row-entry-in sequence handle (caddr segment))
             (and (equal sequence (fn-record-sequence row)) (equal handle (fn-record-payload row))
                  (fn-lb-log-model-next-entry row payload segment)))))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-log-append-to-segment-directory-by-definition fn-lblfd-entry-in-append fn-lblfd-entry-in-next-singleton))))))

(local (defthm fn-lblfd-next-entry-present
 (consp (fn-lb-log-model-next-entry row payload segment)) :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-lb-log-model-next-entry car-cons cdr-cons (:executable-counterpart consp)))))))

(local (defthm fn-lblfd-next-entry-empty-segment
 (equal (fn-lb-log-model-next-entry row payload (list target nil nil))
        (fn-lb-log-model-next-entry row payload nil))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-lb-log-model-next-entry car-cons cdr-cons (:executable-counterpart car) (:executable-counterpart cdr)))))))

(local (defthm fn-lblfd-appended-segment-id
 (equal (car (fn-lb-log-model-append-to-segment row payload segment)) (car segment))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-lb-log-model-append-to-segment car-cons))))))

(local (defthm fn-lblfd-entry-in-nil
 (equal (fn-lb-log-model-row-entry-in sequence handle nil) nil)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-lb-log-model-row-entry-in (:executable-counterpart consp)))))))

(defthm fn-lb-log-append-fresh-row-entry
 (implies (and (natp (fn-record-payload row)) (not (fn-lb-log-model-row-entry row log)))
  (equal (fn-lb-log-model-row-entry row (fn-lb-log-model-append row payload target log))
         (fn-lb-log-model-next-entry row payload (fn-lb-log-model-segment target log))))
 :hints (("Goal" :induct (fn-lb-log-model-append row payload target log)
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lblfd-entry-in-nil fn-lb-log-model-append fn-lb-log-model-row-entry fn-lb-log-model-segment
     fn-lblfd-entry-in-appended-segment fn-lblfd-entry-in-next-singleton fn-lblfd-next-entry-empty-segment
     (:type-prescription fn-lblfd-next-entry-present))) '(nth)))))

(defthm fn-lb-log-append-fresh-row-segment
 (implies (and (natp (fn-record-payload row)) (not (fn-lb-log-model-row-entry row log)))
  (equal (fn-lb-log-model-row-segment row (fn-lb-log-model-append row payload target log)) target))
 :hints (("Goal" :induct (fn-lb-log-model-append row payload target log)
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lblfd-entry-in-nil fn-lb-log-model-append fn-lb-log-model-row-entry fn-lb-log-model-row-segment
     fn-lblfd-entry-in-appended-segment fn-lblfd-entry-in-next-singleton fn-lblfd-appended-segment-id
     (:type-prescription fn-lblfd-next-entry-present))) '(nth)))))
