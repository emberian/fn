; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-row-allocation-counts")

(local (defthm fn-lbptr-row-count-natural
 (natp (fn-lbc-count fn-lbc)) :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-count fn-lbc-row-store fn-lbc-rowwords-count-is-len))))))

(defun-nx fn-lb-column-row-pointerp (i fn-lbc)
 (and
  (or (fn-lbc-escape i :nov fn-lbc)
      (equal (fn-lbc-directory-value i :nov-length fn-lbc) 0)
      (and (natp (fn-lbc-directory-value i :nov-start fn-lbc))
           (< (fn-lbc-directory-value i :nov-start fn-lbc) (fn-lbc-nov-record-count fn-lbc))))
  (or (fn-lbc-escape i :render-nov fn-lbc)
      (and (natp (fn-lbc-directory-value i :render-nov-start fn-lbc))
           (< (fn-lbc-directory-value i :render-nov-start fn-lbc) (fn-lbc-nov-record-count fn-lbc))))
  (or (fn-lbc-escape i :groups fn-lbc)
      (<= (+ (nfix (fn-lbc-directory-value i :groups-start fn-lbc))
             (nfix (fn-lbc-directory-value i :groups-count fn-lbc)))
          (fn-lbc-membership-record-count fn-lbc)))
  (or (fn-lbc-escape i :numbers fn-lbc)
      (<= (+ (nfix (fn-lbc-directory-value i :numbers-start fn-lbc))
             (nfix (fn-lbc-directory-value i :numbers-count fn-lbc)))
          (fn-lbc-membership-record-count fn-lbc)))
  (<= (+ (nfix (fn-lbc-value i :msgid-offset fn-lbc))
         (nfix (fn-lbc-value i :msgid-length fn-lbc)))
      (fn-lbc-msgid-pool-count fn-lbc))))

(defun-nx fn-lb-columns-row-pointersp (i fn-lbc)
 (declare (xargs :measure (nfix (- (fn-lbc-count fn-lbc) (nfix i)))
  :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(nfix (:type-prescription fn-lbptr-row-count-natural)))))))
 (if (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (and (fn-lb-column-row-pointerp i fn-lbc)
       (fn-lb-columns-row-pointersp (+ 1 i) fn-lbc)) t))

(defthm fn-lb-columns-row-pointersp-of-clear-columns
 (fn-lb-columns-row-pointersp 0 (fn-lbc-clear-columns fn-lbc))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lb-columns-row-pointersp fn-lbc-count-of-clear-columns)))))
