; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-membership-single-readback")

(defun-nx fn-lb-column-text-listp (texts)
 (declare (xargs :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (consp texts)
  (and (fn-lbc-text-smallp (car texts)) (fn-lb-column-text-listp (cdr texts)))
  (null texts)))

(local (defthm fn-lbmr-count-by-store
 (equal (fn-lbc-membership-record-count fn-lbc) (len (nth *fn-lbc-membership-store* fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-membership-record-count fn-lbc-membership-store fn-lbc-memberships-count-is-len))))))

(local (defthm fn-lbmr-nfix-when-natural
 (implies (natp x) (equal (nfix x) x))
 :hints (("Goal" :in-theory (enable nfix)))))

(local (defthm fn-lbmr-u64-when-representable
 (implies (unsigned-byte-p 64 x) (equal (fn-lbc-u64 x) x))
 :hints (("Goal" :in-theory (enable fn-lbc-u64)))))

(local (defthm fn-lbmr-pool-fit-head-and-tail
 (implies (and (natp offset) (consp items) (fn-lbc-pool-spans-fitp items numbersp offset))
  (and (unsigned-byte-p 64 offset)
       (unsigned-byte-p 64 (len (fn-record-string-octets (if numbersp (caar items) (car items)))))
       (fn-lbc-pool-spans-fitp (cdr items) numbersp
        (+ offset (len (fn-record-string-octets (if numbersp (caar items) (car items))))))))
 :hints (("Goal" :expand ((fn-lbc-pool-spans-fitp items numbersp offset))
  :in-theory (union-theories (theory 'ground-zero) '(fn-ag-car fn-lbmr-nfix-when-natural))))))

(local (defthm fn-lbmr-overview-count-of-membership-store-update
  (equal (fn-lbc-overview-pool-count (update-nth *fn-lbc-membership-store* value fn-lbc))
         (fn-lbc-overview-pool-count fn-lbc))
  :hints (("Goal" :do-not-induct t :in-theory
   (union-theories (theory 'ground-zero)
    '(fn-lbc-overview-pool-count fn-lbc-overview-store fn-lbc-overview-octets-count-is-len fn-dm-nth-update-nth nth))))))

(local (defthm fn-lbmr-len-append-one
  (equal (len (append xs (list x))) (+ 1 (len xs)))
  :hints (("Goal" :induct (len xs) :in-theory (enable binary-append len)))))

(defthm fn-lbc-membership-run-of-append-memberships-new
 (implies (and (fn-lb-columns-pool-layoutp fn-lbc)
               (if numbersp (fn-lbc-numbers-smallp items) (fn-lb-column-text-listp items))
               (fn-lbc-pool-spans-fitp items numbersp (fn-lbc-overview-pool-count fn-lbc)))
  (equal (fn-lbc-membership-run (fn-lbc-membership-record-count fn-lbc) (len items) numbersp
           (fn-lbc-append-memberships items numbersp fn-lbc)) items))
 :hints (("Goal" :induct (fn-lbc-append-memberships items numbersp fn-lbc)
   :do-not '(preprocess)
   :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
     '(fn-lb-columns-pool-layoutp fn-lbmr-overview-count-of-membership-store-update fn-lbmr-len-append-one fn-lbc-append-memberships fn-lbc-membership-run fn-lbc-numbers-smallp fn-lb-column-text-listp fn-lbmr-count-by-store fn-lbmr-nfix-when-natural fn-lbmr-u64-when-representable fn-lbc-membership-store update-fn-lbc-membership-store fn-lbc-memberships-append-is-append fn-dm-nth-update-nth fn-lbwf-overview-pool-append-field fn-lbc-membership-store-length-of-append-memberships fn-lbc-membership-store-nth-of-append-memberships-prefix fn-lbc-membership-field-number-by-definition fn-lbc-membership-group-of-append-memberships-prefix fn-lb-column-membership-record-layoutp-of-nth fn-lbc-overview-pool-count-of-append (:type-prescription fn-lbc-overview-pool-count-natural))) '((:definition nfix) (:definition true-list-fix) (:definition unsigned-byte-p) (:definition integer-range-p) (tau-system))))
  ("Subgoal *1/1" :use ((:instance fn-lbmr-pool-fit-head-and-tail (offset (fn-lbc-overview-pool-count fn-lbc))) (:instance fn-lbc-membership-group-of-append-single-new (group (if numbersp (caar items) (car items))) (number (if numbersp (cdar items) 0))) (:instance fn-lbc-membership-number-of-append-single-new (group (if numbersp (caar items) (car items))) (number (if numbersp (cdar items) 0))) (:instance fn-lb-columns-pool-layoutp-of-append-memberships (items (list (car items)))) (:instance fn-lb-column-membership-record-layoutp-of-nth (records (nth *fn-lbc-membership-store* (fn-lbc-append-memberships (list (car items)) numbersp fn-lbc))) (i (fn-lbc-membership-record-count fn-lbc)) (limit (fn-lbc-overview-pool-count (fn-lbc-append-memberships (list (car items)) numbersp fn-lbc))))))))
