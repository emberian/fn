; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-membership-run-frames")

(local (defthm fn-lbnt-u64-when-representable
 (implies (unsigned-byte-p 64 x) (equal (fn-lbc-u64 x) x))
 :hints (("Goal" :in-theory (enable fn-lbc-u64)))))

(local (defthm fn-lbnt-nfix-when-natural
 (implies (natp x) (equal (nfix x) x))
 :hints (("Goal" :in-theory (enable nfix)))))

(local (defthm fn-lbnt-pool-fit-head-and-tail
 (implies (and (consp texts) (fn-lbc-pool-spans-fitp texts nil offset))
  (and (unsigned-byte-p 64 offset)
       (unsigned-byte-p 64 (len (fn-record-string-octets (car texts))))
       (fn-lbc-pool-spans-fitp (cdr texts) nil
        (+ (nfix offset) (len (fn-record-string-octets (car texts)))))))
 :rule-classes ((:forward-chaining :trigger-terms ((fn-lbc-pool-spans-fitp texts nil offset))))
 :hints (("Goal" :expand ((fn-lbc-pool-spans-fitp texts nil offset))
  :in-theory (union-theories (theory 'ground-zero) '())))))

(defun-nx fn-lb-nov-span-bytes-corr (spans texts fn-lbc)
 (declare (xargs :measure (acl2-count texts)))
 (if (consp texts)
  (and (equal (fn-lbc-overview-pool-range (nfix (car spans)) (nfix (cadr spans)) fn-lbc)
              (true-list-fix (fn-record-string-octets (car texts))))
       (fn-lb-nov-span-bytes-corr (cddr spans) (cdr texts) fn-lbc))
  t))

(local (defthm fn-lbnt-pool-fit-tail-at-natural-offset
  (implies (and (natp offset) (consp texts) (fn-lbc-pool-spans-fitp texts nil offset))
   (fn-lbc-pool-spans-fitp (cdr texts) nil
    (+ offset (len (fn-record-string-octets (car texts))))))
  :hints (("Goal" :expand ((fn-lbc-pool-spans-fitp texts nil offset))
   :in-theory (union-theories (theory 'ground-zero) '(fn-lbnt-nfix-when-natural))))))

(defthm fn-lbc-nov-text-spans-read-appended-bytes
 (implies (fn-lbc-pool-spans-fitp texts nil (fn-lbc-overview-pool-count fn-lbc))
  (fn-lb-nov-span-bytes-corr
   (fn-lbc-nov-spans texts (fn-lbc-overview-pool-count fn-lbc)) texts
   (fn-lbc-append-nov-texts texts fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-append-nov-texts texts fn-lbc)
  :do-not '(preprocess)
  :in-theory (set-difference-theories
   (union-theories (theory 'ground-zero)
    '(fn-lbc-append-nov-texts fn-lbc-nov-spans fn-lb-nov-span-bytes-corr
      fn-lbnt-u64-when-representable fn-lbnt-nfix-when-natural fn-lbnt-pool-fit-head-and-tail fn-lbnt-pool-fit-tail-at-natural-offset
      fn-lbc-overview-pool-count-of-append fn-lbc-overview-pool-range-of-append-nov-texts-prefix
      fn-lbc-overview-pool-range-of-appended-bytes
      (:type-prescription fn-lbc-overview-pool-count-natural)))
   '((:definition nfix) (tau-system))))))
