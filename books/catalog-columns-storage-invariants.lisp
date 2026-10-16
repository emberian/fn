; Structural representation types carried by native constructors.
; These predicates are proof-only; a served command never runs their walks.
(in-package "ACL2")
(include-book "catalog-columns-construction")

(defun-nx fn-lb-column-span-in-poolp (start length limit)
 (<= (+ (nfix start) (nfix length)) (nfix limit)))

(defun-nx fn-lb-column-nov-record-layoutp (record limit)
 (and (fn-lb-column-span-in-poolp (nth 2 record) (nth 3 record) limit)
       (fn-lb-column-span-in-poolp (nth 4 record) (nth 5 record) limit)
       (fn-lb-column-span-in-poolp (nth 6 record) (nth 7 record) limit)
       (fn-lb-column-span-in-poolp (nth 8 record) (nth 9 record) limit)
       (fn-lb-column-span-in-poolp (nth 10 record) (nth 11 record) limit)))

(defun-nx fn-lb-column-nov-records-layoutp (records limit)
 (declare (xargs :hints (("Goal" :in-theory (disable fn-lb-column-nov-record-layoutp)))))
 (if (consp records)
  (and (fn-lb-column-nov-record-layoutp (car records) limit)
       (fn-lb-column-nov-records-layoutp (cdr records) limit))
  t))

(defun-nx fn-lb-column-membership-record-layoutp (record limit)
 (and (fn-lb-column-span-in-poolp (nth 0 record) (nth 1 record) limit)))

(defun-nx fn-lb-column-membership-records-layoutp (records limit)
 (declare (xargs :hints (("Goal" :in-theory (disable fn-lb-column-membership-record-layoutp)))))
 (if (consp records)
  (and (fn-lb-column-membership-record-layoutp (car records) limit)
       (fn-lb-column-membership-records-layoutp (cdr records) limit))
  t))

(defun-nx fn-lb-column-row-layoutp (i fn-lbc)
 (and (alistp (fn-lbc-escape-store-get i fn-lbc))
      (fn-lb-column-span-in-poolp
        (fn-lbc-value i :msgid-offset fn-lbc) (fn-lbc-value i :msgid-length fn-lbc)
        (fn-lbc-msgid-pool-count fn-lbc))
      (or (fn-lbc-escape i :nov fn-lbc)
          (equal (fn-lbc-directory-value i :nov-length fn-lbc) 0)
          (and (natp (fn-lbc-directory-value i :nov-start fn-lbc))
               (< (fn-lbc-directory-value i :nov-start fn-lbc)
                  (fn-lbc-nov-record-count fn-lbc))))
      (or (fn-lbc-escape i :render-nov fn-lbc)
          (and (natp (fn-lbc-directory-value i :render-nov-start fn-lbc))
               (< (fn-lbc-directory-value i :render-nov-start fn-lbc)
                  (fn-lbc-nov-record-count fn-lbc))))
      (or (fn-lbc-escape i :groups fn-lbc)
          (fn-lb-column-span-in-poolp
            (fn-lbc-directory-value i :groups-start fn-lbc)
            (fn-lbc-directory-value i :groups-count fn-lbc)
            (fn-lbc-membership-record-count fn-lbc)))
      (or (fn-lbc-escape i :numbers fn-lbc)
          (fn-lb-column-span-in-poolp
            (fn-lbc-directory-value i :numbers-start fn-lbc)
            (fn-lbc-directory-value i :numbers-count fn-lbc)
            (fn-lbc-membership-record-count fn-lbc)))))

(defun-nx fn-lb-column-rows-layoutp (i fn-lbc)
 (declare (xargs :measure (nfix (- (fn-lbc-count fn-lbc) (nfix i)))
  :hints (("Goal" :in-theory (disable fn-lbc-count fn-lb-column-row-layoutp)))))
 (if (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (and (fn-lb-column-row-layoutp i fn-lbc)
       (fn-lb-column-rows-layoutp (+ 1 i) fn-lbc))
  t))

(defun-nx fn-lb-columns-storage-layoutp (fn-lbc)
 (and (fn-lb-columns-directory-alignedp fn-lbc)
      (fn-lb-column-nov-records-layoutp (nth *fn-lbc-nov-store* fn-lbc)
                                      (fn-lbc-overview-pool-count fn-lbc))
      (fn-lb-column-membership-records-layoutp (nth *fn-lbc-membership-store* fn-lbc)
                                             (fn-lbc-overview-pool-count fn-lbc))
      (fn-lb-column-rows-layoutp 0 fn-lbc)))

; BEGIN actual empty storage establishment
(defthm fn-lb-columns-storage-layoutp-of-clear-columns
  (fn-lb-columns-storage-layoutp (fn-lbc-clear-columns fn-lbc))
  :hints (("Goal" :do-not-induct t
   :in-theory
   (e/d (fn-lb-columns-storage-layoutp fn-lb-columns-directory-alignedp
         fn-lb-column-nov-records-layoutp fn-lb-column-membership-records-layoutp
         fn-lb-column-rows-layoutp fn-lbc-clear-columns fn-lbc-count)
        (fn-lbc-p fn-lb-column-row-layoutp)))))
