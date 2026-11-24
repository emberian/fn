; An admitted overview has proper octet lists for its line and complete encoding.
(in-package "ACL2")
(include-book "runs-load-overview-proof")

(local
 (defthm fn2-ov-octets-at-tail
   (equal (fn-b3-octet-listp (append xs ys)) (and (fn-b3-octet-listp (true-list-fix xs)) (fn-b3-octet-listp ys)))))

(local
 (defthm fn2-ov-octets-in-fixed-append
   (equal (fn-b3-octet-listp (true-list-fix (append xs ys)))
          (and (fn-b3-octet-listp (true-list-fix xs)) (fn-b3-octet-listp (true-list-fix ys))))))

(local
 (defthm fn2-ov-fifth-input
   (equal (nth 4 row) (car (cddddr row)))
   :hints (("Goal" :expand ((:free (x) (nth 0 x)) (:free (x) (nth 1 x)) (:free (x) (nth 2 x))
                            (:free (x) (nth 3 x)) (:free (x) (nth 4 x)))))))

(defthmd fn2-ov-checked-row-contains-octets
   (implies (fn2-run-values-layoutp *fn2-overview-entry* row)
            (and (fn-b3-octet-listp (nth 4 row)) (fn-b3-octet-listp (fn2-layout-octets *fn2-overview-entry* row))
                 (true-listp (fn2-layout-octets *fn2-overview-entry* row))))
   :hints (("Goal" :use ((:instance fn2-run-overview-admitted-row (values row)))
            :in-theory (e/d (fn2-run-values-layoutp fn2-layout-octets fn2-layout-field-octets)
                            (fn2-layout-parse fn2-layout-varoctets fn-b3-octet-listp true-list-fix binary-append nth)))))
