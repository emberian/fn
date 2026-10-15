; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-zero-storage")

(defun-nx fn-lb-slot-build-start (rows log fn-lbc) (let* ((fn-lbc (fn-lbc-clear-columns fn-lbc))
         (fn-lbc (fn-lbc-rebuild-rows rows log fn-lbc))
         (groups (fn-lbc-row-group-keys rows))
         (fn-lbc (fn-lbc-rebuild-summaries groups rows fn-lbc))
         (fn-lbc (update-fn-lbc-summary-groups groups fn-lbc))
         (fn-lbc (fn-lbc-reserve-slots (+ 1 (* 2 (len rows))) fn-lbc)))
    fn-lbc))

(defthm fn-lbc-open-rebuild-by-slot-start-definition
 (equal (fn-lbc-open-rebuild rows log fn-lbc)
        (fn-lbc-index-slots 0 (len rows) (fn-lb-slot-build-start rows log fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-open-rebuild fn-lb-slot-build-start)))))

(defthm fn-lb-slot-build-start-raw-store
 (equal (fn-lb-slot-store-model (fn-lb-slot-build-start rows log fn-lbc))
        (fn-lb-zero-slot-records (+ 1 (* 2 (len rows)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-slot-build-start fn-lb-slot-store-model-of-reserve-slots
 fn-lb-slot-store-model-of-summary-groups-update fn-lb-slot-store-model-of-rebuild-summaries
 fn-lb-slot-store-model-of-rebuild-rows fn-lb-slot-store-model-of-clear-columns binary-append true-listp natp)))))

(defthm fn-lb-slot-build-start-capacity
 (equal (fn-lbc-slot-count (fn-lb-slot-build-start rows log fn-lbc))
        (+ 1 (* 2 (len rows))))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lb-slot-build-start-raw-store))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-count-by-store fn-lb-slot-store-model fn-lb-zero-slot-records-length nfix)))))

(defthm fn-lb-slot-build-start-owner-keys
 (equal (fn-lbc-slot-escape-keys (fn-lb-slot-build-start rows log fn-lbc)) nil)
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-slot-build-start fn-lbc-slot-escape-keys-of-reserve-slots
 fn-lbc-slot-escape-keys-of-summary-groups-update fn-lbc-slot-escape-keys-of-rebuild-summaries
 fn-lbc-slot-escape-keys-of-rebuild-rows fn-lbc-slot-escape-keys-of-clear-columns)))))

(defthm fn-lb-slot-build-start-empty-owner-cell
 (equal (fn-lbc-escape key :msgid-slot (fn-lb-slot-build-start rows log fn-lbc)) nil)
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-slot-build-start fn-lbc-escape-of-reserve-slots fn-lbc-escape-of-summary-groups-update
 fn-lbc-escape-of-rebuild-summaries fn-lbc-slot-escape-empty-of-rebuild-rows fn-lbc-slot-escape-of-clear-columns)))))

(defthm fn-lb-slot-build-start-unindexed
 (fn-lb-unindexed-slotsp start n (fn-lb-slot-build-start rows log fn-lbc))
 :hints (("Goal" :induct (fn-lb-unindexed-slotsp start n (fn-lb-slot-build-start rows log fn-lbc))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-unindexed-slotsp fn-lb-slot-build-start-empty-owner-cell)))))

(defthm fn-lb-slot-build-start-zero-cells
 (fn-lbc-slot-cells-corr (make-list (+ 1 (* 2 (len rows))) :initial-element 0) 0
                        (fn-lb-slot-build-start rows log fn-lbc))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-slot-cells-corr-of-zero-records
 (fn-lbc (fn-lb-slot-build-start rows log fn-lbc)) (capacity (+ 1 (* 2 (len rows))))
 (n (+ 1 (* 2 (len rows))))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lb-slot-build-start-raw-store)))))
