; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-index-frames")

(defthm fn-lbc-nov-at-of-slot-put
 (equal (fn-lbc-nov-at read-j (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lbc-nov-at read-j fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-nov-at-frame-by-definition (new (fn-lbc-slot-put slot ordinal fn-lbc)) (i read-j)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbwf-slot-put-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-lbc-membership-run-of-slot-put
 (equal (fn-lbc-membership-run start count numbersp (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lbc-membership-run start count numbersp fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-membership-run-frame-by-definition (new (fn-lbc-slot-put slot ordinal fn-lbc)) ))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbwf-slot-put-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-lbc-msgid-pool-range-of-slot-put
 (implies (and (natp off) (natp n))
  (equal (fn-lbc-msgid-pool-range off n (fn-lbc-slot-put slot ordinal fn-lbc)) (fn-lbc-msgid-pool-range off n fn-lbc)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-msgid-pool-range-of-same-model (new (fn-lbc-slot-put slot ordinal fn-lbc))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid-pool-model-frame-of-slot-put)))))

(defthm fn-lbc-nov-at-of-slot-insert
 (equal (fn-lbc-nov-at read-j (fn-lbc-slot-insert j slot fuel fn-lbc)) (fn-lbc-nov-at read-j fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-nov-at-frame-by-definition (new (fn-lbc-slot-insert j slot fuel fn-lbc)) (i read-j)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbwf-slot-insert-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-lbc-membership-run-of-slot-insert
 (equal (fn-lbc-membership-run start count numbersp (fn-lbc-slot-insert j slot fuel fn-lbc)) (fn-lbc-membership-run start count numbersp fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-membership-run-frame-by-definition (new (fn-lbc-slot-insert j slot fuel fn-lbc)) ))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbwf-slot-insert-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-lbc-msgid-pool-range-of-slot-insert
 (implies (and (natp off) (natp n))
  (equal (fn-lbc-msgid-pool-range off n (fn-lbc-slot-insert j slot fuel fn-lbc)) (fn-lbc-msgid-pool-range off n fn-lbc)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-msgid-pool-range-of-same-model (new (fn-lbc-slot-insert j slot fuel fn-lbc))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid-pool-model-frame-of-slot-insert)))))

(defthm fn-lbc-nov-at-of-index-slots
 (equal (fn-lbc-nov-at read-j (fn-lbc-index-slots j end fn-lbc)) (fn-lbc-nov-at read-j fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-nov-at-frame-by-definition (new (fn-lbc-index-slots j end fn-lbc)) (i read-j)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbwf-index-slots-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-lbc-membership-run-of-index-slots
 (equal (fn-lbc-membership-run start count numbersp (fn-lbc-index-slots j end fn-lbc)) (fn-lbc-membership-run start count numbersp fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-membership-run-frame-by-definition (new (fn-lbc-index-slots j end fn-lbc)) ))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbwf-index-slots-field (:executable-counterpart natp) (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-lbc-msgid-pool-range-of-index-slots
 (implies (and (natp off) (natp n))
  (equal (fn-lbc-msgid-pool-range off n (fn-lbc-index-slots j end fn-lbc)) (fn-lbc-msgid-pool-range off n fn-lbc)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-msgid-pool-range-of-same-model (new (fn-lbc-index-slots j end fn-lbc))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid-pool-model-frame-of-index-slots)))))
