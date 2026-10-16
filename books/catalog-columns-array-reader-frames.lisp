; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-msgid-readback")

(defthm fn-lbc-nov-at-frame-by-definition
 (implies (and (equal (nth 2 new) (nth 2 fn-lbc)) (equal (nth 7 new) (nth 7 fn-lbc))) (equal (fn-lbc-nov-at i new) (fn-lbc-nov-at i fn-lbc)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbc-nov-at fn-lbc-nov-field fn-lbc-nov-store fn-lbc-nov-text fn-lbc-overview-pool-range-by-store))
    '((:definition nfix) (:definition true-list-fix) (tau-system))))))

(defthm fn-lbc-nov-at-of-row-store-update
 (equal (fn-lbc-nov-at i (update-fn-lbc-row-store value fn-lbc))
        (fn-lbc-nov-at i fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-nov-at-frame-by-definition (new (update-fn-lbc-row-store value fn-lbc))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-nth-of-other-row-store-update-by-definition
     (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-nov-at-of-directory-store-update
 (equal (fn-lbc-nov-at i (update-fn-lbc-directory-store value fn-lbc))
        (fn-lbc-nov-at i fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-nov-at-frame-by-definition (new (update-fn-lbc-directory-store value fn-lbc))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-nth-of-other-directory-store-update-by-definition
     (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-nov-at-of-msgid-pool-append
 (equal (fn-lbc-nov-at i (fn-lbc-msgid-pool-append bytes fn-lbc)) (fn-lbc-nov-at i fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-nov-at-frame-by-definition (new (fn-lbc-msgid-pool-append bytes fn-lbc))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbwf-msgid-pool-append-field (:executable-counterpart natp)
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-lbc-nov-at-of-escape-store-put
 (equal (fn-lbc-nov-at i (fn-lbc-escape-store-put key cell fn-lbc)) (fn-lbc-nov-at i fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-nov-at-frame-by-definition (new (fn-lbc-escape-store-put key cell fn-lbc))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbwf-escape-store-put-field (:executable-counterpart natp)
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-lbc-membership-group-frame-by-definition
 (implies (and (equal (nth 2 new) (nth 2 fn-lbc)) (equal (nth 6 new) (nth 6 fn-lbc))) (equal (fn-lbc-membership-group i new) (fn-lbc-membership-group i fn-lbc)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbc-membership-group fn-lbc-membership-field fn-lbc-membership-store fn-lbc-overview-pool-range-by-store))
    '((:definition nfix) (:definition true-list-fix) (tau-system))))))

(defthm fn-lbc-membership-group-of-row-store-update
 (equal (fn-lbc-membership-group i (update-fn-lbc-row-store value fn-lbc))
        (fn-lbc-membership-group i fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-membership-group-frame-by-definition (new (update-fn-lbc-row-store value fn-lbc))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-nth-of-other-row-store-update-by-definition
     (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-membership-group-of-directory-store-update
 (equal (fn-lbc-membership-group i (update-fn-lbc-directory-store value fn-lbc))
        (fn-lbc-membership-group i fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-membership-group-frame-by-definition (new (update-fn-lbc-directory-store value fn-lbc))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-nth-of-other-directory-store-update-by-definition
     (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-membership-group-of-msgid-pool-append
 (equal (fn-lbc-membership-group i (fn-lbc-msgid-pool-append bytes fn-lbc)) (fn-lbc-membership-group i fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-membership-group-frame-by-definition (new (fn-lbc-msgid-pool-append bytes fn-lbc))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbwf-msgid-pool-append-field (:executable-counterpart natp)
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-lbc-membership-group-of-escape-store-put
 (equal (fn-lbc-membership-group i (fn-lbc-escape-store-put key cell fn-lbc)) (fn-lbc-membership-group i fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-membership-group-frame-by-definition (new (fn-lbc-escape-store-put key cell fn-lbc))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbwf-escape-store-put-field (:executable-counterpart natp)
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-lbc-membership-run-frame-by-definition
 (implies (and (equal (nth 2 new) (nth 2 fn-lbc)) (equal (nth 6 new) (nth 6 fn-lbc))) (equal (fn-lbc-membership-run start count numbersp new) (fn-lbc-membership-run start count numbersp fn-lbc)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-lbc-membership-run start count numbersp fn-lbc) :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero) '(fn-lbc-membership-run fn-lbc-membership-field fn-lbc-membership-store))
    '((:definition nfix) (:definition true-list-fix) (tau-system)))) ("Subgoal *1/2" :use ((:instance fn-lbc-membership-group-frame-by-definition (i start))))))

(defthm fn-lbc-membership-run-of-row-store-update
 (equal (fn-lbc-membership-run start count numbersp (update-fn-lbc-row-store value fn-lbc))
        (fn-lbc-membership-run start count numbersp fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-membership-run-frame-by-definition (new (update-fn-lbc-row-store value fn-lbc))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-nth-of-other-row-store-update-by-definition
     (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-membership-run-of-directory-store-update
 (equal (fn-lbc-membership-run start count numbersp (update-fn-lbc-directory-store value fn-lbc))
        (fn-lbc-membership-run start count numbersp fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-membership-run-frame-by-definition (new (update-fn-lbc-directory-store value fn-lbc))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-nth-of-other-directory-store-update-by-definition
     (:executable-counterpart natp) (:executable-counterpart equal))))))

(defthm fn-lbc-membership-run-of-msgid-pool-append
 (equal (fn-lbc-membership-run start count numbersp (fn-lbc-msgid-pool-append bytes fn-lbc)) (fn-lbc-membership-run start count numbersp fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-membership-run-frame-by-definition (new (fn-lbc-msgid-pool-append bytes fn-lbc))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbwf-msgid-pool-append-field (:executable-counterpart natp)
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-lbc-membership-run-of-escape-store-put
 (equal (fn-lbc-membership-run start count numbersp (fn-lbc-escape-store-put key cell fn-lbc)) (fn-lbc-membership-run start count numbersp fn-lbc))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-membership-run-frame-by-definition (new (fn-lbc-escape-store-put key cell fn-lbc))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbwf-escape-store-put-field (:executable-counterpart natp)
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))
