; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-open-tables-correspondence")

(local (defthm fn-lbsdr-member-remove
 (iff (member-equal query (remove-equal slot xs))
      (and (not (equal query slot)) (member-equal query xs)))
 :hints (("Goal" :induct (len xs) :in-theory (union-theories (theory 'ground-zero)
 '(len member-equal remove-equal))))))

(local (defthm fn-lbsdr-slot-position-put
 (equal (assoc-eq :msgid-slot (put-assoc-eq :msgid-slot value cell)) (cons :msgid-slot value))
 :hints (("Goal" :induct (put-assoc-eq :msgid-slot value cell) :in-theory (enable put-assoc-eq assoc-eq)))))

(local (defthm fn-lbsdr-slot-position-remove
 (equal (assoc-eq :msgid-slot (remove-assoc-eq :msgid-slot cell)) nil)
 :hints (("Goal" :induct (remove-assoc-eq :msgid-slot cell) :in-theory (enable remove-assoc-equal assoc-eq)))))

(local (defthm fn-lbsdr-other-query-membership-after-drop
 (implies (not (equal query slot))
 (iff (member-equal query (cdr (fn-lbc-escape key :msgid-slot
            (mv-nth 1 (fn-lbc-slot-drop-owner slot keys fn-lbc)))))
      (member-equal query (cdr (fn-lbc-escape key :msgid-slot fn-lbc)))))
 :hints (("Goal" :induct (fn-lbc-slot-drop-owner slot keys fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-drop-owner fn-lbc-escape fn-lbc-escape-store-get-of-put mv-nth
 fn-lbsdr-member-remove fn-lbsdr-slot-position-put fn-lbsdr-slot-position-remove))))))

(defthm fn-lbc-slot-drop-owner-removes-membership
 (iff (member-equal slot (cdr (fn-lbc-escape key :msgid-slot
        (mv-nth 1 (fn-lbc-slot-drop-owner slot keys fn-lbc)))))
      (and (not (member-equal key keys))
           (member-equal slot (cdr (fn-lbc-escape key :msgid-slot fn-lbc)))))
 :hints (("Goal" :induct (fn-lbc-slot-drop-owner slot keys fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-drop-owner fn-lbc-escape fn-lbc-escape-store-get-of-put mv-nth member-equal
 fn-lbsdr-member-remove fn-lbsdr-slot-position-put fn-lbsdr-slot-position-remove)))))

(defthm fn-lbc-escaped-word-after-drop-other-observed
 (implies (not (equal query slot))
 (equal (fn-lbc-escaped-slot-word query observed
          (mv-nth 1 (fn-lbc-slot-drop-owner slot keys fn-lbc)))
        (fn-lbc-escaped-slot-word query observed fn-lbc)))
 :hints (("Goal" :induct (len observed) :in-theory (union-theories (theory 'ground-zero)
 '(len member-equal fn-lbc-escaped-slot-word)))
 ("Subgoal *1/1" :use ((:instance fn-lbsdr-other-query-membership-after-drop (key (car observed)))))))

(local (defthm fn-lbsdr-escaped-word-of-cell-update
 (implies (iff (member-equal query (cdr (assoc-eq :msgid-slot cell)))
               (member-equal query (cdr (fn-lbc-escape at :msgid-slot fn-lbc))))
 (equal (fn-lbc-escaped-slot-word query observed (fn-lbc-escape-store-put at cell fn-lbc))
        (fn-lbc-escaped-slot-word query observed fn-lbc)))
 :hints (("Goal" :induct (len observed) :in-theory (union-theories (theory 'ground-zero)
 '(len fn-lbc-escaped-slot-word fn-lbc-escape fn-lbc-escape-store-get-of-put member-equal))))))

(defthm fn-lbc-escape-cell-after-drop-unlisted-key
 (implies (not (member-equal key keys))
 (equal (fn-lbc-escape-store-get key (mv-nth 1 (fn-lbc-slot-drop-owner slot keys fn-lbc)))
        (fn-lbc-escape-store-get key fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-slot-drop-owner slot keys fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-drop-owner fn-lbc-escape-store-get-of-put member-equal mv-nth)))))

(defthm fn-lbc-slot-drop-keys-preserve-nonmember
 (implies (not (member-equal key keys))
 (not (member-equal key (mv-nth 0 (fn-lbc-slot-drop-owner slot keys fn-lbc)))))
 :hints (("Goal" :induct (fn-lbc-slot-drop-owner slot keys fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-drop-owner member-equal mv-nth)))))

(local (defthm fn-lbsdr-dropped-membership-cleared-in-kept-keys
 (implies (member-equal key (mv-nth 0 (fn-lbc-slot-drop-owner slot keys fn-lbc)))
 (not (member-equal slot (cdr (fn-lbc-escape key :msgid-slot
            (mv-nth 1 (fn-lbc-slot-drop-owner slot keys fn-lbc)))))))
 :hints (("Goal" :do-not-induct t :cases ((member-equal key keys))
 :use ((:instance fn-lbc-slot-drop-keys-preserve-nonmember)
       (:instance fn-lbc-slot-drop-owner-removes-membership))
 :in-theory (theory 'ground-zero)))))

(local (defthm fn-lbsdr-slot-position-by-definition
 (equal (assoc-eq :msgid-slot (fn-lbc-escape-store-get key fn-lbc))
        (fn-lbc-escape key :msgid-slot fn-lbc))
 :hints (("Goal" :in-theory (enable fn-lbc-escape)))))

(local (defthm fn-lbsdr-escaped-target-zero
 (implies (subsetp-equal observed keys)
 (equal (fn-lbc-escaped-slot-word slot observed
          (mv-nth 1 (fn-lbc-slot-drop-owner slot keys fn-lbc))) 0))
 :hints (("Goal" :induct (len observed) :in-theory (union-theories (theory 'ground-zero)
 '(len subsetp-equal member-equal fn-lbc-escaped-slot-word fn-lbc-slot-drop-owner-removes-membership))))))

(local (defthm fn-lbsdr-other-query-not-in-emptied
 (implies (and (not (remove-equal slot xs)) (not (equal query slot)))
 (not (member-equal query xs)))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbsdr-member-remove))
 :in-theory (union-theories (theory 'ground-zero) '(member-equal))))))

(local (defthm fn-lbsdr-other-query-forces-position-after-drop
 (implies (and (not (equal query slot))
              (member-equal query (cdr (fn-lbc-escape key :msgid-slot fn-lbc))))
 (fn-lbc-escape key :msgid-slot (mv-nth 1 (fn-lbc-slot-drop-owner slot keys fn-lbc))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbsdr-other-query-membership-after-drop))
 :in-theory (union-theories (theory 'ground-zero) '(member-equal))))))

(local (defthm fn-lbsir-escaped-word-of-unlisted-cell-put
 (implies (not (member-equal at keys))
 (equal (fn-lbc-escaped-slot-word query keys (fn-lbc-escape-store-put at cell fn-lbc))
        (fn-lbc-escaped-slot-word query keys fn-lbc)))
 :hints (("Goal" :induct (len keys) :in-theory (union-theories (theory 'ground-zero)
 '(len member-equal fn-lbc-escaped-slot-word fn-lbc-escape fn-lbc-escape-store-get-of-put))))))

(defthm fn-lbc-escaped-word-of-fresh-owner-insertion
 (implies (and (not (member-equal at keys))
               (not (fn-lbc-escape at :msgid-slot fn-lbc)))
 (equal (fn-lbc-escaped-slot-word query (cons at keys)
         (fn-lbc-escape-store-put at
           (put-assoc-eq :msgid-slot (list slot) (fn-lbc-escape-store-get at fn-lbc)) fn-lbc))
        (if (equal query slot) (+ 1 (nfix at)) (fn-lbc-escaped-slot-word query keys fn-lbc))))
 :hints (("Goal" :do-not-induct t
 :expand ((fn-lbc-escaped-slot-word query (cons at keys)
         (fn-lbc-escape-store-put at
           (put-assoc-eq :msgid-slot (list slot) (fn-lbc-escape-store-get at fn-lbc)) fn-lbc)))
 :in-theory (union-theories (theory 'ground-zero)
 '(member-equal fn-lbc-escape fn-lbc-escape-store-get-of-put
 fn-lbsdr-slot-position-put fn-lbsir-escaped-word-of-unlisted-cell-put)))))

(defthm fn-lbc-escaped-word-after-drop-other
 (implies (not (equal query slot)) (equal (fn-lbc-escaped-slot-word query
           (mv-nth 0 (fn-lbc-slot-drop-owner slot keys fn-lbc))
           (mv-nth 1 (fn-lbc-slot-drop-owner slot keys fn-lbc)))
        (fn-lbc-escaped-slot-word query keys fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-slot-drop-owner slot keys fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-drop-owner fn-lbc-escaped-slot-word mv-nth member-equal
 fn-lbsdr-member-remove fn-lbsdr-slot-position-put fn-lbsdr-slot-position-remove
 fn-lbsdr-escaped-word-of-cell-update fn-lbc-escaped-word-after-drop-other-observed
 fn-lbsdr-other-query-membership-after-drop fn-lbc-slot-drop-owner-removes-membership
 fn-lbsdr-slot-position-by-definition fn-lbc-escape-store-get-of-put fn-lbsdr-other-query-not-in-emptied fn-lbsdr-other-query-forces-position-after-drop)))))

(local (defthm fn-lbsdr-member-cons
 (iff (member-equal query (cons key rest)) (or (equal query key) (member-equal query rest)))
 :hints (("Goal" :in-theory (enable member-equal)))))

(local (defthm fn-lbsdr-subset-cons
 (implies (subsetp-equal xs ys) (subsetp-equal xs (cons item ys)))
 :hints (("Goal" :induct (len xs) :in-theory (union-theories (theory 'ground-zero)
 '(len subsetp-equal fn-lbsdr-member-cons))))))

(local (defthm fn-lbsdr-member-head
 (implies (consp xs) (member-equal (car xs) xs))
 :hints (("Goal" :in-theory (enable member-equal)))))

(local (defthm fn-lbsdr-subset-self
 (subsetp-equal xs xs)
 :hints (("Goal" :induct (len xs) :in-theory (union-theories (theory 'ground-zero)
 '(len subsetp-equal fn-lbsdr-subset-cons fn-lbsdr-member-head))))))

(local (defthm fn-lbsdr-slot-drop-keys-subset
 (subsetp-equal (mv-nth 0 (fn-lbc-slot-drop-owner slot keys fn-lbc)) keys)
 :hints (("Goal" :induct (fn-lbc-slot-drop-owner slot keys fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-slot-drop-owner mv-nth subsetp-equal fn-lbsdr-member-cons fn-lbsdr-subset-cons fn-lbsdr-member-head))))))

(defthm fn-lbc-escaped-word-after-drop-target
 (equal (fn-lbc-escaped-slot-word slot
          (mv-nth 0 (fn-lbc-slot-drop-owner slot keys fn-lbc))
          (mv-nth 1 (fn-lbc-slot-drop-owner slot keys fn-lbc))) 0)
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbsdr-escaped-target-zero
       (observed (mv-nth 0 (fn-lbc-slot-drop-owner slot keys fn-lbc)))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbsdr-slot-drop-keys-subset)))))

(defthm fn-lbc-escaped-word-after-drop
 (equal (fn-lbc-escaped-slot-word query
           (mv-nth 0 (fn-lbc-slot-drop-owner slot keys fn-lbc))
           (mv-nth 1 (fn-lbc-slot-drop-owner slot keys fn-lbc)))
        (if (equal query slot) 0 (fn-lbc-escaped-slot-word query keys fn-lbc)))
 :hints (("Goal" :do-not-induct t :cases ((equal query slot))
 :use ((:instance fn-lbc-escaped-word-after-drop-other)
 (:instance fn-lbc-escaped-word-after-drop-target))
 :in-theory (theory 'ground-zero))))
