; The generated placement drive cannot refuse a well-formed, opened plan.
(in-package "ACL2")
(include-book "history-image-place-invariant")
(include-book "history-image-plan-proof")
(local (include-book "arithmetic/top" :dir :system))

(defthm fn-his-remaining-lengths-step
 (implies (and (consp h) (nat-listp lens) (equal (len lens) 5))
  (equal (fn-hp-x-add
          (fn-hp-x-add lens (list 8 8 8 8 (len (fn-hp-pe (car h)))))
          (fn-hp-lens (cdr h) salt))
         (fn-hp-x-add lens (fn-hp-lens h salt))))
 :hints (("Goal" :in-theory (e/d (fn-hp-x-add fn-hp-pes-len len)
                                (fn-hp-lens fn-hp-pe fn-hp-pe-is-pad8)))))

(local
 (defthm fn-his-u64-list-nth
  (implies (and (fn-hp-u64-listp xs) (natp i) (< i (len xs)))
           (unsigned-byte-p 64 (nth i xs)))
  :hints (("Goal" :in-theory (enable nth len fn-hp-u64-listp)))))

(defthm fn-his-planned-row-word-fields
 (implies (and (consp h) (nat-listp lens) (equal (len lens) 5)
               (fn-hp-u64-listp (fn-hp-x-add lens (fn-hp-lens h salt))))
  (and (unsigned-byte-p 64 (nth 4 lens))
       (unsigned-byte-p 64 (len (fn-hp-pe (car h))))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-hp-u64-listp-of-x-add (a lens) (b (fn-hp-lens h salt)))
                (:instance fn-his-u64-list-nth (xs lens) (i 4)))
          :expand ((fn-hp-pes-len h))
          :in-theory (e/d (fn-hp-u64-listp)
                          (fn-hp-x-add fn-hp-u64-listp-of-x-add fn-his-u64-list-nth
                           len nth fn-hp-pes-len fn-hp-lens fn-hp-pe fn-hp-pe-is-pad8)))))

(defthm fn-his-planned-row-placement
 (implies (and (consp h) (nat-listp lens) (equal (len lens) 5)
               (adt-placement-ok starts (fn-hp-x-add lens (fn-hp-lens h salt)) np))
  (adt-placement-ok starts (fn-hp-x-add lens (list 8 8 8 8 (len (fn-hp-pe (car h))))) np))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-hp-placement-mono
                  (lens (fn-hp-x-add lens (list 8 8 8 8 (len (fn-hp-pe (car h))))))
                  (lens2 (fn-hp-x-add (fn-hp-x-add lens (list 8 8 8 8 (len (fn-hp-pe (car h)))))
                                    (fn-hp-lens (cdr h) salt))))
                (:instance fn-hp-caps-le-x-add
                  (lens (fn-hp-x-add lens (list 8 8 8 8 (len (fn-hp-pe (car h))))))
                  (d (fn-hp-lens (cdr h) salt))))
          :in-theory (disable adt-placement-ok fn-hp-caps-le fn-hp-x-add fn-hp-lens
                              fn-hp-pe fn-hp-pe-is-pad8 fn-his-canonical-lens))))

(defthm fn-his-place-row-accepts-planned
 (implies
  (and (consp h) (fn-hp-events-okp h) (fn-his-pwp pw)
       (fn-his-cursors-at (caddr pw) (cadr pw))
       (nat-listp starts) (equal (len starts) 5) (natp np)
       (fn-hp-u64-listp (fn-hp-x-add (cadr pw) (fn-hp-lens h salt)))
       (adt-placement-ok starts (fn-hp-x-add (cadr pw) (fn-hp-lens h salt)) np)
       (equal (pgs-w-length pgs-mem) (* 2048 np)) (equal (pgs-d-length pgs-mem) np))
  (equal (mv-nth 0 (fn-his-place-row (car h) salt pw starts np pgs-mem)) :ok))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-his-place-row-accepts-fitting-cursors (ev (car h)))
                (:instance fn-his-planned-row-word-fields (lens (cadr pw)))
                (:instance fn-his-planned-row-placement (lens (cadr pw))))
          :in-theory (e/d (fn-his-pwp fn-hp-events-okp)
                          (fn-his-place-row fn-hp-evp fn-his-cursors-at fn-hp-x-add fn-hp-lens
                           fn-hp-pe fn-hp-pe-is-pad8 fn-his-canonical-lens adt-placement-ok)))))

(local
 (defthm fn-his-add-zero5
  (implies (and (nat-listp lens) (equal (len lens) 5))
           (equal (fn-hp-x-add lens '(0 0 0 0 0)) lens))
  :hints (("Goal" :in-theory (enable fn-hp-x-add len)))))

(local
 (defthm fn-his-pwp-fields
  (implies (fn-his-pwp pw)
           (and (natp (car pw)) (nat-listp (cadr pw)) (equal (len (cadr pw)) 5)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-his-pwp)))))

(defthm fn-his-place-all-accepts-planned
 (implies
  (and (fn-hp-events-okp h) (fn-his-pwp pw)
       (fn-his-cursors-at (caddr pw) (cadr pw))
       (nat-listp starts) (equal (len starts) 5) (natp np)
       (fn-hp-u64-listp (fn-hp-x-add (cadr pw) (fn-hp-lens h salt)))
       (adt-placement-ok starts (fn-hp-x-add (cadr pw) (fn-hp-lens h salt)) np)
       (equal (pgs-w-length pgs-mem) (* 2048 np)) (equal (pgs-d-length pgs-mem) np))
  (let* ((res (fn-his-place-all h salt pw starts np pgs-mem))
         (out (mv-nth 1 res)))
   (and (equal (mv-nth 0 res) :ok)
        (equal (car out) (+ (car pw) (len h)))
        (equal (cadr out) (fn-hp-x-add (cadr pw) (fn-hp-lens h salt)))
        (fn-his-cursors-at (caddr out) (cadr out)))))
 :hints (("Goal" :induct (fn-his-place-all h salt pw starts np pgs-mem)
          :in-theory (disable fn-his-place-row fn-his-cursors-at fn-hp-x-add fn-hp-lens
                              fn-his-canonical-lens fn-hp-evp fn-hp-pe fn-hp-pe-is-pad8
                              fn-hp-u64-listp adt-placement-ok fn-his-pwp))
         ("Subgoal *1/2"
          :use ((:instance fn-his-place-row-preserves-cursors-at (ev (car h)))
                (:instance fn-his-planned-row-word-fields (lens (cadr pw)))
                (:instance fn-his-remaining-lengths-step (lens (cadr pw)))))))
