; The length-only pass agrees with the canonical image's region lengths.
(in-package "ACL2")
(include-book "history-image-plan")
(local (include-book "arithmetic/top" :dir :system))

(defthm fn-his-plan-row-spec
 (equal (fn-his-plan-row ev plan)
  (if (fn-hp-evp ev)
      (list nil (list (+ 1 (nfix (car plan)))
                      (fn-hp-x-add (cadr plan)
                                   (list 8 8 8 8 (len (fn-hp-pe ev))))))
    (list '(:refused :event) plan)))
 :hints (("Goal" :use fn-hp-x-rowlen-spec
          :in-theory (e/d (fn-his-plan-row fn-hp-pe)
                          (fn-hp-x-rowlen fn-hp-evp fn-scc-encode
                           fn-scc-encode-is-program fn-hp-pad8 fn-hp-len-pad8
                           fn-hp-x-add fn-hp-pe-is-pad8)))))

(defthm fn-his-plan-all-verdict
 (equal (mv-nth 0 (fn-his-plan-all h plan))
        (if (fn-hp-events-okp h) nil '(:refused :event)))
 :hints (("Goal" :induct (fn-his-plan-all h plan)
          :in-theory (disable fn-his-plan-row fn-hp-evp fn-hp-pe fn-hp-x-add))))

(defthm fn-his-plan-all-count
 (implies (and (fn-hp-events-okp h) (fn-his-planp plan))
  (equal (car (mv-nth 1 (fn-his-plan-all h plan))) (+ (car plan) (len h))))
 :hints (("Goal" :induct (fn-his-plan-all h plan)
          :in-theory (e/d (fn-his-planp len)
                          (fn-his-plan-row fn-hp-evp fn-hp-pe fn-hp-x-add)))))

(defthm fn-his-canonical-lens
 (equal (fn-hp-lens h salt)
        (list (* 8 (len h)) (* 8 (len h)) (* 8 (len h)) (* 8 (len h))
              (fn-hp-pes-len h)))
 :hints (("Goal" :do-not-induct t
          :use ((:instance adt-len-cars-of-transpose (r 0) (m 4) (rows (adt-rows-cells *fn-hp-schema* (fn-hp-rows h salt) 0)))
                (:instance adt-len-cars-of-transpose (r 1) (m 4) (rows (adt-rows-cells *fn-hp-schema* (fn-hp-rows h salt) 0)))
                (:instance adt-len-cars-of-transpose (r 2) (m 4) (rows (adt-rows-cells *fn-hp-schema* (fn-hp-rows h salt) 0)))
                (:instance adt-len-cars-of-transpose (r 3) (m 4) (rows (adt-rows-cells *fn-hp-schema* (fn-hp-rows h salt) 0))))
          :in-theory (e/d (fn-hp-lens fn-hp-regs adt-regs adt-lens adt-col-regs adt-transpose)
                          (fn-hp-rows fn-hp-row fn-hp-pe fn-hp-pes fn-hp-pes-len
                           adt-rows-cells adt-rows-pool adt-le-list adt-len-cars-of-transpose)))))

(defthm fn-his-add-lengths-associative
 (implies (and (nat-listp a) (nat-listp b) (nat-listp c)
               (equal (len a) (len b)) (equal (len b) (len c)))
  (equal (fn-hp-x-add (fn-hp-x-add a b) c) (fn-hp-x-add a (fn-hp-x-add b c))))
 :hints (("Goal" :in-theory (enable fn-hp-x-add len))))

(defthm fn-his-plan-all-lengths
 (implies (and (fn-hp-events-okp h) (fn-his-planp plan))
  (equal (cadr (mv-nth 1 (fn-his-plan-all h plan)))
         (fn-hp-x-add (cadr plan)
                      (list (* 8 (len h)) (* 8 (len h)) (* 8 (len h)) (* 8 (len h))
                            (fn-hp-pes-len h)))))
 :hints (("Goal" :induct (fn-his-plan-all h plan)
          :in-theory (e/d (fn-his-planp len fn-hp-pes-len fn-hp-x-add)
                          (fn-his-plan-row fn-hp-evp fn-hp-pe)))))

(local
 (defthm fn-his-plan-all-pair
  (equal (fn-his-plan-all h plan)
         (list (mv-nth 0 (fn-his-plan-all h plan)) (mv-nth 1 (fn-his-plan-all h plan))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-his-plan-all h plan)
           :in-theory (disable fn-his-plan-row fn-his-plan-row-spec)))))

(local
 (defthm fn-his-planp-reconstruct
  (implies (fn-his-planp plan)
           (equal (list (car plan) (cadr plan)) plan))
  :hints (("Goal" :in-theory (e/d (fn-his-planp) (len true-listp))
           :expand ((len plan) (true-listp plan) (len (cdr plan)) (len (cddr plan))
                    (true-listp (cdr plan)) (true-listp (cddr plan)))))))

(defthm fn-his-plan-all-canonical
 (implies (fn-hp-events-okp h)
  (equal (fn-his-plan-all h '(0 (0 0 0 0 0)))
         (list nil (list (len h) (fn-hp-lens h salt)))))
 :hints (("Goal"
          :use ((:instance fn-his-plan-all-count (plan '(0 (0 0 0 0 0))))
                (:instance fn-his-plan-all-lengths (plan '(0 (0 0 0 0 0))))
                (:instance fn-his-plan-all-verdict (plan '(0 (0 0 0 0 0))))
                (:instance fn-his-plan-all-pair (plan '(0 (0 0 0 0 0))))
                (:instance fn-his-plan-all-preserves-planp (evs h) (plan '(0 (0 0 0 0 0)))))
          :in-theory (e/d (fn-hp-x-add)
                          (len fn-his-planp fn-his-plan-all fn-his-plan-all-count fn-his-plan-all-lengths
                           fn-his-plan-all-verdict fn-his-plan-all-preserves-planp
                           fn-hp-lens fn-hp-pe fn-hp-events-okp fn-hp-pes-len)))))

(defthm fn-his-plan-drive-canonical
 (implies (fn-hp-events-okp h)
  (equal (fn-his-plan-drive (+ 1 (len h)) h '(0 (0 0 0 0 0)))
         (list nil (list (len h) (fn-hp-lens h salt)))))
 :hints (("Goal" :use ((:instance fn-his-plan-drive-is-plan-all (evs h) (plan '(0 (0 0 0 0 0)))))
          :in-theory (disable fn-his-plan-drive fn-his-plan-all fn-hp-events-okp fn-hp-lens))))

(defthm fn-his-plan-drive-verdict
 (equal (mv-nth 0 (fn-his-plan-drive (+ 1 (len h)) h plan))
        (if (fn-hp-events-okp h) nil '(:refused :event)))
 :hints (("Goal" :use ((:instance fn-his-plan-drive-is-plan-all (evs h)))
          :in-theory (disable fn-his-plan-drive fn-his-plan-all fn-hp-events-okp))))
