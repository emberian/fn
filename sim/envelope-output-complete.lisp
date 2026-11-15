; Composition target: actual fast-path/DP dispatch and the public matcher.
(in-package "ACL2")
(include-book "envelope-output-linear")
(defun fn2-eo-matching-fuel (segments peer)
 (declare (xargs :guard t))
 (+ 4 (* 4 (len segments)) (len peer)
    (* (+ 5 (* 2 (len peer))) (fn2-envelope-output-source-size segments))))

(local
 (defthm fn2-eo-collect-one-product
 (implies (and (acl2-numberp x) (acl2-numberp c))
  (equal (+ x (* c x)) (* (+ 1 c) x)))
 :hints (("Goal" :use ((:instance distributivity (x x) (y 1) (z c)))
          :in-theory (disable distributivity)))))
(local
 (defthm fn2-eo-double-product
 (implies (acl2-numberp x) (equal (+ x x) (* 2 x)))
 :hints (("Goal" :use ((:instance distributivity (x x) (y 1) (z 1)))
          :in-theory (disable distributivity)))))
(local
 (defthm fn2-eo-product-two-middle
 (equal (* x 2 y) (* 2 (* x y)))
 :hints (("Goal" :use ((:instance associativity-of-* (x 2) (y x) (z y))
                       (:instance associativity-of-* (x x) (y 2) (z y))
                       (:instance commutativity-of-* (x x) (y 2)))
          :in-theory (disable associativity-of-* commutativity-of-*)))))
(local
 (defthm fn2-eo-dp-cost-algebra
 (implies (and (natp n) (natp m) (natp k))
  (equal (+ 3 k m n (* 3 n) (* 4 k) (* k m) (* k m))
         (+ 3 (* 4 n) m (* (+ 5 (* 2 m)) k))))
 :hints (("Goal" :nonlinearp t))))
(local
 (defthm fn2-eo-singleton-reconstruct
 (implies (and (consp xs) (equal (cdr xs) nil))
          (equal (list (car xs)) xs))
 :hints (("Goal" :use ((:instance car-cdr-elim (x xs)))))))
(local
 (defthm fn2-eo-phase1-terminal-result
 (implies (and (equal (fn2-eo-phase fn2-envelope-output-state) 1)
               (fn2-eo-segments-p (fn2-eo-segments fn2-envelope-output-state))
               (fn2-eo-octets-p (fn2-eo-peer fn2-envelope-output-state))
               (equal (fn2-eo-phase (fn2-envelope-output-step fn2-envelope-output-state)) 10))
          (equal (fn2-eo-result (fn2-envelope-output-step fn2-envelope-output-state))
                 (fn2-envelope-output-language-p (fn2-eo-segments fn2-envelope-output-state)
                                                (fn2-eo-peer fn2-envelope-output-state))))
 :hints (("Goal" :in-theory (e/d (fn2-envelope-output-language-p)
                                (fn2-envelope-output-step fn2-eo-collect-one-product fn2-eo-double-product fn2-eo-product-two-middle fn2-eo-dp-cost-algebra))))))
(local
 (defthm fn2-eo-phase1-dispatch-contract
 (implies (and (equal (fn2-eo-phase fn2-envelope-output-state) 1)
               (fn2-eo-segments-p (fn2-eo-segments fn2-envelope-output-state)) (fn2-eo-octets-p (fn2-eo-peer fn2-envelope-output-state)))
  (let ((next (fn2-envelope-output-step fn2-envelope-output-state)))
   (and (member-equal (fn2-eo-phase next) '(1 2 3 10))
        (implies (equal (fn2-eo-phase next) 2)
          (and (fn2-eo-octets-p (fn2-eo-peer next)) (fn2-eo-octets-p (fn2-eo-bytes next))
               (< (+ 1 (len (fn2-eo-peer next))) (fn2-eo-matching-fuel (fn2-eo-segments fn2-envelope-output-state) (fn2-eo-peer fn2-envelope-output-state)))
               (equal (fn2-envelope-output-language-p (list (cons :prefix (fn2-eo-bytes next))) (fn2-eo-peer next))
                      (fn2-envelope-output-language-p (fn2-eo-segments fn2-envelope-output-state) (fn2-eo-peer fn2-envelope-output-state)))))
        (implies (equal (fn2-eo-phase next) 3)
          (and (fn2-eo-segments-p (fn2-eo-segments next)) (fn2-eo-octets-p (fn2-eo-peer next))
               (equal (fn2-eo-ordered next) nil)
               (equal (fn2-eo-segments next) (fn2-eo-segments fn2-envelope-output-state)) (equal (fn2-eo-peer next) (fn2-eo-peer fn2-envelope-output-state)))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn2-envelope-output-language-p)
            (fn2-envelope-output-step fn2-eo-collect-one-product fn2-eo-double-product fn2-eo-product-two-middle fn2-eo-dp-cost-algebra))))))
(local (in-theory (disable fn2-eo-collect-one-product fn2-eo-double-product fn2-eo-product-two-middle fn2-eo-dp-cost-algebra)))

(defthm fn2-eo-phase2-sufficient-fuel
 (implies (and (natp fuel) (<= (+ 1 (len (fn2-eo-peer fn2-envelope-output-state))) fuel)
               (equal (fn2-eo-phase fn2-envelope-output-state) 2)
               (fn2-eo-octets-p (fn2-eo-peer fn2-envelope-output-state)) (fn2-eo-octets-p (fn2-eo-bytes fn2-envelope-output-state)))
  (let ((finished (fn2-envelope-output-run fuel fn2-envelope-output-state)))
   (and (equal (fn2-eo-phase finished) 10)
        (equal (fn2-eo-result finished) (fn2-envelope-output-language-p (list (cons :prefix (fn2-eo-bytes fn2-envelope-output-state))) (fn2-eo-peer fn2-envelope-output-state))))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-eo-phase2-completes-prefix (fuel (+ 1 (len (fn2-eo-peer fn2-envelope-output-state)))))
                       (:instance fn2-eo-run-after-finished (a (+ 1 (len (fn2-eo-peer fn2-envelope-output-state)))) (b fuel)))
          :in-theory (e/d (distributivity) (fn2-eo-collect-one-product fn2-eo-double-product fn2-eo-product-two-middle fn2-eo-dp-cost-algebra fn2-envelope-output-run fn2-envelope-output-step
                              fn2-envelope-output-language-p fn2-eo-phase fn2-eo-result
                              fn2-eo-segments fn2-eo-peer fn2-eo-ordered fn2-eo-bytes)))))

(defthm fn2-eo-phase3-sufficient-fuel
 (implies (and (natp fuel) (<= (+ 3 (* 4 (len (fn2-eo-segments fn2-envelope-output-state))) (len (fn2-eo-peer fn2-envelope-output-state)) (* (+ 5 (* 2 (len (fn2-eo-peer fn2-envelope-output-state)))) (fn2-envelope-output-source-size (fn2-eo-segments fn2-envelope-output-state)))) fuel)
               (equal (fn2-eo-phase fn2-envelope-output-state) 3)
               (fn2-eo-octets-p (fn2-eo-peer fn2-envelope-output-state)) (and (equal (fn2-eo-ordered fn2-envelope-output-state) nil) (fn2-eo-segments-p (fn2-eo-segments fn2-envelope-output-state))))
  (let ((finished (fn2-envelope-output-run fuel fn2-envelope-output-state)))
   (and (equal (fn2-eo-phase finished) 10)
        (equal (fn2-eo-result finished) (fn2-envelope-output-language-p (fn2-eo-segments fn2-envelope-output-state) (fn2-eo-peer fn2-envelope-output-state))))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-eo-dp-cost-algebra (n (len (fn2-eo-segments fn2-envelope-output-state))) (m (len (fn2-eo-peer fn2-envelope-output-state))) (k (fn2-envelope-output-source-size (fn2-eo-segments fn2-envelope-output-state))))
                       (:instance fn2-eo-phase3-completes-language)
                       (:instance fn2-eo-run-after-finished (a (+ 3 (* 4 (len (fn2-eo-segments fn2-envelope-output-state))) (len (fn2-eo-peer fn2-envelope-output-state)) (* (+ 5 (* 2 (len (fn2-eo-peer fn2-envelope-output-state)))) (fn2-envelope-output-source-size (fn2-eo-segments fn2-envelope-output-state))))) (b fuel)))
          :in-theory (e/d (distributivity) (fn2-eo-collect-one-product fn2-eo-double-product fn2-eo-product-two-middle fn2-eo-dp-cost-algebra fn2-envelope-output-run fn2-envelope-output-step
                              fn2-envelope-output-language-p fn2-eo-phase fn2-eo-result
                              fn2-eo-segments fn2-eo-peer fn2-eo-ordered fn2-eo-bytes)))))

(defthm fn2-eo-phase1-sufficient-fuel
 (implies (and (natp fuel) (<= (fn2-eo-matching-fuel (fn2-eo-segments fn2-envelope-output-state) (fn2-eo-peer fn2-envelope-output-state)) fuel)
               (equal (fn2-eo-phase fn2-envelope-output-state) 1)
               (fn2-eo-segments-p (fn2-eo-segments fn2-envelope-output-state)) (fn2-eo-octets-p (fn2-eo-peer fn2-envelope-output-state)))
  (let ((finished (fn2-envelope-output-run fuel fn2-envelope-output-state)))
   (and (equal (fn2-eo-phase finished) 10)
        (equal (fn2-eo-result finished) (fn2-envelope-output-language-p (fn2-eo-segments fn2-envelope-output-state) (fn2-eo-peer fn2-envelope-output-state))))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-envelope-output-run fuel fn2-envelope-output-state)
          :expand ((:free (fuel) (fn2-envelope-output-run fuel fn2-envelope-output-state)))
          :in-theory (e/d ((:induction fn2-envelope-output-run))
                          ((:definition fn2-envelope-output-run) fn2-envelope-output-step fn2-eo-phase1-step-unfolds fn2-eo-phase fn2-eo-peer fn2-eo-segments fn2-eo-bytes fn2-eo-ordered fn2-eo-result fn2-envelope-output-language-p fn2-eo-collect-one-product fn2-eo-double-product fn2-eo-product-two-middle fn2-eo-dp-cost-algebra)))
         ("Subgoal *1/2"
          :use ((:instance fn2-eo-phase1-dispatch-contract)
                (:instance fn2-eo-phase1-terminal-result)
                (:instance fn2-eo-phase1-linear-progress)
                (:instance fn2-eo-phase2-sufficient-fuel (fuel (1- fuel))
                 (fn2-envelope-output-state (fn2-envelope-output-step fn2-envelope-output-state)))
                (:instance fn2-eo-phase3-sufficient-fuel (fuel (1- fuel))
                 (fn2-envelope-output-state (fn2-envelope-output-step fn2-envelope-output-state)))))))
