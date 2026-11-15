; Actual linear matching paths; no replacement runtime evaluator.
(in-package "ACL2")
(include-book "envelope-output-dp-entry")
(include-book "envelope-output-validation")

(defthm fn2-eo-phase2-step-unfolds
 (implies (equal (fn2-eo-phase fn2-envelope-output-state) 2)
  (equal (fn2-envelope-output-step fn2-envelope-output-state)
   (cond ((atom (fn2-eo-peer fn2-envelope-output-state)) (update-fn2-eo-result (equal (fn2-eo-peer fn2-envelope-output-state) nil) (update-fn2-eo-phase 10 fn2-envelope-output-state)))
         ((and (consp (fn2-eo-bytes fn2-envelope-output-state)) (equal (car (fn2-eo-peer fn2-envelope-output-state)) (car (fn2-eo-bytes fn2-envelope-output-state))))
          (update-fn2-eo-bytes (cdr (fn2-eo-bytes fn2-envelope-output-state)) (update-fn2-eo-peer (cdr (fn2-eo-peer fn2-envelope-output-state)) fn2-envelope-output-state)))
         (t (update-fn2-eo-result nil (update-fn2-eo-phase 10 fn2-envelope-output-state))))))
 :hints (("Goal" :in-theory (enable fn2-envelope-output-step))))

(defthm fn2-eo-phase2-completes-prefix
 (implies
  (and (natp fuel) (equal fuel (+ 1 (len (fn2-eo-peer fn2-envelope-output-state))))
       (equal (fn2-eo-phase fn2-envelope-output-state) 2)
       (fn2-eo-octets-p (fn2-eo-peer fn2-envelope-output-state)) (fn2-eo-octets-p (fn2-eo-bytes fn2-envelope-output-state)))
  (let ((finished (fn2-envelope-output-run fuel fn2-envelope-output-state)))
   (and (equal (fn2-eo-phase finished) 10)
        (equal (fn2-eo-result finished)
               (fn2-envelope-output-language-p (list (cons :prefix (fn2-eo-bytes fn2-envelope-output-state))) (fn2-eo-peer fn2-envelope-output-state))))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-envelope-output-run fuel fn2-envelope-output-state)
          :expand ((:free (fuel) (fn2-envelope-output-run fuel fn2-envelope-output-state)))
          :in-theory (e/d ((:induction fn2-envelope-output-run) fn2-envelope-output-language-p)
                          ((:definition fn2-envelope-output-run) fn2-envelope-output-step fn2-eo-terminal-step-run)))))


(defthm fn2-eo-phase1-step-unfolds
 (implies (equal (fn2-eo-phase fn2-envelope-output-state) 1)
  (equal (fn2-envelope-output-step fn2-envelope-output-state)
   (let ((segments (fn2-eo-segments fn2-envelope-output-state)) (peer (fn2-eo-peer fn2-envelope-output-state)))
    (cond ((atom segments)
                    (let* ((fn2-envelope-output-state (update-fn2-eo-phase 10
                                                                           fn2-envelope-output-state))
                           (fn2-envelope-output-state (update-fn2-eo-result (equal peer
                                                                                   nil)
                                                                            fn2-envelope-output-state)))
                      fn2-envelope-output-state))
                   ((eq (fn2-eo-first (fn2-eo-first segments)) :exact)
                    (cond ((atom (fn2-eo-rest (fn2-eo-first segments)))
                           (let* ((fn2-envelope-output-state (update-fn2-eo-segments (fn2-eo-rest segments)
                                                                                     fn2-envelope-output-state)))
                             fn2-envelope-output-state))
                          ((and (consp peer) (equal (fn2-eo-first peer) (fn2-eo-first (fn2-eo-rest (fn2-eo-first segments)))))
                           (let* ((fn2-envelope-output-state (update-fn2-eo-peer (fn2-eo-rest peer)
                                                                                 fn2-envelope-output-state))
                                  (fn2-envelope-output-state (update-fn2-eo-segments (cons (cons :exact (fn2-eo-rest (fn2-eo-rest (fn2-eo-first segments))))
                                                                                           (fn2-eo-rest segments))
                                                                                     fn2-envelope-output-state)))
                             fn2-envelope-output-state))
                          (t (let* ((fn2-envelope-output-state (update-fn2-eo-phase 10
                                                                                    fn2-envelope-output-state))
                                    (fn2-envelope-output-state (update-fn2-eo-result nil
                                                                                     fn2-envelope-output-state)))
                               fn2-envelope-output-state))))
                   ((eq (fn2-eo-first (fn2-eo-first segments)) :prefix)
                    (if (atom (fn2-eo-rest segments))
                        (let* ((fn2-envelope-output-state (update-fn2-eo-phase 2
                                                                               fn2-envelope-output-state))
                               (fn2-envelope-output-state (update-fn2-eo-bytes (fn2-eo-rest (fn2-eo-first segments))
                                                                               fn2-envelope-output-state)))
                          fn2-envelope-output-state)
                      (let* ((fn2-envelope-output-state (update-fn2-eo-phase 3
                                                                             fn2-envelope-output-state))
                             (fn2-envelope-output-state (update-fn2-eo-ordered nil
                                                                               fn2-envelope-output-state)))
                        fn2-envelope-output-state)))
                   (t (let* ((fn2-envelope-output-state (update-fn2-eo-phase 10
                                                                             fn2-envelope-output-state))
                             (fn2-envelope-output-state (update-fn2-eo-result nil
                                                                              fn2-envelope-output-state)))
                        fn2-envelope-output-state))))))
 :hints (("Goal" :in-theory (enable fn2-envelope-output-step))))

(defthm fn2-eo-phase1-linear-progress
 (implies (and (equal (fn2-eo-phase fn2-envelope-output-state) 1)
               (fn2-eo-segments-p (fn2-eo-segments fn2-envelope-output-state)) (fn2-eo-octets-p (fn2-eo-peer fn2-envelope-output-state))
               (equal (fn2-eo-phase (fn2-envelope-output-step fn2-envelope-output-state)) 1))
  (let ((next (fn2-envelope-output-step fn2-envelope-output-state)))
   (and (fn2-eo-segments-p (fn2-eo-segments next))
        (fn2-eo-octets-p (fn2-eo-peer next))
        (equal (fn2-envelope-output-language-p (fn2-eo-segments next) (fn2-eo-peer next))
               (fn2-envelope-output-language-p (fn2-eo-segments fn2-envelope-output-state) (fn2-eo-peer fn2-envelope-output-state)))
        (< (+ 4 (* 4 (len (fn2-eo-segments next))) (len (fn2-eo-peer next))
              (* (+ 5 (* 2 (len (fn2-eo-peer next)))) (fn2-envelope-output-source-size (fn2-eo-segments next))))
           (+ 4 (* 4 (len (fn2-eo-segments fn2-envelope-output-state))) (len (fn2-eo-peer fn2-envelope-output-state))
              (* (+ 5 (* 2 (len (fn2-eo-peer fn2-envelope-output-state)))) (fn2-envelope-output-source-size (fn2-eo-segments fn2-envelope-output-state))))))))
 :hints (("Goal" :in-theory (e/d (fn2-envelope-output-language-p)
                                (fn2-envelope-output-step)))))

(defthm fn2-eo-cancel-sum
 (implies (acl2-numberp b) (equal (+ a (- a) b) b))
 :hints (("Goal" :use ((:instance associativity-of-+ (x a) (y (- a)) (z b))
                       (:instance inverse-of-+ (x a)))
          :in-theory (disable associativity-of-+ inverse-of-+))))

(defthm fn2-eo-run-after-finished
 (implies (and (natp a) (natp b) (<= a b)
               (equal (fn2-eo-phase (fn2-envelope-output-run a fn2-envelope-output-state)) 10))
          (equal (fn2-envelope-output-run b fn2-envelope-output-state)
                 (fn2-envelope-output-run a fn2-envelope-output-state)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-envelope-output-run-resume (b (- b a))))
          :in-theory (e/d (associativity-of-+ inverse-of-+ unicity-of-0) (fn2-envelope-output-run fn2-envelope-output-step)))))
(defthm fn2-eo-source-size-revappend
 (equal (fn2-envelope-output-source-size (revappend a b))
        (+ (fn2-envelope-output-source-size a) (fn2-envelope-output-source-size b))))
