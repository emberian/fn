; Composition target: actual fast-path/DP dispatch and the public matcher.
(in-package "ACL2")
(include-book "envelope-output-linear")
(defun fn2-eo-matching-fuel (segments peer)
 (declare (xargs :guard t))
 (+ 4 (* 4 (len segments)) (len peer)
    (* (+ 5 (* 2 (len peer))) (fn2-envelope-output-source-size segments))))

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
          :in-theory (disable fn2-envelope-output-run fn2-envelope-output-step
                              fn2-envelope-output-language-p fn2-eo-phase fn2-eo-result
                              fn2-eo-segments fn2-eo-peer fn2-eo-ordered fn2-eo-bytes))))

(defthm fn2-eo-phase3-sufficient-fuel
 (implies (and (natp fuel) (<= (+ 3 (* 4 (len (fn2-eo-segments fn2-envelope-output-state))) (len (fn2-eo-peer fn2-envelope-output-state)) (* (+ 5 (* 2 (len (fn2-eo-peer fn2-envelope-output-state)))) (fn2-envelope-output-source-size (fn2-eo-segments fn2-envelope-output-state)))) fuel)
               (equal (fn2-eo-phase fn2-envelope-output-state) 3)
               (fn2-eo-octets-p (fn2-eo-peer fn2-envelope-output-state)) (and (equal (fn2-eo-ordered fn2-envelope-output-state) nil) (fn2-eo-segments-p (fn2-eo-segments fn2-envelope-output-state))))
  (let ((finished (fn2-envelope-output-run fuel fn2-envelope-output-state)))
   (and (equal (fn2-eo-phase finished) 10)
        (equal (fn2-eo-result finished) (fn2-envelope-output-language-p (fn2-eo-segments fn2-envelope-output-state) (fn2-eo-peer fn2-envelope-output-state))))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-eo-phase3-completes-language)
                       (:instance fn2-eo-run-after-finished (a (+ 3 (* 4 (len (fn2-eo-segments fn2-envelope-output-state))) (len (fn2-eo-peer fn2-envelope-output-state)) (* (+ 5 (* 2 (len (fn2-eo-peer fn2-envelope-output-state)))) (fn2-envelope-output-source-size (fn2-eo-segments fn2-envelope-output-state))))) (b fuel)))
          :in-theory (disable fn2-envelope-output-run fn2-envelope-output-step
                              fn2-envelope-output-language-p fn2-eo-phase fn2-eo-result
                              fn2-eo-segments fn2-eo-peer fn2-eo-ordered fn2-eo-bytes))))

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
          :in-theory (e/d ((:induction fn2-envelope-output-run) fn2-envelope-output-language-p)
                          ((:definition fn2-envelope-output-run) fn2-envelope-output-step)))
         ("Subgoal *1/2"
          :use ((:instance fn2-eo-phase1-linear-progress)
                (:instance fn2-eo-phase2-sufficient-fuel (fuel (1- fuel))
                 (fn2-envelope-output-state (fn2-envelope-output-step fn2-envelope-output-state)))
                (:instance fn2-eo-phase3-sufficient-fuel (fuel (1- fuel))
                 (fn2-envelope-output-state (fn2-envelope-output-step fn2-envelope-output-state)))))))
