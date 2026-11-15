; Pending author proof: actual phase5 dispatch and phase6 reversal.
(in-package "ACL2")
(include-book "envelope-output-segment-loop")

(defthm fn2-eo-phase6-step-unfolds
 (implies (equal (fn2-eo-phase fn2-envelope-output-state) 6)
  (equal (fn2-envelope-output-step fn2-envelope-output-state)
   (if (consp (fn2-eo-bytes fn2-envelope-output-state))
    (update-fn2-eo-reversed
     (cons (car (fn2-eo-bytes fn2-envelope-output-state)) (fn2-eo-reversed fn2-envelope-output-state))
     (update-fn2-eo-bytes (cdr (fn2-eo-bytes fn2-envelope-output-state)) fn2-envelope-output-state))
    (update-fn2-eo-bytes (fn2-eo-reversed fn2-envelope-output-state)
     (update-fn2-eo-phase 7 fn2-envelope-output-state)))))
 :hints (("Goal" :in-theory (enable fn2-envelope-output-step))))

(defthm fn2-eo-phase6-reverses-payload
 (implies
  (and (natp fuel) (equal (fn2-eo-phase fn2-envelope-output-state) 6)
       (equal fuel (+ 1 (len (fn2-eo-bytes fn2-envelope-output-state)))))
  (let ((finished (fn2-envelope-output-run fuel fn2-envelope-output-state)))
   (and (equal (fn2-eo-phase finished) 7)
        (equal (fn2-eo-bytes finished)
               (revappend (fn2-eo-bytes fn2-envelope-output-state) (fn2-eo-reversed fn2-envelope-output-state)))
        (equal (fn2-eo-reversed finished)
               (revappend (fn2-eo-bytes fn2-envelope-output-state) (fn2-eo-reversed fn2-envelope-output-state)))
        (equal (fn2-eo-peer finished) (fn2-eo-peer fn2-envelope-output-state))
        (equal (fn2-eo-prefix finished) (fn2-eo-prefix fn2-envelope-output-state))
        (equal (fn2-eo-suffix finished) (fn2-eo-suffix fn2-envelope-output-state))
        (equal (fn2-eo-segments finished) (fn2-eo-segments fn2-envelope-output-state))
        (equal (fn2-eo-row finished) (fn2-eo-row fn2-envelope-output-state)))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-envelope-output-run fuel fn2-envelope-output-state)
          :expand ((:free (fuel) (fn2-envelope-output-run fuel fn2-envelope-output-state)))
          :in-theory (e/d ((:induction fn2-envelope-output-run))
                          ((:definition fn2-envelope-output-run) fn2-envelope-output-step)))))

(defthm fn2-eo-empty-segment-row
 (implies (or (equal mode :exact) (equal mode :prefix))
  (equal (fn2-eo-language-row (cons (cons mode nil) following) peer)
         (fn2-eo-language-row following peer)))
 :hints (("Goal" :induct (fn2-eo-language-row following peer)
          :in-theory (enable fn2-eo-language-row fn2-envelope-output-language-p))))

(defthm fn2-eo-phase5-nonempty-step-unfolds
 (implies
  (and (equal (fn2-eo-phase fn2-envelope-output-state) 5)
       (consp (fn2-eo-segments fn2-envelope-output-state))
       (fn2-eo-segments-p (fn2-eo-segments fn2-envelope-output-state)))
  (equal (fn2-envelope-output-step fn2-envelope-output-state)
   (update-fn2-eo-prefix (eq (caar (fn2-eo-segments fn2-envelope-output-state)) :prefix)
    (update-fn2-eo-suffix (fn2-eo-row fn2-envelope-output-state)
     (update-fn2-eo-reversed nil
      (update-fn2-eo-bytes (cdar (fn2-eo-segments fn2-envelope-output-state))
       (update-fn2-eo-segments (cdr (fn2-eo-segments fn2-envelope-output-state))
        (update-fn2-eo-phase 6 fn2-envelope-output-state))))))))
 :hints (("Goal" :in-theory (enable fn2-envelope-output-step fn2-eo-segments-p))))

(defthm fn2-eo-phase5-launch-frame
 (implies (and (equal (fn2-eo-phase fn2-envelope-output-state) 5) (consp (fn2-eo-segments fn2-envelope-output-state)) (fn2-eo-segments-p (fn2-eo-segments fn2-envelope-output-state)))
  (and (equal (fn2-eo-phase (fn2-envelope-output-step fn2-envelope-output-state)) 6)
       (equal (fn2-eo-segments (fn2-envelope-output-step fn2-envelope-output-state)) (cdr (fn2-eo-segments fn2-envelope-output-state)))
       (equal (fn2-eo-bytes (fn2-envelope-output-step fn2-envelope-output-state)) (cdar (fn2-eo-segments fn2-envelope-output-state)))
       (equal (fn2-eo-reversed (fn2-envelope-output-step fn2-envelope-output-state)) nil)
       (equal (fn2-eo-prefix (fn2-envelope-output-step fn2-envelope-output-state)) (eq (caar (fn2-eo-segments fn2-envelope-output-state)) :prefix))
       (equal (fn2-eo-suffix (fn2-envelope-output-step fn2-envelope-output-state)) (fn2-eo-row fn2-envelope-output-state))
       (equal (fn2-eo-row (fn2-envelope-output-step fn2-envelope-output-state)) (fn2-eo-row fn2-envelope-output-state))
       (equal (fn2-eo-peer (fn2-envelope-output-step fn2-envelope-output-state)) (fn2-eo-peer fn2-envelope-output-state))))
 :hints (("Goal" :in-theory (disable fn2-envelope-output-step))))

(defthm fn2-eo-phase5-processes-one-segment
 (implies
  (and (equal (fn2-eo-phase fn2-envelope-output-state) 5)
       (consp (fn2-eo-segments fn2-envelope-output-state)) (fn2-eo-segments-p (fn2-eo-segments fn2-envelope-output-state))
       (fn2-eo-octets-p (fn2-eo-peer fn2-envelope-output-state)) (fn2-eo-segments-p following)
       (equal (fn2-eo-row fn2-envelope-output-state) (fn2-eo-language-row following (fn2-eo-peer fn2-envelope-output-state))))
  (let ((finished (fn2-envelope-output-run (+ 1 (+ 1 (len (cdar (fn2-eo-segments fn2-envelope-output-state)))) (+ 1 (* (len (cdar (fn2-eo-segments fn2-envelope-output-state))) (+ 4 (len (fn2-eo-peer fn2-envelope-output-state)) (len (fn2-eo-peer fn2-envelope-output-state)))))) fn2-envelope-output-state)))
   (and (equal (fn2-eo-phase finished) 5)
        (equal (fn2-eo-segments finished) (cdr (fn2-eo-segments fn2-envelope-output-state)))
        (equal (fn2-eo-peer finished) (fn2-eo-peer fn2-envelope-output-state))
        (equal (fn2-eo-row finished)
               (fn2-eo-language-row (cons (car (fn2-eo-segments fn2-envelope-output-state)) following) (fn2-eo-peer fn2-envelope-output-state))))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn2-eo-phase6-reverses-payload (fuel (+ 1 (len (cdar (fn2-eo-segments fn2-envelope-output-state))))) (fn2-envelope-output-state (fn2-envelope-output-step fn2-envelope-output-state)))
        (:instance fn2-eo-phase7-completes-segment (rest nil) (fn2-envelope-output-state (fn2-envelope-output-run (+ 1 (len (cdar (fn2-eo-segments fn2-envelope-output-state)))) (fn2-envelope-output-step fn2-envelope-output-state))))
        (:instance fn2-envelope-output-run-resume (a (+ 1 (len (cdar (fn2-eo-segments fn2-envelope-output-state))))) (b (+ 1 (* (len (cdar (fn2-eo-segments fn2-envelope-output-state))) (+ 4 (len (fn2-eo-peer fn2-envelope-output-state)) (len (fn2-eo-peer fn2-envelope-output-state)))))) (fn2-envelope-output-state (fn2-envelope-output-step fn2-envelope-output-state)))
        (:instance fn2-envelope-output-run-resume (a 1) (b (+ (+ 1 (len (cdar (fn2-eo-segments fn2-envelope-output-state)))) (+ 1 (* (len (cdar (fn2-eo-segments fn2-envelope-output-state))) (+ 4 (len (fn2-eo-peer fn2-envelope-output-state)) (len (fn2-eo-peer fn2-envelope-output-state)))))))))
  :in-theory (disable fn2-envelope-output-run fn2-envelope-output-step
                      fn2-eo-phase5-nonempty-step-unfolds fn2-eo-phase6-step-unfolds
                      fn2-eo-language-row fn2-envelope-output-language-p fn2-eo-phase fn2-eo-segments fn2-eo-bytes fn2-eo-reversed fn2-eo-prefix fn2-eo-suffix fn2-eo-row fn2-eo-peer))))
