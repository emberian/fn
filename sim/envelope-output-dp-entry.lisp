; Actual phase3 reversal and entry into the DP language theorem.
(in-package "ACL2")
(include-book "envelope-output-dp-loop")

(defthm fn2-eo-phase3-step-unfolds
 (implies (equal (fn2-eo-phase fn2-envelope-output-state) 3)
  (equal (fn2-envelope-output-step fn2-envelope-output-state)
   (if (consp (fn2-eo-segments fn2-envelope-output-state))
    (update-fn2-eo-ordered
     (cons (car (fn2-eo-segments fn2-envelope-output-state)) (fn2-eo-ordered fn2-envelope-output-state))
     (update-fn2-eo-segments (cdr (fn2-eo-segments fn2-envelope-output-state)) fn2-envelope-output-state))
    (update-fn2-eo-row '(t)
     (update-fn2-eo-scan (fn2-eo-peer fn2-envelope-output-state)
      (update-fn2-eo-segments (fn2-eo-ordered fn2-envelope-output-state)
       (update-fn2-eo-phase 4 fn2-envelope-output-state)))))))
 :hints (("Goal" :in-theory (enable fn2-envelope-output-step))))

(defthm fn2-eo-phase3-reverses-segments
 (implies
  (and (natp fuel) (equal (fn2-eo-phase fn2-envelope-output-state) 3)
       (equal fuel (+ 1 (len (fn2-eo-segments fn2-envelope-output-state)))))
  (let ((finished (fn2-envelope-output-run fuel fn2-envelope-output-state)))
   (and (equal (fn2-eo-phase finished) 4)
        (equal (fn2-eo-segments finished)
               (revappend (fn2-eo-segments fn2-envelope-output-state) (fn2-eo-ordered fn2-envelope-output-state)))
        (equal (fn2-eo-peer finished) (fn2-eo-peer fn2-envelope-output-state))
        (equal (fn2-eo-scan finished) (fn2-eo-peer fn2-envelope-output-state))
        (equal (fn2-eo-row finished) '(t)))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-envelope-output-run fuel fn2-envelope-output-state)
          :expand ((:free (fuel) (fn2-envelope-output-run fuel fn2-envelope-output-state)))
          :in-theory (e/d ((:induction fn2-envelope-output-run))
                          ((:definition fn2-envelope-output-run) fn2-envelope-output-step)))))

(defthm fn2-eo-segments-revappend
 (implies (and (fn2-eo-segments-p a) (fn2-eo-segments-p b))
          (fn2-eo-segments-p (revappend a b))))

(defthm fn2-eo-segments-true-listp
 (implies (fn2-eo-segments-p a) (true-listp a)))

(defthm fn2-eo-phase3-completes-language
 (implies
  (and (equal (fn2-eo-phase fn2-envelope-output-state) 3)
       (equal (fn2-eo-ordered fn2-envelope-output-state) nil)
       (fn2-eo-segments-p (fn2-eo-segments fn2-envelope-output-state)) (fn2-eo-octets-p (fn2-eo-peer fn2-envelope-output-state)))
  (let ((finished (fn2-envelope-output-run (+ (+ 1 (len (fn2-eo-segments fn2-envelope-output-state))) (+ (+ 1 (len (fn2-eo-peer fn2-envelope-output-state))) (+ 1 (* 3 (len (revappend (fn2-eo-segments fn2-envelope-output-state) nil))) (fn2-envelope-output-source-size (revappend (fn2-eo-segments fn2-envelope-output-state) nil)) (* (fn2-envelope-output-source-size (revappend (fn2-eo-segments fn2-envelope-output-state) nil)) (+ 4 (len (fn2-eo-peer fn2-envelope-output-state)) (len (fn2-eo-peer fn2-envelope-output-state))))))) fn2-envelope-output-state)))
   (and (equal (fn2-eo-phase finished) 10)
        (equal (fn2-eo-peer finished) (fn2-eo-peer fn2-envelope-output-state))
        (equal (fn2-eo-result finished) (fn2-envelope-output-language-p (fn2-eo-segments fn2-envelope-output-state) (fn2-eo-peer fn2-envelope-output-state))))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn2-eo-phase3-reverses-segments (fuel (+ 1 (len (fn2-eo-segments fn2-envelope-output-state)))))
        (:instance fn2-eo-dp-from-initial-row
         (fn2-envelope-output-state (fn2-envelope-output-run (+ 1 (len (fn2-eo-segments fn2-envelope-output-state))) fn2-envelope-output-state)))
        (:instance fn2-envelope-output-run-resume (a (+ 1 (len (fn2-eo-segments fn2-envelope-output-state)))) (b (+ (+ 1 (len (fn2-eo-peer fn2-envelope-output-state))) (+ 1 (* 3 (len (revappend (fn2-eo-segments fn2-envelope-output-state) nil))) (fn2-envelope-output-source-size (revappend (fn2-eo-segments fn2-envelope-output-state) nil)) (* (fn2-envelope-output-source-size (revappend (fn2-eo-segments fn2-envelope-output-state) nil)) (+ 4 (len (fn2-eo-peer fn2-envelope-output-state)) (len (fn2-eo-peer fn2-envelope-output-state)))))))))
  :in-theory (disable fn2-envelope-output-run fn2-envelope-output-step
                      fn2-eo-phase3-step-unfolds fn2-envelope-output-language-p
                      fn2-eo-phase fn2-eo-peer fn2-eo-result fn2-eo-segments
                      fn2-eo-ordered fn2-eo-scan fn2-eo-row))))
