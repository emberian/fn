; Actual complete-row context frames and phase7 batch composition.
(in-package "ACL2")
(include-book "envelope-output-row")

(defthm fn2-eo-phase8-preserves-byte-context
 (implies (and (natp fuel) (equal (fn2-eo-phase fn2-envelope-output-state) 8)
               (equal fuel (+ 1 (len (fn2-eo-scan fn2-envelope-output-state)))))
  (let ((finished (fn2-envelope-output-run fuel fn2-envelope-output-state)))
   (and (equal (fn2-eo-peer finished) (fn2-eo-peer fn2-envelope-output-state))
        (equal (fn2-eo-prefix finished) (fn2-eo-prefix fn2-envelope-output-state))
        (equal (fn2-eo-bytes finished) (fn2-eo-bytes fn2-envelope-output-state))
        (equal (fn2-eo-byte finished) (fn2-eo-byte fn2-envelope-output-state))
        (equal (fn2-eo-suffix finished) (fn2-eo-suffix fn2-envelope-output-state))
        (equal (fn2-eo-segments finished) (fn2-eo-segments fn2-envelope-output-state)))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-envelope-output-run fuel fn2-envelope-output-state)
          :expand ((:free (fuel) (fn2-envelope-output-run fuel fn2-envelope-output-state)))
          :in-theory (e/d ((:induction fn2-envelope-output-run))
                          ((:definition fn2-envelope-output-run) fn2-envelope-output-step)))))

(defthm fn2-eo-phase9-preserves-byte-context
 (implies (and (natp fuel) (equal (fn2-eo-phase fn2-envelope-output-state) 9)
               (equal fuel (+ 1 (len (fn2-eo-acc fn2-envelope-output-state)))))
  (let ((finished (fn2-envelope-output-run fuel fn2-envelope-output-state)))
   (and (equal (fn2-eo-peer finished) (fn2-eo-peer fn2-envelope-output-state))
        (equal (fn2-eo-prefix finished) (fn2-eo-prefix fn2-envelope-output-state))
        (equal (fn2-eo-bytes finished) (fn2-eo-bytes fn2-envelope-output-state))
        (equal (fn2-eo-byte finished) (fn2-eo-byte fn2-envelope-output-state))
        (equal (fn2-eo-suffix finished) (fn2-eo-suffix fn2-envelope-output-state))
        (equal (fn2-eo-segments finished) (fn2-eo-segments fn2-envelope-output-state)))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-envelope-output-run fuel fn2-envelope-output-state)
          :expand ((:free (fuel) (fn2-envelope-output-run fuel fn2-envelope-output-state)))
          :in-theory (e/d ((:induction fn2-envelope-output-run))
                          ((:definition fn2-envelope-output-run) fn2-envelope-output-step)))))
(defthm fn2-eo-phase8-9-preserves-byte-context
 (implies
  (and (equal (fn2-eo-acc fn2-envelope-output-state) nil)
       (equal (fn2-eo-phase fn2-envelope-output-state) 8)
       (fn2-eo-octets-p (fn2-eo-scan fn2-envelope-output-state))
       (unsigned-byte-p 8 (fn2-eo-byte fn2-envelope-output-state))
       (fn2-eo-octets-p rest) (fn2-eo-segments-p following)
       (equal (fn2-eo-suffix-scan fn2-envelope-output-state)
              (fn2-eo-language-row following (fn2-eo-scan fn2-envelope-output-state)))
       (equal (fn2-eo-shifted fn2-envelope-output-state)
        (cdr (fn2-eo-language-row
         (cons (cons (if (fn2-eo-prefix fn2-envelope-output-state) :prefix :exact) rest) following)
         (fn2-eo-scan fn2-envelope-output-state)))))
  (let ((finished (fn2-envelope-output-run
                    (+ 3 (len (fn2-eo-scan fn2-envelope-output-state)) (len (fn2-eo-scan fn2-envelope-output-state))) fn2-envelope-output-state)))
   (and (equal (fn2-eo-peer finished) (fn2-eo-peer fn2-envelope-output-state))
        (equal (fn2-eo-prefix finished) (fn2-eo-prefix fn2-envelope-output-state))
        (equal (fn2-eo-bytes finished) (fn2-eo-bytes fn2-envelope-output-state))
        (equal (fn2-eo-byte finished) (fn2-eo-byte fn2-envelope-output-state))
        (equal (fn2-eo-suffix finished) (fn2-eo-suffix fn2-envelope-output-state))
        (equal (fn2-eo-segments finished) (fn2-eo-segments fn2-envelope-output-state)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-eo-phase8-builds-whole-row (fuel (+ 1 (len (fn2-eo-scan fn2-envelope-output-state)))))
        (:instance fn2-eo-phase8-preserves-byte-context (fuel (+ 1 (len (fn2-eo-scan fn2-envelope-output-state)))))
        (:instance fn2-eo-phase9-preserves-byte-context
         (fuel (+ 2 (len (fn2-eo-scan fn2-envelope-output-state)))) (fn2-envelope-output-state (fn2-envelope-output-run (+ 1 (len (fn2-eo-scan fn2-envelope-output-state))) fn2-envelope-output-state)))
        (:instance fn2-envelope-output-run-resume
         (a (+ 1 (len (fn2-eo-scan fn2-envelope-output-state)))) (b (+ 2 (len (fn2-eo-scan fn2-envelope-output-state))))))
          :in-theory (disable fn2-envelope-output-run fn2-envelope-output-step
                              fn2-eo-language-row fn2-envelope-output-language-p fn2-eo-peer fn2-eo-prefix fn2-eo-bytes fn2-eo-byte fn2-eo-suffix fn2-eo-segments fn2-eo-phase fn2-eo-row fn2-eo-scan fn2-eo-acc fn2-eo-reversed fn2-eo-suffix-scan fn2-eo-shifted))))

(defthm fn2-eo-phase7-step-unfolds
 (implies (equal (fn2-eo-phase fn2-envelope-output-state) 7)
  (equal (fn2-envelope-output-step fn2-envelope-output-state)
   (if (consp (fn2-eo-bytes fn2-envelope-output-state))
    (update-fn2-eo-acc nil
     (update-fn2-eo-suffix-scan (fn2-eo-suffix fn2-envelope-output-state)
      (update-fn2-eo-shifted (cdr (fn2-eo-row fn2-envelope-output-state))
       (update-fn2-eo-scan (fn2-eo-peer fn2-envelope-output-state)
        (update-fn2-eo-bytes (cdr (fn2-eo-bytes fn2-envelope-output-state))
         (update-fn2-eo-byte (car (fn2-eo-bytes fn2-envelope-output-state))
          (update-fn2-eo-phase 8 fn2-envelope-output-state)))))))
    (update-fn2-eo-phase 5 fn2-envelope-output-state))))
 :hints (("Goal" :in-theory (enable fn2-envelope-output-step))))

(defthm fn2-eo-phase7-launch-frame
 (implies (and (equal (fn2-eo-phase fn2-envelope-output-state) 7) (consp (fn2-eo-bytes fn2-envelope-output-state)))
  (and (equal (fn2-eo-phase (fn2-envelope-output-step fn2-envelope-output-state)) 8)
       (equal (fn2-eo-acc (fn2-envelope-output-step fn2-envelope-output-state)) nil)
       (equal (fn2-eo-scan (fn2-envelope-output-step fn2-envelope-output-state)) (fn2-eo-peer fn2-envelope-output-state))
       (equal (fn2-eo-shifted (fn2-envelope-output-step fn2-envelope-output-state)) (cdr (fn2-eo-row fn2-envelope-output-state)))
       (equal (fn2-eo-suffix-scan (fn2-envelope-output-step fn2-envelope-output-state)) (fn2-eo-suffix fn2-envelope-output-state))
       (equal (fn2-eo-byte (fn2-envelope-output-step fn2-envelope-output-state)) (car (fn2-eo-bytes fn2-envelope-output-state)))
       (equal (fn2-eo-bytes (fn2-envelope-output-step fn2-envelope-output-state)) (cdr (fn2-eo-bytes fn2-envelope-output-state)))
       (equal (fn2-eo-peer (fn2-envelope-output-step fn2-envelope-output-state)) (fn2-eo-peer fn2-envelope-output-state))
       (equal (fn2-eo-prefix (fn2-envelope-output-step fn2-envelope-output-state)) (fn2-eo-prefix fn2-envelope-output-state))
       (equal (fn2-eo-suffix (fn2-envelope-output-step fn2-envelope-output-state)) (fn2-eo-suffix fn2-envelope-output-state))
       (equal (fn2-eo-segments (fn2-envelope-output-step fn2-envelope-output-state)) (fn2-eo-segments fn2-envelope-output-state))
       (equal (fn2-eo-row (fn2-envelope-output-step fn2-envelope-output-state)) (fn2-eo-row fn2-envelope-output-state))))
 :hints (("Goal" :in-theory (disable fn2-envelope-output-step))))

(defthm fn2-eo-phase7-prepends-source-byte
 (implies
  (and (equal (fn2-eo-phase fn2-envelope-output-state) 7)
       (consp (fn2-eo-bytes fn2-envelope-output-state))
       (fn2-eo-octets-p (fn2-eo-bytes fn2-envelope-output-state))
       (fn2-eo-octets-p (fn2-eo-peer fn2-envelope-output-state))
       (fn2-eo-octets-p rest) (fn2-eo-segments-p following)
       (equal (fn2-eo-suffix fn2-envelope-output-state)
              (fn2-eo-language-row following (fn2-eo-peer fn2-envelope-output-state)))
       (equal (fn2-eo-row fn2-envelope-output-state)
        (fn2-eo-language-row
         (cons (cons (if (fn2-eo-prefix fn2-envelope-output-state) :prefix :exact) rest) following)
         (fn2-eo-peer fn2-envelope-output-state))))
  (let ((finished (fn2-envelope-output-run
                   (+ 4 (len (fn2-eo-peer fn2-envelope-output-state))
                        (len (fn2-eo-peer fn2-envelope-output-state)))
                   fn2-envelope-output-state)))
   (and (equal (fn2-eo-phase finished) 7)
        (equal (fn2-eo-bytes finished) (cdr (fn2-eo-bytes fn2-envelope-output-state)))
        (equal (fn2-eo-peer finished) (fn2-eo-peer fn2-envelope-output-state))
        (equal (fn2-eo-prefix finished) (fn2-eo-prefix fn2-envelope-output-state))
        (equal (fn2-eo-suffix finished) (fn2-eo-suffix fn2-envelope-output-state))
        (equal (fn2-eo-segments finished) (fn2-eo-segments fn2-envelope-output-state))
        (equal (fn2-eo-row finished)
         (fn2-eo-language-row
          (cons (cons (if (fn2-eo-prefix fn2-envelope-output-state) :prefix :exact)
                      (cons (car (fn2-eo-bytes fn2-envelope-output-state)) rest)) following)
          (fn2-eo-peer fn2-envelope-output-state))))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn2-eo-phase8-9-completes-semantic-row
         (fn2-envelope-output-state (fn2-envelope-output-step fn2-envelope-output-state)))
        (:instance fn2-eo-phase8-9-preserves-byte-context
         (fn2-envelope-output-state (fn2-envelope-output-step fn2-envelope-output-state)))
        (:instance fn2-envelope-output-run-resume
         (a 1) (b (+ 3 (len (fn2-eo-peer fn2-envelope-output-state))
                       (len (fn2-eo-peer fn2-envelope-output-state))))))
  :in-theory (disable fn2-envelope-output-run fn2-envelope-output-step
                      fn2-eo-language-row fn2-envelope-output-language-p fn2-eo-phase7-step-unfolds
                      fn2-eo-phase fn2-eo-acc fn2-eo-scan fn2-eo-shifted fn2-eo-suffix-scan fn2-eo-byte fn2-eo-bytes fn2-eo-peer fn2-eo-prefix fn2-eo-suffix fn2-eo-segments fn2-eo-row))))
