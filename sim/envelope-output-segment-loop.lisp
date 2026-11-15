; Actual whole-segment induction through the admitted source-byte batch.
(in-package "ACL2")
(include-book "envelope-output-segment")
(local ; Proof-only induction scheme; every transition is the existing actual runner.
(defun fn2-eo-source-byte-induct (todo rest fn2-envelope-output-state)
 (declare (xargs :stobjs fn2-envelope-output-state :verify-guards nil
                 :measure (len todo)))
 (if (atom todo) (mv rest fn2-envelope-output-state)
  (let ((fn2-envelope-output-state
         (fn2-envelope-output-run
          (+ 4 (len (fn2-eo-peer fn2-envelope-output-state))
               (len (fn2-eo-peer fn2-envelope-output-state)))
          fn2-envelope-output-state)))
   (fn2-eo-source-byte-induct (cdr todo) (cons (car todo) rest) fn2-envelope-output-state))))
)
(defthm fn2-eo-zero-product
 (equal (* 0 x) 0)
 :hints (("Goal" :use ((:instance distributivity (x x) (y 0) (z 0))
                       (:instance commutativity-of-* (x x) (y 0))))))
(defthm fn2-eo-phase7-empty-frame
 (implies (and (equal (fn2-eo-phase fn2-envelope-output-state) 7)
               (equal (fn2-eo-bytes fn2-envelope-output-state) nil))
  (and (equal (fn2-eo-phase (fn2-envelope-output-step fn2-envelope-output-state)) 5)
       (equal (fn2-eo-bytes (fn2-envelope-output-step fn2-envelope-output-state)) nil)
       (equal (fn2-eo-peer (fn2-envelope-output-step fn2-envelope-output-state)) (fn2-eo-peer fn2-envelope-output-state))
       (equal (fn2-eo-segments (fn2-envelope-output-step fn2-envelope-output-state)) (fn2-eo-segments fn2-envelope-output-state))
       (equal (fn2-eo-row (fn2-envelope-output-step fn2-envelope-output-state)) (fn2-eo-row fn2-envelope-output-state))))
 :hints (("Goal" :in-theory (disable fn2-envelope-output-step))))

(defthm fn2-eo-phase7-completes-segment-aux
 (implies
  (and (equal todo (fn2-eo-bytes fn2-envelope-output-state))
       (equal (fn2-eo-phase fn2-envelope-output-state) 7)
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
                   (+ 1 (* (len todo)
                           (+ 4 (len (fn2-eo-peer fn2-envelope-output-state))
                                (len (fn2-eo-peer fn2-envelope-output-state)))))
                   fn2-envelope-output-state)))
   (and (equal (fn2-eo-phase finished) 5)
        (equal (fn2-eo-bytes finished) nil)
        (equal (fn2-eo-peer finished) (fn2-eo-peer fn2-envelope-output-state))
        (equal (fn2-eo-segments finished) (fn2-eo-segments fn2-envelope-output-state))
        (equal (fn2-eo-row finished)
         (fn2-eo-language-row
          (cons (cons (if (fn2-eo-prefix fn2-envelope-output-state) :prefix :exact)
                      (revappend todo rest)) following)
          (fn2-eo-peer fn2-envelope-output-state))))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-eo-source-byte-induct todo rest fn2-envelope-output-state)
          :in-theory (e/d ((:induction fn2-eo-source-byte-induct))
           (fn2-envelope-output-run fn2-envelope-output-step fn2-eo-phase7-step-unfolds
            (:definition fn2-eo-source-byte-induct)
            fn2-eo-language-row fn2-envelope-output-language-p
            fn2-eo-phase fn2-eo-bytes fn2-eo-peer fn2-eo-prefix fn2-eo-suffix fn2-eo-segments fn2-eo-row)))
         ("Subgoal *1/2"
          :use ((:instance fn2-eo-phase7-prepends-source-byte)
                (:instance fn2-envelope-output-run-resume
                 (a (+ 4 (len (fn2-eo-peer fn2-envelope-output-state)) (len (fn2-eo-peer fn2-envelope-output-state))))
                 (b (+ 1 (* (len (cdr todo)) (+ 4 (len (fn2-eo-peer fn2-envelope-output-state)) (len (fn2-eo-peer fn2-envelope-output-state)))))))))))
(defthm fn2-eo-phase7-completes-segment
 (implies
  (and (equal (fn2-eo-phase fn2-envelope-output-state) 7)
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
                   (+ 1 (* (len (fn2-eo-bytes fn2-envelope-output-state))
                           (+ 4 (len (fn2-eo-peer fn2-envelope-output-state))
                                (len (fn2-eo-peer fn2-envelope-output-state)))))
                   fn2-envelope-output-state)))
   (and (equal (fn2-eo-phase finished) 5)
        (equal (fn2-eo-bytes finished) nil)
        (equal (fn2-eo-peer finished) (fn2-eo-peer fn2-envelope-output-state))
        (equal (fn2-eo-segments finished) (fn2-eo-segments fn2-envelope-output-state))
        (equal (fn2-eo-row finished)
         (fn2-eo-language-row
          (cons (cons (if (fn2-eo-prefix fn2-envelope-output-state) :prefix :exact)
                      (revappend (fn2-eo-bytes fn2-envelope-output-state) rest)) following)
          (fn2-eo-peer fn2-envelope-output-state))))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-eo-phase7-completes-segment-aux
                        (todo (fn2-eo-bytes fn2-envelope-output-state))))
          :in-theory (disable fn2-envelope-output-run fn2-envelope-output-step
                              fn2-eo-language-row fn2-envelope-output-language-p))))
