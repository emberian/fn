; Pending complete reversed-segment traversal through the actual runner.
(in-package "ACL2")
(include-book "envelope-output-dispatch")

; The base membership row is false at every nonempty peer suffix and true at nil.
(defthm fn2-eo-empty-language-row-cons-unfolds
 (equal (fn2-eo-language-row nil (cons byte peer))
        (cons nil (fn2-eo-language-row nil peer)))
 :hints (("Goal" :in-theory (enable fn2-eo-language-row fn2-envelope-output-language-p))))
(defthm fn2-eo-empty-row-move-byte
 (equal (fn2-eo-language-row nil (append todo (cons byte seen)))
        (cons nil (fn2-eo-language-row nil (append todo seen))))
 :hints (("Goal" :induct (append todo seen)
          :in-theory (disable fn2-eo-language-row fn2-envelope-output-language-p))))

(defthm fn2-eo-phase4-step-unfolds
 (implies (equal (fn2-eo-phase fn2-envelope-output-state) 4)
  (equal (fn2-envelope-output-step fn2-envelope-output-state)
   (if (consp (fn2-eo-scan fn2-envelope-output-state))
    (update-fn2-eo-row (cons nil (fn2-eo-row fn2-envelope-output-state))
     (update-fn2-eo-scan (cdr (fn2-eo-scan fn2-envelope-output-state)) fn2-envelope-output-state))
    (update-fn2-eo-phase 5 fn2-envelope-output-state))))
 :hints (("Goal" :in-theory (enable fn2-envelope-output-step))))

(local
 (defun fn2-eo-initial-row-induct (todo seen fn2-envelope-output-state)
  (declare (xargs :stobjs fn2-envelope-output-state :verify-guards nil :measure (len todo)))
  (if (atom todo) (mv seen fn2-envelope-output-state)
   (let ((fn2-envelope-output-state (fn2-envelope-output-step fn2-envelope-output-state)))
    (fn2-eo-initial-row-induct (cdr todo) (cons (car todo) seen) fn2-envelope-output-state)))))

(defthm fn2-eo-phase4-builds-initial-row-aux
 (implies
  (and (equal (fn2-eo-phase fn2-envelope-output-state) 4)
       (equal todo (fn2-eo-scan fn2-envelope-output-state))
       (fn2-eo-octets-p todo) (fn2-eo-octets-p seen)
       (equal (fn2-eo-row fn2-envelope-output-state) (fn2-eo-language-row nil seen)))
  (let ((finished (fn2-envelope-output-run (+ 1 (len todo)) fn2-envelope-output-state)))
   (and (equal (fn2-eo-phase finished) 5)
        (equal (fn2-eo-row finished) (fn2-eo-language-row nil (append todo seen)))
        (equal (fn2-eo-peer finished) (fn2-eo-peer fn2-envelope-output-state))
        (equal (fn2-eo-segments finished) (fn2-eo-segments fn2-envelope-output-state)))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-eo-initial-row-induct todo seen fn2-envelope-output-state)
          :expand ((:free (fuel) (fn2-envelope-output-run fuel fn2-envelope-output-state)))
          :in-theory (e/d ((:induction fn2-eo-initial-row-induct))
                          ((:definition fn2-eo-initial-row-induct) fn2-envelope-output-run
                           fn2-envelope-output-step fn2-eo-language-row fn2-envelope-output-language-p)))))

(defthm fn2-eo-phase4-builds-initial-row
 (implies
  (and (equal (fn2-eo-phase fn2-envelope-output-state) 4)
       (equal (fn2-eo-scan fn2-envelope-output-state) (fn2-eo-peer fn2-envelope-output-state))
       (fn2-eo-octets-p (fn2-eo-peer fn2-envelope-output-state))
       (equal (fn2-eo-row fn2-envelope-output-state) '(t)))
  (let ((finished (fn2-envelope-output-run
                   (+ 1 (len (fn2-eo-peer fn2-envelope-output-state))) fn2-envelope-output-state)))
   (and (equal (fn2-eo-phase finished) 5)
        (equal (fn2-eo-row finished) (fn2-eo-language-row nil (fn2-eo-peer fn2-envelope-output-state)))
        (equal (fn2-eo-peer finished) (fn2-eo-peer fn2-envelope-output-state))
        (equal (fn2-eo-segments finished) (fn2-eo-segments fn2-envelope-output-state)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-eo-phase4-builds-initial-row-aux
                        (todo (fn2-eo-peer fn2-envelope-output-state)) (seen nil)))
          :in-theory (disable fn2-envelope-output-run fn2-envelope-output-step))))

(defthm fn2-eo-phase5-empty-step-unfolds
 (implies (and (equal (fn2-eo-phase fn2-envelope-output-state) 5) (equal (fn2-eo-segments fn2-envelope-output-state) nil))
  (equal (fn2-envelope-output-step fn2-envelope-output-state)
         (update-fn2-eo-result (and (car (fn2-eo-row fn2-envelope-output-state)) t)
          (update-fn2-eo-phase 10 fn2-envelope-output-state))))
 :hints (("Goal" :in-theory (enable fn2-envelope-output-step))))
(defthm fn2-eo-phase5-empty-frame
 (implies (and (equal (fn2-eo-phase fn2-envelope-output-state) 5) (equal (fn2-eo-segments fn2-envelope-output-state) nil))
  (and (equal (fn2-eo-phase (fn2-envelope-output-step fn2-envelope-output-state)) 10)
       (equal (fn2-eo-result (fn2-envelope-output-step fn2-envelope-output-state)) (and (car (fn2-eo-row fn2-envelope-output-state)) t))
       (equal (fn2-eo-row (fn2-envelope-output-step fn2-envelope-output-state)) (fn2-eo-row fn2-envelope-output-state))
       (equal (fn2-eo-peer (fn2-envelope-output-step fn2-envelope-output-state)) (fn2-eo-peer fn2-envelope-output-state))
       (equal (fn2-eo-segments (fn2-envelope-output-step fn2-envelope-output-state)) nil)))
 :hints (("Goal" :in-theory (disable fn2-envelope-output-step))))

(local
 (defun fn2-eo-segments-induct (todo following fn2-envelope-output-state)
  (declare (xargs :stobjs fn2-envelope-output-state :verify-guards nil :measure (len todo)))
  (if (atom todo) (mv following fn2-envelope-output-state)
   (let ((fn2-envelope-output-state (fn2-envelope-output-run (+ 1 (+ 1 (len (cdar todo))) (+ 1 (* (len (cdar todo)) (+ 4 (len (fn2-eo-peer fn2-envelope-output-state)) (len (fn2-eo-peer fn2-envelope-output-state)))))) fn2-envelope-output-state)))
    (fn2-eo-segments-induct (cdr todo) (cons (car todo) following) fn2-envelope-output-state)))))

(defthm fn2-eo-phase5-completes-language-aux
 (implies
  (and (equal todo (fn2-eo-segments fn2-envelope-output-state)) (equal (fn2-eo-phase fn2-envelope-output-state) 5)
       (fn2-eo-segments-p todo) (fn2-eo-segments-p following)
       (fn2-eo-octets-p (fn2-eo-peer fn2-envelope-output-state))
       (equal (fn2-eo-row fn2-envelope-output-state) (fn2-eo-language-row following (fn2-eo-peer fn2-envelope-output-state))))
  (let ((finished (fn2-envelope-output-run (+ 1 (* 3 (len todo)) (fn2-envelope-output-source-size todo) (* (fn2-envelope-output-source-size todo) (+ 4 (len (fn2-eo-peer fn2-envelope-output-state)) (len (fn2-eo-peer fn2-envelope-output-state))))) fn2-envelope-output-state)))
   (and (equal (fn2-eo-phase finished) 10)
        (equal (fn2-eo-segments finished) nil)
        (equal (fn2-eo-peer finished) (fn2-eo-peer fn2-envelope-output-state))
        (equal (fn2-eo-row finished) (fn2-eo-language-row (revappend todo following) (fn2-eo-peer fn2-envelope-output-state)))
        (equal (fn2-eo-result finished)
               (fn2-envelope-output-language-p (revappend todo following) (fn2-eo-peer fn2-envelope-output-state))))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-eo-segments-induct todo following fn2-envelope-output-state)
          :in-theory (e/d ((:induction fn2-eo-segments-induct))
                          ((:definition fn2-eo-segments-induct) fn2-envelope-output-run fn2-envelope-output-step fn2-eo-phase5-empty-step-unfolds fn2-eo-phase5-nonempty-step-unfolds fn2-eo-language-row fn2-envelope-output-language-p fn2-eo-phase fn2-eo-row fn2-eo-peer fn2-eo-segments fn2-eo-result)))
         ("Subgoal *1/2"
          :use ((:instance fn2-eo-phase5-processes-one-segment)
                (:instance fn2-envelope-output-run-resume (a (+ 1 (+ 1 (len (cdar todo))) (+ 1 (* (len (cdar todo)) (+ 4 (len (fn2-eo-peer fn2-envelope-output-state)) (len (fn2-eo-peer fn2-envelope-output-state))))))) (b (+ 1 (* 3 (len (cdr todo))) (fn2-envelope-output-source-size (cdr todo)) (* (fn2-envelope-output-source-size (cdr todo)) (+ 4 (len (fn2-eo-peer fn2-envelope-output-state)) (len (fn2-eo-peer fn2-envelope-output-state)))))))))))

(defthm fn2-eo-dp-from-initial-row
 (implies
  (and (equal (fn2-eo-phase fn2-envelope-output-state) 4)
       (equal (fn2-eo-scan fn2-envelope-output-state) (fn2-eo-peer fn2-envelope-output-state))
       (equal (fn2-eo-row fn2-envelope-output-state) '(t))
       (fn2-eo-octets-p (fn2-eo-peer fn2-envelope-output-state)) (fn2-eo-segments-p (fn2-eo-segments fn2-envelope-output-state)))
  (let ((finished (fn2-envelope-output-run (+ (+ 1 (len (fn2-eo-peer fn2-envelope-output-state))) (+ 1 (* 3 (len (fn2-eo-segments fn2-envelope-output-state))) (fn2-envelope-output-source-size (fn2-eo-segments fn2-envelope-output-state)) (* (fn2-envelope-output-source-size (fn2-eo-segments fn2-envelope-output-state)) (+ 4 (len (fn2-eo-peer fn2-envelope-output-state)) (len (fn2-eo-peer fn2-envelope-output-state)))))) fn2-envelope-output-state)))
   (and (equal (fn2-eo-phase finished) 10)
        (equal (fn2-eo-segments finished) nil)
        (equal (fn2-eo-peer finished) (fn2-eo-peer fn2-envelope-output-state))
        (equal (fn2-eo-result finished)
               (fn2-envelope-output-language-p (revappend (fn2-eo-segments fn2-envelope-output-state) nil) (fn2-eo-peer fn2-envelope-output-state))))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn2-eo-phase4-builds-initial-row)
        (:instance fn2-eo-phase5-completes-language-aux
         (todo (fn2-eo-segments fn2-envelope-output-state)) (following nil) (fn2-envelope-output-state (fn2-envelope-output-run (+ 1 (len (fn2-eo-peer fn2-envelope-output-state))) fn2-envelope-output-state)))
        (:instance fn2-envelope-output-run-resume (a (+ 1 (len (fn2-eo-peer fn2-envelope-output-state)))) (b (+ 1 (* 3 (len (fn2-eo-segments fn2-envelope-output-state))) (fn2-envelope-output-source-size (fn2-eo-segments fn2-envelope-output-state)) (* (fn2-envelope-output-source-size (fn2-eo-segments fn2-envelope-output-state)) (+ 4 (len (fn2-eo-peer fn2-envelope-output-state)) (len (fn2-eo-peer fn2-envelope-output-state))))))))
  :in-theory (disable fn2-envelope-output-run fn2-envelope-output-step
                      fn2-eo-language-row fn2-envelope-output-language-p
                      fn2-eo-phase fn2-eo-scan fn2-eo-row fn2-eo-peer fn2-eo-segments fn2-eo-result))))
