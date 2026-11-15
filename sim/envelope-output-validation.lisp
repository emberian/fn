; Actual bounded validation, separately from language semantics.
(in-package "ACL2")
; The validator uses the actual run-zero/run-one contracts owned by row.
(include-book "envelope-output-row")

(defthm fn2-eo-terminal-run-identity
 (implies (equal (fn2-eo-phase fn2-envelope-output-state) 10)
          (equal (fn2-envelope-output-run fuel fn2-envelope-output-state)
                 fn2-envelope-output-state))
 :hints (("Goal" :in-theory (enable fn2-envelope-output-run))))

(defthm fn2-eo-phase11-step-unfolds
 (implies (equal (fn2-eo-phase fn2-envelope-output-state) 11)
  (equal (fn2-envelope-output-step fn2-envelope-output-state)
   (cond ((consp (fn2-eo-bytes fn2-envelope-output-state))
          (if (unsigned-byte-p 8 (car (fn2-eo-bytes fn2-envelope-output-state)))
              (update-fn2-eo-bytes (cdr (fn2-eo-bytes fn2-envelope-output-state)) fn2-envelope-output-state) (update-fn2-eo-result nil (update-fn2-eo-phase 10 fn2-envelope-output-state))))
         ((equal (fn2-eo-bytes fn2-envelope-output-state) nil) (update-fn2-eo-phase 0 fn2-envelope-output-state))
         (t (update-fn2-eo-result nil (update-fn2-eo-phase 10 fn2-envelope-output-state))))))
 :hints (("Goal" :in-theory (enable fn2-envelope-output-step))))

(defthm fn2-eo-phase11-validates-octets
 (implies (and (natp fuel) (equal (fn2-eo-phase fn2-envelope-output-state) 11)
               (equal fuel (+ 1 (len (fn2-eo-bytes fn2-envelope-output-state)))))
  (let ((finished (fn2-envelope-output-run fuel fn2-envelope-output-state)))
   (and (equal (fn2-eo-peer finished) (fn2-eo-peer fn2-envelope-output-state))
        (equal (fn2-eo-segments finished) (fn2-eo-segments fn2-envelope-output-state))
        (equal (fn2-eo-ordered finished) (fn2-eo-ordered fn2-envelope-output-state))
        (if (fn2-eo-octets-p (fn2-eo-bytes fn2-envelope-output-state))
            (and (equal (fn2-eo-phase finished) 0)
                 (equal (fn2-eo-bytes finished) nil))
          (and (equal (fn2-eo-phase finished) 10)
               (equal (fn2-eo-result finished) nil))))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-envelope-output-run fuel fn2-envelope-output-state)
          :expand ((:free (fuel) (fn2-envelope-output-run fuel fn2-envelope-output-state)))
          :in-theory (e/d ((:induction fn2-envelope-output-run))
                          ((:definition fn2-envelope-output-run) fn2-envelope-output-step)))))

(defthm fn2-eo-phase12-step-unfolds
 (implies (equal (fn2-eo-phase fn2-envelope-output-state) 12)
  (equal (fn2-envelope-output-step fn2-envelope-output-state)
   (cond ((consp (fn2-eo-scan fn2-envelope-output-state))
          (if (unsigned-byte-p 8 (car (fn2-eo-scan fn2-envelope-output-state)))
              (update-fn2-eo-scan (cdr (fn2-eo-scan fn2-envelope-output-state)) fn2-envelope-output-state) (update-fn2-eo-result nil (update-fn2-eo-phase 10 fn2-envelope-output-state))))
         ((equal (fn2-eo-scan fn2-envelope-output-state) nil) (update-fn2-eo-phase 1 fn2-envelope-output-state))
         (t (update-fn2-eo-result nil (update-fn2-eo-phase 10 fn2-envelope-output-state))))))
 :hints (("Goal" :in-theory (enable fn2-envelope-output-step))))

(defthm fn2-eo-phase12-validates-octets
 (implies (and (natp fuel) (equal (fn2-eo-phase fn2-envelope-output-state) 12)
               (equal fuel (+ 1 (len (fn2-eo-scan fn2-envelope-output-state)))))
  (let ((finished (fn2-envelope-output-run fuel fn2-envelope-output-state)))
   (and (equal (fn2-eo-peer finished) (fn2-eo-peer fn2-envelope-output-state))
        (equal (fn2-eo-segments finished) (fn2-eo-segments fn2-envelope-output-state))
        (equal (fn2-eo-ordered finished) (fn2-eo-ordered fn2-envelope-output-state))
        (if (fn2-eo-octets-p (fn2-eo-scan fn2-envelope-output-state))
            (and (equal (fn2-eo-phase finished) 1)
                 (equal (fn2-eo-scan finished) nil))
          (and (equal (fn2-eo-phase finished) 10)
               (equal (fn2-eo-result finished) nil))))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-envelope-output-run fuel fn2-envelope-output-state)
          :expand ((:free (fuel) (fn2-envelope-output-run fuel fn2-envelope-output-state)))
          :in-theory (e/d ((:induction fn2-envelope-output-run))
                          ((:definition fn2-envelope-output-run) fn2-envelope-output-step)))))

(defthm fn2-eo-terminal-step-run
 (implies (and (natp fuel) (< 0 fuel)
               (not (equal (fn2-eo-phase fn2-envelope-output-state) 10))
               (equal (fn2-eo-phase (fn2-envelope-output-step fn2-envelope-output-state)) 10))
          (equal (fn2-envelope-output-run fuel fn2-envelope-output-state)
                 (fn2-envelope-output-step fn2-envelope-output-state)))
 :hints (("Goal" :expand ((fn2-envelope-output-run fuel fn2-envelope-output-state))
          :in-theory (disable fn2-envelope-output-run fn2-envelope-output-step))))


(defthm fn2-eo-phase0-step-unfolds
 (implies (equal (fn2-eo-phase fn2-envelope-output-state) 0)
  (equal (fn2-envelope-output-step fn2-envelope-output-state)
   (cond ((consp (fn2-eo-segments fn2-envelope-output-state))
          (if (and (consp (car (fn2-eo-segments fn2-envelope-output-state))) (member-eq (caar (fn2-eo-segments fn2-envelope-output-state)) '(:exact :prefix)))
              (update-fn2-eo-bytes (cdar (fn2-eo-segments fn2-envelope-output-state))
               (update-fn2-eo-ordered (cons (car (fn2-eo-segments fn2-envelope-output-state)) (fn2-eo-ordered fn2-envelope-output-state))
                (update-fn2-eo-segments (cdr (fn2-eo-segments fn2-envelope-output-state)) (update-fn2-eo-phase 11 fn2-envelope-output-state))))
            (update-fn2-eo-result nil (update-fn2-eo-phase 10 fn2-envelope-output-state))))
         ((equal (fn2-eo-segments fn2-envelope-output-state) nil)
          (update-fn2-eo-scan (fn2-eo-peer fn2-envelope-output-state)
           (update-fn2-eo-segments (fn2-eo-ordered fn2-envelope-output-state) (update-fn2-eo-phase 12 fn2-envelope-output-state))))
         (t (update-fn2-eo-result nil (update-fn2-eo-phase 10 fn2-envelope-output-state))))))
 :hints (("Goal" :in-theory (enable fn2-envelope-output-step))))

(defthm fn2-eo-phase0-validates-one-segment
 (implies
  (and (equal (fn2-eo-phase fn2-envelope-output-state) 0) (consp (fn2-eo-segments fn2-envelope-output-state))
       (consp (car (fn2-eo-segments fn2-envelope-output-state))) (member-eq (caar (fn2-eo-segments fn2-envelope-output-state)) '(:exact :prefix)))
  (let ((finished (fn2-envelope-output-run (+ 2 (len (cdar (fn2-eo-segments fn2-envelope-output-state)))) fn2-envelope-output-state)))
   (and (equal (fn2-eo-peer finished) (fn2-eo-peer fn2-envelope-output-state))
        (equal (fn2-eo-segments finished) (cdr (fn2-eo-segments fn2-envelope-output-state)))
        (equal (fn2-eo-ordered finished) (cons (car (fn2-eo-segments fn2-envelope-output-state)) (fn2-eo-ordered fn2-envelope-output-state)))
        (if (fn2-eo-octets-p (cdar (fn2-eo-segments fn2-envelope-output-state)))
            (equal (fn2-eo-phase finished) 0)
          (and (equal (fn2-eo-phase finished) 10)
               (equal (fn2-eo-result finished) nil))))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn2-eo-phase11-validates-octets
          (fuel (+ 1 (len (cdar (fn2-eo-segments fn2-envelope-output-state)))))
          (fn2-envelope-output-state (fn2-envelope-output-step fn2-envelope-output-state)))
        (:instance fn2-envelope-output-run-resume
          (a 1) (b (+ 1 (len (cdar (fn2-eo-segments fn2-envelope-output-state)))))))
  :in-theory (disable fn2-envelope-output-run fn2-envelope-output-step))))


(local
 (defun fn2-eo-validation-induct (todo fn2-envelope-output-state)
  (declare (xargs :stobjs fn2-envelope-output-state :verify-guards nil :measure (len todo)))
  (if (and (consp todo) (consp (car todo))
           (member-eq (caar todo) '(:exact :prefix)) (fn2-eo-octets-p (cdar todo)))
      (let ((fn2-envelope-output-state (fn2-envelope-output-run (+ 2 (len (cdar todo))) fn2-envelope-output-state)))
        (fn2-eo-validation-induct (cdr todo) fn2-envelope-output-state))
    fn2-envelope-output-state)))

(defthm fn2-eo-phase0-validates-segments
 (implies (and (equal todo (fn2-eo-segments fn2-envelope-output-state)) (equal (fn2-eo-phase fn2-envelope-output-state) 0))
  (let ((finished (fn2-envelope-output-run (+ 1 (* 2 (len todo)) (fn2-envelope-output-source-size todo)) fn2-envelope-output-state)))
   (and (equal (fn2-eo-peer finished) (fn2-eo-peer fn2-envelope-output-state))
        (if (fn2-eo-segments-p todo)
            (and (equal (fn2-eo-phase finished) 12)
                 (equal (fn2-eo-segments finished) (revappend todo (fn2-eo-ordered fn2-envelope-output-state)))
                 (equal (fn2-eo-scan finished) (fn2-eo-peer fn2-envelope-output-state)))
          (and (equal (fn2-eo-phase finished) 10)
               (equal (fn2-eo-result finished) nil))))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-eo-validation-induct todo fn2-envelope-output-state)
          :in-theory (e/d ((:induction fn2-eo-validation-induct))
                          ((:definition fn2-eo-validation-induct) fn2-envelope-output-run fn2-envelope-output-step)))
         ("Subgoal *1/1"
          :use ((:instance fn2-eo-phase0-validates-one-segment)
                (:instance fn2-envelope-output-run-resume
                 (a (+ 2 (len (cdar todo))))
                 (b (+ 1 (* 2 (len (cdr todo))) (fn2-envelope-output-source-size (cdr todo)))))))
         ("Subgoal *1/2"
          :use ((:instance fn2-eo-phase0-validates-one-segment)
                (:instance fn2-envelope-output-run-resume
                 (a (+ 2 (len (cdar todo))))
                 (b (+ 1 (* 2 (len (cdr todo))) (fn2-envelope-output-source-size (cdr todo)))))))))


(defthm fn2-eo-validation-reaches-matching-or-refuses
 (implies (and (equal (fn2-eo-phase fn2-envelope-output-state) 0) (equal (fn2-eo-ordered fn2-envelope-output-state) nil))
  (let ((finished (fn2-envelope-output-run (+ (+ 1 (* 2 (len (fn2-eo-segments fn2-envelope-output-state))) (fn2-envelope-output-source-size (fn2-eo-segments fn2-envelope-output-state))) (+ 1 (len (fn2-eo-peer fn2-envelope-output-state)))) fn2-envelope-output-state)))
   (if (and (fn2-eo-segments-p (fn2-eo-segments fn2-envelope-output-state)) (fn2-eo-octets-p (fn2-eo-peer fn2-envelope-output-state)))
       (and (equal (fn2-eo-phase finished) 1)
            (equal (fn2-eo-segments finished) (revappend (fn2-eo-segments fn2-envelope-output-state) nil))
            (equal (fn2-eo-peer finished) (fn2-eo-peer fn2-envelope-output-state)))
     (and (equal (fn2-eo-phase finished) 10)
          (equal (fn2-eo-result finished) nil)))))
 :rule-classes nil
 :hints (("Goal"
   :use ((:instance fn2-eo-phase0-validates-segments (todo (fn2-eo-segments fn2-envelope-output-state)))
         (:instance fn2-eo-phase12-validates-octets
          (fuel (+ 1 (len (fn2-eo-peer fn2-envelope-output-state)))) (fn2-envelope-output-state (fn2-envelope-output-run (+ 1 (* 2 (len (fn2-eo-segments fn2-envelope-output-state))) (fn2-envelope-output-source-size (fn2-eo-segments fn2-envelope-output-state))) fn2-envelope-output-state)))
         (:instance fn2-envelope-output-run-resume (a (+ 1 (* 2 (len (fn2-eo-segments fn2-envelope-output-state))) (fn2-envelope-output-source-size (fn2-eo-segments fn2-envelope-output-state)))) (b (+ 1 (len (fn2-eo-peer fn2-envelope-output-state))))))
   :in-theory (disable fn2-envelope-output-run fn2-envelope-output-step
                       fn2-eo-terminal-step-run fn2-eo-phase0-step-unfolds fn2-eo-phase12-step-unfolds
                       fn2-eo-phase fn2-eo-segments fn2-eo-peer fn2-eo-result fn2-eo-scan fn2-eo-ordered))))
