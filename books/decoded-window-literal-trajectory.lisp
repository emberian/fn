; Actual literal batching normalized to existing actual decoder actions.
; Work in progress; no general trajectory, scheduling budget or native grant.
(in-package "ACL2")
(include-book "decoded-window-action-trajectory")

(local
 (defthm fn-pwz-update-nth-same
   (equal (update-nth i x (update-nth i y z)) (update-nth i x z))
   :hints (("Goal" :induct (update-nth i x z)
            :in-theory (enable update-nth)))))

(local
 (defun fn-pwz-index-pair-induction (i j z)
   (declare (xargs :measure (nfix i) :verify-guards nil))
   (if (and (posp i) (posp j))
       (fn-pwz-index-pair-induction (1- i) (1- j) (cdr z))
     z)))

(local
 (defthm fn-pwz-update-nth-commute
   (implies (and (natp i) (natp j) (not (equal i j)))
            (equal (update-nth i x (update-nth j y z))
                   (update-nth j y (update-nth i x z))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-pwz-index-pair-induction i j z)
            :in-theory (enable update-nth)))))

(local
 (defthm fn-pwz-state-set-same
   (equal (fn-zin-set i x (fn-zin-set i y fn-zin-st))
          (fn-zin-set i x fn-zin-st))
   :hints (("Goal" :in-theory (enable fn-zin-set$inline)))))

(local
 (defthm fn-pwz-state-set-commute
   (implies (not (equal i j))
            (equal (fn-zin-set i x (fn-zin-set j y fn-zin-st))
                   (fn-zin-set j y (fn-zin-set i x fn-zin-st))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-zin-set$inline)
            :use ((:instance fn-pwz-update-nth-commute
                            (x (nfix x)) (y (nfix y)) (z (car fn-zin-st))))))))

(local
 (defthm fn-pwz-state-set-canonical-order
   (implies (and (natp i) (natp j) (< j i))
            (equal (fn-zin-set i x (fn-zin-set j y fn-zin-st))
                   (fn-zin-set j y (fn-zin-set i x fn-zin-st))))
   :rule-classes ((:rewrite :loop-stopper nil))
   :hints (("Goal" :use ((:instance fn-pwz-state-set-commute))))))


(local
 (defthm fn-pwz-actual-literal-first-action-effects
   (let* ((entry (fn-zin-tget (+ 723 (fn-zin-lowb (fn-zin-bits fn-zin-st) 9)) fn-zin-tab))
          (width (fn-zin-highb entry 9))
          (octet (fn-zin-lowb entry 9)))
     (implies (and (equal (fn-zin-mode fn-zin-st) 8)
                   (fn-zin-freshp fn-zin-st)
                   (fn-zin-lit-ready-p fn-zin-st fn-zin-tab))
              (equal (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                     (mv nil
                         (fn-zin-set 6 (1+ (fn-zin-tout fn-zin-st))
                                     (fn-zin-set 5 (fn-zin-wrap (1+ (fn-zin-wrap (fn-zin-wpos fn-zin-st))))
                                                 (fn-zin-set 2 (- (fn-zin-nbits fn-zin-st) width)
                                                             (fn-zin-set 1 (fn-zin-highb (fn-zin-bits fn-zin-st) width)
                                                                         fn-zin-st))))
                         (fn-oct-update (fn-zin-wrap (fn-zin-wpos fn-zin-st)) octet fn-zin-win)
                         fn-zin-tab (fn-oct-snoc fn-zin-out octet)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-zin-act fn-zin-decode-bit fn-zin-freshp
                                       fn-zin-lit-ready-p fn-zin-emit fn-zin-lk-base)
                            (fn-zin-emit-out))))))

(local
 (defthm fn-pwz-literal-loop-tout-monotone
   (implies (and (natp tout) (natp nbits))
            (<= tout (mv-nth 3 (fn-zin-lit-loop k bits nbits w tout limit
                                               fn-zin-tab fn-zin-win fn-zin-out))))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance fn-zin-lit-loop-counts))
            :in-theory (disable fn-zin-lit-loop-counts)))))

(local
 (defthm fn-pwz-ready-literal-batch-positive
   (implies (and (posp room)
                 (fn-zin-lit-ready-p fn-zin-st fn-zin-tab))
            (< 0 (car (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :expand ((:free (bits nbits w tout limit tab win out)
                             (fn-zin-lit-loop room bits nbits w tout limit tab win out)))
            :in-theory (e/d (fn-zin-lits fn-zin-lit-ready-p) (fn-zin-lit-loop-out-free))))))

(local
 (defthm fn-pwz-literal-batch-first-action-and-tail
   (implies (and (posp room)
                 (equal (fn-zin-mode fn-zin-st) 8)
                 (fn-zin-freshp fn-zin-st)
                 (fn-zin-lit-ready-p fn-zin-st fn-zin-tab))
            (equal (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                   (let* ((first (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
                          (tail (fn-zin-lits (1- room) (mv-nth 1 first) (mv-nth 2 first)
                                             (mv-nth 3 first) (mv-nth 4 first))))
                     (mv (1+ (car tail)) (mv-nth 1 tail) (mv-nth 2 tail) (mv-nth 3 tail)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-pwz-actual-literal-first-action-effects))
            :expand ((:free (bits nbits w tout limit tab win out)
                             (fn-zin-lit-loop room bits nbits w tout limit tab win out)))
            :in-theory (e/d (fn-zin-lits fn-zin-lit-ready-p fn-zin-freshp)
                            (fn-zin-act fn-zin-act-counts fn-zin-lit-loop-out-free))))))

(local
 (defun fn-pwz-literal-canonical-state-p (z)
   (equal z (update-nth 0
                       (update-nth 6 (nfix (nth 6 (car z)))
                                   (update-nth 5 (nfix (nth 5 (car z)))
                                               (update-nth 2 (nfix (nth 2 (car z)))
                                                           (update-nth 1 (nfix (nth 1 (car z))) (car z)))))
                       z))))

(local
 (defthm fn-pwz-literal-first-action-state
   (let* ((entry (fn-zin-tget (+ 723 (fn-zin-lowb (fn-zin-bits fn-zin-st) 9)) fn-zin-tab))
          (width (fn-zin-highb entry 9)))
     (implies (and (equal (fn-zin-mode fn-zin-st) 8)
                   (fn-zin-freshp fn-zin-st)
                   (fn-zin-lit-ready-p fn-zin-st fn-zin-tab))
              (equal (mv-nth 1 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
                     (fn-zin-set 6 (1+ (fn-zin-tout fn-zin-st))
                                 (fn-zin-set 5 (fn-zin-wrap (1+ (fn-zin-wrap (fn-zin-wpos fn-zin-st))))
                                             (fn-zin-set 2 (- (fn-zin-nbits fn-zin-st) width)
                                                         (fn-zin-set 1 (fn-zin-highb (fn-zin-bits fn-zin-st) width)
                                                                     fn-zin-st)))))))
   :hints (("Goal" :use ((:instance fn-pwz-actual-literal-first-action-effects))
            :in-theory (disable fn-zin-act fn-zin-act-counts)))))

(local
 (defthm fn-pwz-update-nth-canonical-order
   (implies (and (natp i) (natp j) (< j i))
            (equal (update-nth i x (update-nth j y z))
                   (update-nth j y (update-nth i x z))))
   :rule-classes ((:rewrite :loop-stopper nil))
   :hints (("Goal" :use ((:instance fn-pwz-update-nth-commute))))))

(local
 (defthm fn-pwz-literal-first-action-canonical
   (implies (and (equal (fn-zin-mode fn-zin-st) 8)
                 (fn-zin-freshp fn-zin-st)
                 (fn-zin-lit-ready-p fn-zin-st fn-zin-tab))
            (fn-pwz-literal-canonical-state-p
             (mv-nth 1 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-pwz-actual-literal-first-action-effects))
            :in-theory (e/d (fn-pwz-literal-canonical-state-p fn-zin-lit-ready-p fn-zin-set$inline fn-zin-fld$inline)
                            (fn-zin-act fn-zin-act-counts))))))

(local
 (defthm fn-pwz-literal-canonical-state-unfolds
   (equal (fn-pwz-literal-canonical-state-p fn-zin-st)
          (equal fn-zin-st
                 (fn-zin-set 6 (fn-zin-tout fn-zin-st)
                             (fn-zin-set 5 (fn-zin-wpos fn-zin-st)
                                         (fn-zin-set 2 (fn-zin-nbits fn-zin-st)
                                                     (fn-zin-set 1 (fn-zin-bits fn-zin-st) fn-zin-st))))))
   :hints (("Goal" :in-theory (enable fn-pwz-literal-canonical-state-p
                                     fn-zin-set$inline fn-zin-fld$inline)))))

(local
 (defthm fn-pwz-literal-batch-terminal-effects
   (implies (and (fn-pwz-literal-canonical-state-p fn-zin-st)
                 (or (zp room) (not (fn-zin-lit-ready-p fn-zin-st fn-zin-tab))))
            (equal (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                   (mv 0 fn-zin-st fn-zin-win fn-zin-out)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :expand ((:free (bits nbits w tout limit tab win out)
                             (fn-zin-lit-loop room bits nbits w tout limit tab win out)))
            :in-theory (e/d (fn-zin-lits fn-zin-lit-ready-p)
                            (fn-zin-lit-loop-out-free))))))

(local
 (defun fn-pwz-literal-action-induction (room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
   (declare (xargs :stobjs (fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                   :verify-guards nil :measure (nfix room)))
   (if (and (posp room) (fn-zin-lit-ready-p fn-zin-st fn-zin-tab))
       (mv-let (why fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
         (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
         (declare (ignore why))
         (fn-pwz-literal-action-induction (1- room) fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
     (mv fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))

(local
 (defthm fn-pwz-literal-batch-first-action-and-tail-rewrite
   (implies (and (posp room)
                 (equal (fn-zin-mode fn-zin-st) 8)
                 (fn-zin-freshp fn-zin-st)
                 (fn-zin-lit-ready-p fn-zin-st fn-zin-tab))
            (equal (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                   (let* ((first (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
                          (tail (fn-zin-lits (1- room) (mv-nth 1 first) (mv-nth 2 first)
                                             (mv-nth 3 first) (mv-nth 4 first))))
                     (mv (1+ (car tail)) (mv-nth 1 tail) (mv-nth 2 tail) (mv-nth 3 tail)))))
   :rule-classes :rewrite
   :hints (("Goal" :use ((:instance fn-pwz-literal-batch-first-action-and-tail))
            :in-theory (disable fn-zin-lits fn-zin-act fn-zin-act-counts)))))

(local
 (defthm fn-pwz-actual-literal-first-action-effects-rewrite
   (let* ((entry (fn-zin-tget (+ 723 (fn-zin-lowb (fn-zin-bits fn-zin-st) 9)) fn-zin-tab))
          (width (fn-zin-highb entry 9))
          (octet (fn-zin-lowb entry 9)))
     (implies (and (equal (fn-zin-mode fn-zin-st) 8)
                   (fn-zin-freshp fn-zin-st)
                   (fn-zin-lit-ready-p fn-zin-st fn-zin-tab))
              (equal (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                     (mv nil
                         (fn-zin-set 6 (1+ (fn-zin-tout fn-zin-st))
                                     (fn-zin-set 5 (fn-zin-wrap (1+ (fn-zin-wrap (fn-zin-wpos fn-zin-st))))
                                                 (fn-zin-set 2 (- (fn-zin-nbits fn-zin-st) width)
                                                             (fn-zin-set 1 (fn-zin-highb (fn-zin-bits fn-zin-st) width)
                                                                         fn-zin-st))))
                         (fn-oct-update (fn-zin-wrap (fn-zin-wpos fn-zin-st)) octet fn-zin-win)
                         fn-zin-tab (fn-oct-snoc fn-zin-out octet)))))
   :rule-classes :rewrite
   :hints (("Goal" :use ((:instance fn-pwz-actual-literal-first-action-effects))
            :in-theory (disable fn-zin-act fn-zin-act-counts)))))

(local
 (defthm fn-pwz-canonical-literal-batch-is-action-sequence
   (let* ((batch (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
          (count (car batch)))
     (implies (and (natp room)
                   (fn-pwz-literal-canonical-state-p fn-zin-st)
                   (equal (fn-zin-mode fn-zin-st) 8)
                   (fn-zin-freshp fn-zin-st))
              (equal (fn-pwz-action-sequence count fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                     (mv nil (mv-nth 1 batch) (mv-nth 2 batch) fn-zin-tab (mv-nth 3 batch)))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-pwz-literal-action-induction room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
            :in-theory (e/d (fn-pwz-action-sequence fn-zin-freshp)
                            (fn-zin-act fn-zin-act-counts fn-zin-lits fn-zin-lits-out-free fn-oct-update fn-oct-snoc
                             fn-pwz-literal-canonical-state-p fn-pwz-literal-canonical-state-unfolds)))
           ("Subgoal *1/2" :use ((:instance fn-pwz-literal-batch-terminal-effects)))
           ("Subgoal *1/1" :use ((:instance fn-pwz-literal-batch-first-action-and-tail)
                                 (:instance fn-pwz-actual-literal-first-action-effects)
                                 (:instance fn-pwz-literal-first-action-canonical))))))

(defthm fn-pwz-actual-ready-literal-batch-is-action-trajectory
  (let* ((batch (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
         (count (car batch)))
    (implies (and (posp room)
                  (equal (fn-zin-mode fn-zin-st) 8)
                  (fn-zin-freshp fn-zin-st)
                  (fn-zin-lit-ready-p fn-zin-st fn-zin-tab))
             (equal (fn-pwz-action-sequence count fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                    (mv nil (mv-nth 1 batch) (mv-nth 2 batch) fn-zin-tab (mv-nth 3 batch)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-pwz-canonical-literal-batch-is-action-sequence
                            (room (1- room))
                            (fn-zin-st (mv-nth 1 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
                            (fn-zin-win (mv-nth 2 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
                            (fn-zin-tab (mv-nth 3 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
                            (fn-zin-out (mv-nth 4 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
                 (:instance fn-pwz-literal-first-action-canonical))
           :in-theory (e/d (fn-pwz-action-sequence fn-zin-freshp)
                           (fn-zin-act fn-zin-act-counts fn-zin-lits fn-zin-lits-out-free
                            fn-oct-update fn-oct-snoc fn-pwz-literal-canonical-state-p
                            fn-pwz-literal-canonical-state-unfolds)))))

(defthm fn-pwz-actual-ready-literal-step-is-action-trajectory
  (implies (and (posp room)
                (equal (fn-zin-mode fn-zin-st) 8)
                (fn-zin-freshp fn-zin-st)
                (fn-zin-lit-ready-p fn-zin-st fn-zin-tab))
           (equal (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                  (fn-pwz-action-sequence
                   (car (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
                   fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-pwz-actual-ready-literal-batch-is-action-trajectory))
           :in-theory (e/d (fn-zin-step)
                           (fn-zin-lits fn-pwz-action-sequence
                            fn-pwz-literal-batch-first-action-and-tail-rewrite
                            fn-pwz-actual-literal-first-action-effects-rewrite)))))
