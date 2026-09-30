; Actual basic-loop charge trajectory through the cold compressed controller.

; Proof-only carry: no new hosted decoder, data ceiling, native tariff, or activation.

(in-package "ACL2")

(include-book "decoded-window-step-trajectory")
(include-book "extent-window-compressed-output")

(defun fn-pwz-progress-statep (fn-zin-st)
  (declare (xargs :stobjs fn-zin-st :guard t))
  (let ((mode (fn-zin-mode fn-zin-st)) (n (fn-zin-n fn-zin-st))
        (sym (fn-zin-sym fn-zin-st)))
    (and (implies (equal mode 9) (<= sym 28))
         (implies (or (equal mode 10) (equal mode 11))
                  (and (posp n) (<= n 258)))
         (implies (equal mode 11) (<= sym 29))
         (implies (equal mode 12) (<= n 258)))))

(defun fn-pwz-progress-phase (fn-zin-st)
  (declare (xargs :stobjs fn-zin-st :guard t))
  (let ((mode (fn-zin-mode fn-zin-st)) (n (fn-zin-n fn-zin-st)))
    (case mode
      (0 -2) (1 0) (2 -1) (3 (if (zp n) -1 -2))
      (4 0) (5 1) (6 0) (7 0) (8 -1)
      (9 (- 2 (fn-zin-lbase-of (fn-zin-sym fn-zin-st))))
      ((10 11) (- 1 n)) (12 (- n)) (13 -2)
      (otherwise 0))))

(local
 (defthm fn-pwz-length-index-extra-envelope
   (implies (and (natp index) (<= index 28) (natp extra)
                 (< extra (expt 2 (fn-zin-lext-of index))))
            (and (<= 3 (+ (fn-zin-lbase-of index) extra))
                 (<= (+ (fn-zin-lbase-of index) extra) 258)))
   :rule-classes nil
   :hints (("Goal" :cases ((equal index 0) (equal index 1) (equal index 2)
                           (equal index 3) (equal index 4) (equal index 5)
                           (equal index 6) (equal index 7) (equal index 8)
                           (equal index 9) (equal index 10) (equal index 11)
                           (equal index 12) (equal index 13) (equal index 14)
                           (equal index 15) (equal index 16) (equal index 17)
                           (equal index 18) (equal index 19) (equal index 20)
                           (equal index 21) (equal index 22) (equal index 23)
                           (equal index 24) (equal index 25) (equal index 26)
                           (equal index 27) (equal index 28))
            :in-theory (enable fn-zin-lbase-of fn-zin-lext-of)))))

(local
 (defthm fn-pwz-take-keeps-progress-fields
   (let ((s (mv-nth 1 (fn-zin-take k fn-zin-st))))
     (and (equal (fn-zin-mode s) (fn-zin-mode fn-zin-st))
          (equal (fn-zin-n s) (fn-zin-n fn-zin-st))
          (equal (fn-zin-sym s) (fn-zin-sym fn-zin-st))))
   :hints (("Goal" :in-theory (enable fn-zin-take)))))

(local
 (defthm fn-pwz-decode-bit-keeps-progress-fields
   (let ((s (mv-nth 2 (fn-zin-decode-bit tb fn-zin-st fn-zin-tab))))
     (and (equal (fn-zin-mode s) (fn-zin-mode fn-zin-st))
          (equal (fn-zin-n s) (fn-zin-n fn-zin-st))
          (equal (fn-zin-sym s) (fn-zin-sym fn-zin-st))))
   :hints (("Goal" :in-theory (enable fn-zin-decode-bit)))))

(local
 (defthm fn-pwz-pull-keeps-progress
   (let ((s (fn-zin-pull ip fn-zin-st fn-octets)))
     (and (equal (fn-pwz-progress-statep s) (fn-pwz-progress-statep fn-zin-st))
          (equal (fn-pwz-progress-phase s) (fn-pwz-progress-phase fn-zin-st))))
   :hints (("Goal" :in-theory (enable fn-zin-pull fn-pwz-progress-statep fn-pwz-progress-phase)))))

(local
 (defthm fn-pwz-act-keeps-progress-state
   (implies (fn-pwz-progress-statep fn-zin-st)
            (fn-pwz-progress-statep
             (mv-nth 1 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-pwz-length-index-extra-envelope
                   (index (fn-zin-sym fn-zin-st))
                   (extra (car (fn-zin-take (fn-zin-lext-of (fn-zin-sym fn-zin-st)) fn-zin-st)))))
            :in-theory (e/d (fn-zin-act fn-pwz-progress-statep
                             fn-zin-decode-reset fn-zin-block-end fn-zin-emit)
                            (fn-zin-take fn-zin-decode-bit fn-zin-lowb fn-zin-highb
                             fn-zin-construct fn-zin-fill fn-zin-dynamic-tables
                             fn-zin-fixed-tables fn-zin-zero-cl fn-zin-lbase-of
                             fn-zin-lext-of fn-zin-dbase-of fn-zin-dext-of))))))

(local
 (defthm fn-pwz-reset-loop-below-progress
   (implies (and (natp i) (natp j) (< j i))
            (equal (fn-zin-fld j (fn-zin-reset-loop i fn-zin-st)) (fn-zin-fld j fn-zin-st)))
   :hints (("Goal" :induct (fn-zin-reset-loop i fn-zin-st)
            :in-theory (enable fn-zin-reset-loop)))))

(local
 (defthm fn-pwz-reset-loop-progress-fields
   (implies (and (natp i) (natp j) (<= i j) (< j 18))
            (equal (fn-zin-fld j (fn-zin-reset-loop i fn-zin-st)) 0))
   :hints (("Goal" :induct (fn-zin-reset-loop i fn-zin-st)
            :in-theory (enable fn-zin-reset-loop)))))

(local
 (defthm fn-pwz-initialize-establishes-progress
   (let ((s (mv-nth 0 (fn-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
     (and (fn-pwz-progress-statep s)
          (equal (fn-pwz-progress-phase s) -2)))
   :hints (("Goal" :in-theory (enable fn-pzw-initialize fn-zin-reset fn-zin-reset-loop
                                     fn-pwz-progress-statep fn-pwz-progress-phase)))))

(local
 (defthm fn-pwz-progress-phase-lower-bound
   (implies (fn-pwz-progress-statep fn-zin-st)
            (<= -258 (fn-pwz-progress-phase fn-zin-st)))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance fn-pwz-length-index-extra-envelope
                                    (index (fn-zin-sym fn-zin-st)) (extra 0)))
            :in-theory (e/d (fn-pwz-progress-phase fn-pwz-progress-statep)
                            (fn-zin-lbase-of fn-zin-lext-of))))))

(local
 (defthm fn-pwz-action-sequence-keeps-progress-state
   (implies (fn-pwz-progress-statep fn-zin-st)
            (fn-pwz-progress-statep
             (mv-nth 1 (fn-pwz-action-sequence k fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
   :hints (("Goal" :induct (fn-pwz-action-sequence k fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
            :in-theory (e/d (fn-pwz-action-sequence) (fn-pwz-progress-statep))))))

(local
 (defthm fn-pwz-step-keeps-progress-state
   (implies (and (posp room) (fn-pwz-progress-statep fn-zin-st))
            (fn-pwz-progress-statep
             (mv-nth 1 (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
   :hints (("Goal" :use ((:instance fn-pwz-actual-step-is-action-trajectory))
            :in-theory (disable fn-zin-step fn-pwz-action-sequence fn-pwz-progress-statep)))))

(local
 (defthm fn-pwz-walk-consumes-bit
   (implies (posp nbits)
            (< (mv-nth 3 (fn-zin-walk tb bits nbits code first index len fn-zin-tab)) nbits))
   :rule-classes :linear
   :hints (("Goal" :induct (fn-zin-walk tb bits nbits code first index len fn-zin-tab)
            :in-theory (enable fn-zin-walk)))))

(local
 (defthm fn-pwz-walk-nbits-natp
   (natp (mv-nth 3 (fn-zin-walk tb bits nbits code first index len fn-zin-tab)))
   :rule-classes :type-prescription
   :hints (("Goal" :induct (fn-zin-walk tb bits nbits code first index len fn-zin-tab)
            :in-theory (enable fn-zin-walk)))))

(local
 (defthm fn-pwz-decode-bit-consumes-bit
   (implies (posp (fn-zin-nbits fn-zin-st))
            (< (fn-zin-nbits (mv-nth 2 (fn-zin-decode-bit tb fn-zin-st fn-zin-tab)))
               (fn-zin-nbits fn-zin-st)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (e/d (fn-zin-decode-bit) (fn-zin-walk fn-zin-lowb fn-zin-highb))))))

(local
 (defthm fn-pwz-take-consumes-exact-bits
   (implies (and (natp k) (<= k (fn-zin-nbits fn-zin-st)))
            (equal (fn-zin-nbits (mv-nth 1 (fn-zin-take k fn-zin-st)))
                   (- (fn-zin-nbits fn-zin-st) k)))
   :hints (("Goal" :in-theory (enable fn-zin-take)))))

(local
 (defthm fn-pwz-take-keeps-tout
   (equal (fn-zin-tout (mv-nth 1 (fn-zin-take k fn-zin-st))) (fn-zin-tout fn-zin-st))
   :hints (("Goal" :in-theory (enable fn-zin-take)))))

(local
 (defthm fn-pwz-take-nbits-nonincreasing
   (<= (fn-zin-nbits (mv-nth 1 (fn-zin-take k fn-zin-st))) (fn-zin-nbits fn-zin-st))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-zin-take)))))

(local
 (defthm fn-pwz-decode-bit-keeps-tout
   (equal (fn-zin-tout (mv-nth 2 (fn-zin-decode-bit tb fn-zin-st fn-zin-tab))) (fn-zin-tout fn-zin-st))
   :hints (("Goal" :in-theory (enable fn-zin-decode-bit)))))

(local
 (defthm fn-pwz-length-base-lower-bound
   (implies (and (natp index) (<= index 28))
            (<= 3 (fn-zin-lbase-of index)))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance fn-pwz-length-index-extra-envelope (extra 0)))
            :in-theory (enable fn-zin-lbase-of fn-zin-lext-of)))))

(local
 (defthm fn-pwz-act-success-charged-progress
   (implies (and (fn-pwz-progress-statep fn-zin-st)
                 (<= (fn-zin-need fn-zin-st) (fn-zin-nbits fn-zin-st))
                 (not (mv-nth 0 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
            (let ((s (mv-nth 1 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
              (<= (+ 1 (fn-pwz-progress-phase s))
                  (+ (fn-pwz-progress-phase fn-zin-st)
                     (- (fn-zin-nbits fn-zin-st) (fn-zin-nbits s))
                     (* 2 (- (fn-zin-tout s) (fn-zin-tout fn-zin-st)))))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-zin-act fn-pwz-progress-phase fn-pwz-progress-statep
                             fn-zin-need fn-zin-decode-reset fn-zin-block-end fn-zin-emit)
                            (fn-zin-take fn-zin-decode-bit fn-zin-lowb fn-zin-highb
                             fn-zin-construct fn-zin-fill fn-zin-dynamic-tables
                             fn-zin-fixed-tables fn-zin-zero-cl fn-zin-lbase-of
                             fn-zin-lext-of fn-zin-dbase-of fn-zin-dext-of))))))

(local
 (defthm fn-pwz-literal-loop-nbits-nonincreasing
   (implies (natp nbits)
            (<= (mv-nth 1 (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out)) nbits))
   :rule-classes :linear
   :hints (("Goal" :induct (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out)
            :in-theory (enable fn-zin-lit-loop)))))

(local
 (defthm fn-pwz-literal-loop-tout-monotone-progress
   (implies (and (natp tout) (natp nbits))
            (<= tout (mv-nth 3 (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out))))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance fn-zin-lit-loop-counts))
            :in-theory (disable fn-zin-lit-loop-counts)))))

(local
 (defthm fn-pwz-ready-literal-batch-positive-progress
   (implies (and (posp room) (fn-zin-lit-ready-p fn-zin-st fn-zin-tab))
            (< 0 (car (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :expand ((:free (bits nbits w tout limit tab win out)
                             (fn-zin-lit-loop room bits nbits w tout limit tab win out)))
            :in-theory (e/d (fn-zin-lits fn-zin-lit-ready-p) (fn-zin-lit-loop-out-free))))))

(local
 (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm fn-pwz-step-success-charged-progress
   (implies (and (posp room) (fn-pwz-progress-statep fn-zin-st)
                 (<= (fn-zin-need fn-zin-st) (fn-zin-nbits fn-zin-st))
                 (not (mv-nth 0 (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
            (let ((s (mv-nth 1 (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
              (<= (+ 1 (fn-pwz-progress-phase s))
                  (+ (fn-pwz-progress-phase fn-zin-st)
                     (- (fn-zin-nbits fn-zin-st) (fn-zin-nbits s))
                     (* 2 (- (fn-zin-tout s) (fn-zin-tout fn-zin-st)))))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-pwz-act-success-charged-progress)
                  (:instance fn-pwz-ready-literal-batch-positive-progress))
            :in-theory (e/d (fn-zin-step fn-zin-match fn-zin-lits fn-pwz-progress-phase)
                            (fn-zin-act fn-zin-copy fn-zin-lit-loop fn-zin-lit-ready-p
                             fn-zin-freshp fn-zin-need fn-pwz-progress-statep
                             fn-zin-lbase-of fn-zin-lits-counts fn-zin-lit-loop-counts))))))

(local
 (defthm fn-pwz-pull-progress-counters
   (let ((s (fn-zin-pull ip fn-zin-st fn-octets)))
     (and (equal (fn-zin-nbits s) (+ 8 (fn-zin-nbits fn-zin-st)))
          (equal (fn-zin-tout s) (fn-zin-tout fn-zin-st))))
   :hints (("Goal" :in-theory (enable fn-zin-pull)))))

(local
 (defthm fn-pwz-loop-nonrefusal-charged-progress
   (implies (and (natp b) (natp ip) (fn-pwz-progress-statep fn-zin-st)
                 (not (consp (mv-nth 0 (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))
            (let* ((r (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
                   (s (mv-nth 3 r)))
              (and (fn-pwz-progress-statep s)
                   (<= (- b (mv-nth 1 r))
                       (+ (* 9 (- (mv-nth 2 r) ip))
                          (* 2 (- (fn-zin-tout s) (fn-zin-tout fn-zin-st)))
                          (- (fn-pwz-progress-phase fn-zin-st) (fn-pwz-progress-phase s))
                          (- (fn-zin-nbits fn-zin-st) (fn-zin-nbits s)))))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
            :in-theory (e/d (fn-zin-loop)
                            ( fn-zin-step fn-zin-pull fn-pwz-progress-statep fn-pwz-progress-phase
                             fn-zin-loop-counts fn-zin-act fn-zin-need fn-zin-out-len))
            :expand ((fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
           ("Subgoal *1/6" :use ((:instance fn-pwz-step-success-charged-progress
                                  (room (- (nfix lim) (fn-zin-out-len fn-zin-out)))))))))

(local
 (defthm fn-pwz-act-tout-nondecreasing
   (<= (fn-zin-tout fn-zin-st)
       (fn-zin-tout (mv-nth 1 (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
   :rule-classes :linear
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-zin-act fn-zin-emit fn-zin-block-end fn-zin-decode-reset)
                            (fn-zin-act-counts fn-zin-take fn-zin-decode-bit fn-zin-lowb fn-zin-highb
                             fn-zin-fill fn-zin-construct fn-zin-dynamic-tables fn-zin-fixed-tables
                             fn-zin-zero-cl fn-zin-lbase-of fn-zin-lext-of fn-zin-dbase-of fn-zin-dext-of))))))

(local
 (defthm fn-pwz-step-tout-nondecreasing
   (<= (fn-zin-tout fn-zin-st)
       (fn-zin-tout (mv-nth 1 (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
   :rule-classes :linear
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-zin-step fn-zin-match fn-zin-lits)
                            (fn-zin-act fn-zin-act-counts fn-zin-step-counts fn-zin-lits-counts fn-zin-lit-loop-counts))))))

(local
 (defthm fn-pwz-loop-all-outcomes-charge-bound
   (implies (and (natp b) (natp ip) (fn-pwz-progress-statep fn-zin-st))
            (let* ((r (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
                   (s (mv-nth 3 r)))
              (and (fn-pwz-progress-statep s)
                   (<= (- b (mv-nth 1 r))
                       (+ (* 9 (- (mv-nth 2 r) ip))
                          (* 2 (- (fn-zin-tout s) (fn-zin-tout fn-zin-st)))
                          (fn-pwz-progress-phase fn-zin-st)
                          (fn-zin-nbits fn-zin-st) 259)))))
   :rule-classes nil
   :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
            :in-theory (e/d (fn-zin-loop)
                            (fn-zin-step fn-zin-pull fn-pwz-progress-statep fn-pwz-progress-phase
                             fn-zin-loop-counts fn-zin-step-counts fn-zin-act fn-zin-need fn-zin-out-len)))
           ("Subgoal *1/6" :use ((:instance fn-pwz-step-success-charged-progress
                                  (room (- (nfix lim) (fn-zin-out-len fn-zin-out)))))))))

(local
 (defthm fn-pwz-credit-keeps-progress-coordinates
   (let ((s (fn-zin-set 7 credit fn-zin-st)))
     (and (equal (fn-pwz-progress-statep s) (fn-pwz-progress-statep fn-zin-st))
          (equal (fn-pwz-progress-phase s) (fn-pwz-progress-phase fn-zin-st))
          (equal (fn-zin-nbits s) (fn-zin-nbits fn-zin-st))
          (equal (fn-zin-tout s) (fn-zin-tout fn-zin-st))))
   :hints (("Goal" :in-theory (enable fn-pwz-progress-statep fn-pwz-progress-phase)))))

(local
 (defthm fn-pwz-stored-chunk-nonrefusal-charged-progress
   (implies (and (natp start) (fn-pwz-progress-statep fn-zin-st)
                 (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab)
                 (not (consp (mv-nth 0 (fn-pzw-stored-chunk requested remaining start end compressed expected
                                                         fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))
            (let* ((r (fn-pzw-stored-chunk requested remaining start end compressed expected
                                          fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
                   (s (mv-nth 3 r)))
              (and (fn-pwz-progress-statep s)
                   (<= (- (fn-pzw-quantum requested remaining) (mv-nth 1 r))
                       (+ (* 9 (- (mv-nth 2 r) start))
                          (* 2 (- (fn-zin-tout s) (fn-zin-tout fn-zin-st)))
                          (- (fn-pwz-progress-phase fn-zin-st) (fn-pwz-progress-phase s))
                          (- (fn-zin-nbits fn-zin-st) (fn-zin-nbits s)))))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-pwz-loop-nonrefusal-charged-progress
                           (b (fn-pzw-quantum requested remaining)) (ip start)
                           (lim (fn-pzw-room (min (nfix expected) (fn-pzw-stored-allowance compressed))
                                              (fn-zin-tout fn-zin-st)))
                           (fn-zin-st (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st))
                           (fn-zin-out nil)))
            :in-theory (e/d (fn-pzw-stored-chunk fn-pzw-chunk fn-zin-feed)
                            (fn-zin-loop fn-zin-loop-counts fn-pzw-chunk-is-resumable-run
                             fn-pzw-stored-chunk-is-resumable-run fn-pzw-room fn-pzw-quantum
                             fn-pzw-stored-allowance min nfix fn-pwz-progress-statep fn-pwz-progress-phase))))))

(local
 (defthm fn-pwz-loop-returned-budget-bounds
   (implies (natp b)
            (let ((left (mv-nth 1 (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
              (and (natp left) (<= left b))))
   :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
            :in-theory (e/d (fn-zin-loop) (fn-zin-step fn-zin-pull fn-zin-loop-counts))))))

(local
 (defthm fn-pwz-stored-chunk-returned-budget-bounds
   (implies (and (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab))
            (let ((left (mv-nth 1 (fn-pzw-stored-chunk requested remaining start end compressed expected
                                                      fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
              (and (natp left) (<= left (fn-pzw-quantum requested remaining)))))
   :hints (("Goal" :in-theory (e/d (fn-pzw-stored-chunk fn-pzw-chunk fn-zin-feed fn-pzw-quantum)
                            (fn-zin-loop fn-zin-loop-counts fn-pzw-chunk-is-resumable-run
                             fn-pzw-stored-chunk-is-resumable-run fn-pzw-room fn-pzw-stored-allowance min nfix))))))

(local
 (defthm fn-pwz-stored-chunk-real-input-count
   (implies (and (natp start) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab))
            (let* ((r (fn-pzw-stored-chunk requested remaining start end compressed expected
                                          fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
              (equal (fn-zin-tin (mv-nth 3 r))
                     (+ (fn-zin-tin fn-zin-st) (- (mv-nth 2 r) start)))))
   :hints (("Goal" :use ((:instance fn-zin-loop-counts
                           (b (fn-pzw-quantum requested remaining)) (ip start)
                           (lim (fn-pzw-room (min (nfix expected) (fn-pzw-stored-allowance compressed))
                                              (fn-zin-tout fn-zin-st)))
                           (fn-zin-st (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st))
                           (fn-zin-out nil)))
            :in-theory (e/d (fn-pzw-stored-chunk fn-pzw-chunk fn-zin-feed)
                            (fn-zin-loop fn-zin-loop-counts fn-pzw-chunk-is-resumable-run
                             fn-pzw-stored-chunk-is-resumable-run fn-pzw-room fn-pzw-quantum
                             fn-pzw-stored-allowance min))))))

(defun fn-pwz-budget-carryp (compressed expected remaining fn-zin-st)
  (declare (xargs :stobjs fn-zin-st :guard t))
  (and (natp remaining) (fn-pwz-progress-statep fn-zin-st)
       (<= (+ (- (fn-pzd-budget compressed expected) remaining)
              (fn-pwz-progress-phase fn-zin-st) (fn-zin-nbits fn-zin-st))
           (- (+ (* 9 (fn-zin-tin fn-zin-st)) (* 2 (fn-zin-tout fn-zin-st))) 2))))

(local
 (defthm fn-pwz-stored-chunk-preserves-budget-carry
   (implies (and (natp start) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab)
                 (fn-pwz-budget-carryp compressed expected remaining fn-zin-st)
                 (not (consp (mv-nth 0 (fn-pzw-stored-chunk requested remaining start end compressed expected
                                                         fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))
            (let* ((r (fn-pzw-stored-chunk requested remaining start end compressed expected
                                          fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
              (fn-pwz-budget-carryp compressed expected
                                   (fn-pzw-budget-left requested remaining (mv-nth 1 r)) (mv-nth 3 r))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-pwz-stored-chunk-nonrefusal-charged-progress)
                          (:instance fn-pwz-stored-chunk-returned-budget-bounds)
                          (:instance fn-pwz-stored-chunk-real-input-count))
            :in-theory (e/d (fn-pwz-budget-carryp fn-pzw-budget-left fn-pzw-quantum)
                            (fn-pwz-stored-chunk-returned-budget-bounds fn-pzw-stored-chunk-counts-real-input fn-pzw-stored-chunk fn-pzd-budget fn-pwz-progress-statep
                             fn-pwz-progress-phase fn-pwz-stored-chunk-real-input-count))))))

(defthm fn-pwz-budget-carry-has-positive-remaining
  (implies (and (natp compressed) (natp expected)
                (fn-pwz-budget-carryp compressed expected remaining fn-zin-st)
                (<= (fn-zin-tin fn-zin-st) compressed)
                (<= (fn-zin-tout fn-zin-st) (+ 1 expected)))
           (and (posp remaining) (<= (+ 3838 (* 7 compressed)) remaining)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-pwz-budget-carryp fn-pzd-budget)
                                   (fn-pwz-progress-statep fn-pwz-progress-phase)))))

(local
 (defthm fn-pwz-initialize-establishes-budget-carry
   (let ((s (mv-nth 0 (fn-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
     (fn-pwz-budget-carryp compressed expected (fn-pzd-budget compressed expected) s))
   :hints (("Goal" :in-theory (e/d (fn-pwz-budget-carryp fn-pzw-initialize fn-zin-reset fn-pzd-budget
                                     fn-pwz-progress-statep fn-pwz-progress-phase)
                                    (fn-zin-reset-loop))))))

(local
 (defthm fn-pwz-actual-codec-preserves-budget-carry
   (implies (and (eq (nth 0 z) :codec) (natp (nth 6 z)) (natp (nth 7 z))
                 (<= (nth 6 z) (nth 7 z)) (<= (- (nth 7 z) (nth 6 z)) 64)
                 (<= (nth 7 z) (fn-octets-len fn-octets))
                 (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab)
                 (fn-pwz-budget-carryp (nth 12 (nth 1 z)) (nth 2 z) (nth 5 z) fn-zin-st)
                 (not (consp (nth 8 (mv-nth 1 (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))))))
            (let* ((r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))
                   (next (mv-nth 1 r)))
              (fn-pwz-budget-carryp (nth 12 (nth 1 next)) (nth 2 next) (nth 5 next) (mv-nth 2 r))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-pwz-stored-chunk-preserves-budget-carry
                           (requested 1024) (remaining (nth 5 z)) (start (nth 6 z)) (end (nth 7 z))
                           (compressed (nth 12 (nth 1 z))) (expected (nth 2 z))))
            :in-theory (e/d (fn-ewz-codec-tick fn-ewz-state nth)
                            (fn-pzw-stored-chunk fn-pzw-stored-chunk-is-resumable-run fn-pzw-chunk-is-resumable-run
                             fn-zin-loop fn-zin-run fn-zin-loop-counts fn-pzw-quantum fn-pzw-room
                             fn-pzw-stored-allowance min nfix fn-pzw-select fn-ewb-copy fn-pzw-budget-left
                             fn-pzw-stored-decision fn-ewz-compressed-completep fn-ewz-decision-mode
                             fn-pwz-budget-carryp))))))

(defthm fn-pwz-actual-compressed-begin-establishes-budget-carry
  (let* ((r (fn-ewz-begin file eoff elen poff compressed decoded offset ticket incarnation lease expected dict
                         pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
         (z (mv-nth 0 r)))
    (fn-pwz-budget-carryp compressed decoded (nth 5 z) (mv-nth 2 r)))
  :hints (("Goal" :use ((:instance fn-pwz-initialize-establishes-budget-carry (expected decoded)))
           :in-theory (e/d (fn-ewz-begin fn-ewz-state nth)
                           (fn-pzw-initialize fn-ews-begin fn-pzd-budget fn-pwz-budget-carryp)))))

(local
 (defthm fn-pwz-raw-plan-phase-keeps-compressed-length-by-definition
   (equal (nth 12 (fn-ewp-with-phase-pos phase pos s)) (nth 12 s))
   :hints (("Goal" :in-theory (enable fn-ewp-with-phase-pos fn-ewp-state nth)))))

(local
 (defthm fn-pwz-raw-plan-complete-keeps-compressed-length
   (equal (nth 12 (mv-nth 1 (fn-ewp-complete-read effect got verdict s))) (nth 12 s))
   :hints (("Goal" :in-theory (enable fn-ewp-complete-read)))))

(local
 (defthm fn-pwz-raw-plan-finish-keeps-compressed-length
   (equal (nth 12 (mv-nth 1 (fn-ewp-finish read digest s))) (nth 12 s))
   :hints (("Goal" :in-theory (enable fn-ewp-finish)))))

(local
 (defthm fn-pwz-protected-read-keeps-compressed-length
   (equal (nth 12 (mv-nth 1 (fn-ews-read effect io-status s fn-octets pgs-digest-state fn-ew-buffer))) (nth 12 s))
   :hints (("Goal" :in-theory (e/d (fn-ews-read) (fn-ewp-finish fn-ewp-complete-read fn-b3x-words fn-ewb-capture pgs-dcb-step pgs-dcb-result-octets))))))

(local
 (defthm fn-pwz-protected-tick-keeps-compressed-length
   (equal (nth 12 (mv-nth 1 (fn-ews-tick s pgs-digest-state))) (nth 12 s))
   :hints (("Goal" :in-theory (e/d (fn-ews-tick) (pgs-dcb-step fn-ews-boundp fn-ews-effect))))))

(defthm fn-pwz-actual-compressed-read-preserves-budget-carry
  (implies (fn-pwz-budget-carryp (nth 12 (nth 1 z)) (nth 2 z) (nth 5 z) fn-zin-st)
           (let ((next (mv-nth 1 (fn-ewz-read effect io-status z fn-octets pgs-digest-state fn-ew-buffer))))
             (fn-pwz-budget-carryp (nth 12 (nth 1 next)) (nth 2 next) (nth 5 next) fn-zin-st)))
  :hints (("Goal" :in-theory (e/d (fn-ewz-read fn-ewz-state nth)
                                   (fn-pwz-budget-carryp fn-ews-read fn-ewz-effect fn-ewp-payload-span)))))

(defthm fn-pwz-actual-compressed-hash-tick-preserves-budget-carry
  (implies (fn-pwz-budget-carryp (nth 12 (nth 1 z)) (nth 2 z) (nth 5 z) fn-zin-st)
           (let ((next (mv-nth 1 (fn-ewz-hash-tick z pgs-digest-state fn-zin-st))))
             (fn-pwz-budget-carryp (nth 12 (nth 1 next)) (nth 2 next) (nth 5 next) fn-zin-st)))
  :hints (("Goal" :in-theory (e/d (fn-ewz-hash-tick)
                                   (fn-pwz-budget-carryp fn-ews-tick fn-ewz-compressed-completep fn-pzw-stored-decision fn-ewz-decision-mode)))))

(local
 (defthm fn-pwz-actual-codec-budget-carry
   (implies (and (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab)
                 (fn-pwz-budget-carryp (nth 12 (nth 1 z)) (nth 2 z) (nth 5 z) fn-zin-st)
                 (not (consp (nth 8 (mv-nth 1 (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))))))
            (let* ((r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))
                   (next (mv-nth 1 r)))
              (fn-pwz-budget-carryp (nth 12 (nth 1 next)) (nth 2 next) (nth 5 next) (mv-nth 2 r))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-pwz-stored-chunk-preserves-budget-carry
                           (requested 1024) (remaining (nth 5 z)) (start (nth 6 z)) (end (nth 7 z))
                           (compressed (nth 12 (nth 1 z))) (expected (nth 2 z))))
            :in-theory (e/d (fn-ewz-codec-tick fn-ewz-state nth)
                            (fn-pzw-stored-chunk fn-pzw-stored-chunk-is-resumable-run fn-pzw-chunk-is-resumable-run
                             fn-zin-loop fn-zin-run fn-zin-loop-counts fn-pzw-quantum fn-pzw-room
                             fn-pzw-stored-allowance min nfix fn-pzw-select fn-ewb-copy fn-pzw-budget-left
                             fn-pzw-stored-decision fn-ewz-compressed-completep fn-ewz-decision-mode
                             fn-pwz-budget-carryp))))))

(local
 (defthm fn-pwz-stored-nonrefusal-implies-ready-buffers
   (implies (not (consp (mv-nth 0 (fn-pzw-stored-chunk requested remaining start end compressed expected
                                                    fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
            (and (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab)))
   :hints (("Goal" :in-theory (e/d (fn-pzw-stored-chunk fn-pzw-chunk fn-zin-feed)
                            (fn-zin-loop fn-zin-loop-counts fn-pzw-chunk-is-resumable-run
                             fn-pzw-stored-chunk-is-resumable-run fn-pzw-room fn-pzw-quantum
                             fn-pzw-stored-allowance min nfix))))))

(defthm fn-pwz-actual-codec-carries-budget
  (implies (and (fn-pwz-budget-carryp (nth 12 (nth 1 z)) (nth 2 z) (nth 5 z) fn-zin-st)
                (not (consp (nth 8 (mv-nth 1 (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))))))
           (let* ((r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))
                  (next (mv-nth 1 r)))
             (fn-pwz-budget-carryp (nth 12 (nth 1 next)) (nth 2 next) (nth 5 next) (mv-nth 2 r))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-pwz-stored-nonrefusal-implies-ready-buffers
                          (requested 1024) (remaining (nth 5 z)) (start (nth 6 z)) (end (nth 7 z))
                          (compressed (nth 12 (nth 1 z))) (expected (nth 2 z)))
                         (:instance fn-pwz-stored-chunk-preserves-budget-carry
                          (requested 1024) (remaining (nth 5 z)) (start (nth 6 z)) (end (nth 7 z))
                          (compressed (nth 12 (nth 1 z))) (expected (nth 2 z))))
           :in-theory (e/d (fn-ewz-codec-tick fn-ewz-state nth)
                           (fn-pwz-stored-nonrefusal-implies-ready-buffers fn-pzw-stored-chunk fn-pzw-stored-chunk-is-resumable-run fn-pzw-chunk-is-resumable-run
                            fn-zin-loop fn-zin-run fn-zin-loop-counts fn-pzw-quantum fn-pzw-room
                            fn-pzw-stored-allowance min nfix fn-pzw-select fn-ewb-copy fn-pzw-budget-left
                            fn-pzw-stored-decision fn-ewz-compressed-completep fn-ewz-decision-mode
                            fn-pwz-budget-carryp)))))

(defthm fn-pwz-actual-loop-charge-bound
  (implies (and (natp b) (fn-pwz-progress-statep fn-zin-st))
           (let* ((r (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
                  (s (mv-nth 3 r)))
             (and (fn-pwz-progress-statep s)
                  (<= (- b (mv-nth 1 r))
                      (+ (* 9 (- (mv-nth 2 r) ip))
                         (* 2 (- (fn-zin-tout s) (fn-zin-tout fn-zin-st)))
                         (fn-pwz-progress-phase fn-zin-st)
                         (fn-zin-nbits fn-zin-st) 259)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-zin-loop)
                           (fn-zin-step fn-zin-pull fn-pwz-progress-statep fn-pwz-progress-phase
                            fn-zin-loop-counts fn-zin-step-counts fn-zin-act fn-zin-need fn-zin-out-len)))
          ("Subgoal *1/6" :use ((:instance fn-pwz-step-success-charged-progress
                                 (room (- (nfix lim) (fn-zin-out-len fn-zin-out))))))))


; Joint carry over the actual controller's existing real-input and active
; output invariants. No caller supplies a claimed count or budget adequacy.
(defun fn-pwz-controller-budget-carryp (z fn-zin-st)
  (declare (xargs :stobjs fn-zin-st :guard (and (true-listp z) (true-listp (nth 1 z)))))
  (and (fn-ewz-input-invariantp z fn-zin-st)
       (fn-ewz-output-invariantp z fn-zin-st)
       (fn-pwz-budget-carryp (nth 12 (nth 1 z)) (nth 2 z) (nth 5 z) fn-zin-st)))

(local
 (defthm fn-pwz-raw-begin-keeps-compressed-length-by-definition
   (equal (nth 12 (car (fn-ews-begin file eoff elen poff plen offset ticket incarnation lease expected pgs-digest-state))) plen)
   :hints (("Goal" :in-theory (e/d (fn-ews-begin fn-ewp-begin fn-ewp-state nth)
                                    (pgs-dcb-begin fn-ews-capture))))))

(defthm fn-pwz-controller-begin-establishes-budget-carry
  (implies (natp poff)
           (let ((r (fn-ewz-begin file eoff elen poff compressed decoded offset ticket incarnation lease expected dict
                                 pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
             (fn-pwz-controller-budget-carryp (car r) (mv-nth 2 r))))
  :hints (("Goal" :in-theory (e/d (fn-pwz-controller-budget-carryp fn-ewz-begin fn-ewz-state nth)
                                   (fn-ewz-input-invariantp fn-ewz-output-invariantp fn-pwz-budget-carryp
                                    fn-pzw-initialize fn-ews-begin fn-pzd-budget))
           :use ((:instance fn-ewz-begin-establishes-input-invariant)
                 (:instance fn-ewz-begin-establishes-output-invariant)
                 (:instance fn-pwz-actual-compressed-begin-establishes-budget-carry)))))

(defthm fn-pwz-controller-codec-preserves-budget-carry
  (implies (and (fn-pwz-controller-budget-carryp z fn-zin-st)
                (not (consp (nth 8 (mv-nth 1 (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))))))
           (let ((r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)))
             (fn-pwz-controller-budget-carryp (mv-nth 1 r) (mv-nth 2 r))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-pwz-actual-codec-carries-budget))
           :in-theory (e/d (fn-pwz-controller-budget-carryp)
                           (fn-ewz-codec-tick fn-ewz-input-invariantp fn-ewz-output-invariantp fn-pwz-budget-carryp)))))

(defthm fn-pwz-controller-read-preserves-budget-carry
  (implies (fn-pwz-controller-budget-carryp z fn-zin-st)
           (fn-pwz-controller-budget-carryp
             (mv-nth 1 (fn-ewz-read effect io-status z fn-octets pgs-digest-state fn-ew-buffer)) fn-zin-st))
  :hints (("Goal" :in-theory (e/d (fn-pwz-controller-budget-carryp)
                                   (fn-ewz-read fn-ewz-input-invariantp fn-ewz-output-invariantp fn-pwz-budget-carryp)))))

(defthm fn-pwz-controller-hash-tick-preserves-budget-carry
  (implies (fn-pwz-controller-budget-carryp z fn-zin-st)
           (fn-pwz-controller-budget-carryp
             (mv-nth 1 (fn-ewz-hash-tick z pgs-digest-state fn-zin-st)) fn-zin-st))
  :hints (("Goal" :in-theory (e/d (fn-pwz-controller-budget-carryp)
                                   (fn-ewz-hash-tick fn-ewz-input-invariantp fn-ewz-output-invariantp fn-pwz-budget-carryp)))))

(defthm fn-pwz-active-controller-budget-remains-positive
  (implies (and (fn-pwz-controller-budget-carryp z fn-zin-st)
                (member-eq (nth 0 z) '(:scan :codec :drain :decoded)))
           (and (posp (nth 5 z))
                (<= (+ 3840 (* 7 (nth 12 (nth 1 z)))) (nth 5 z))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-ewz-input-invariant-bounds-real-input))
           :in-theory (e/d (fn-pwz-controller-budget-carryp fn-ewz-output-invariantp
                            fn-pwz-budget-carryp fn-pzd-budget fn-pzw-stored-admissiblep)
                           (fn-ewz-input-invariantp fn-pwz-progress-statep fn-pwz-progress-phase fn-pzw-stored-allowance)))))
