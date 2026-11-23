; Positioned seek over the overview range reader.
(in-package "ACL2")

(include-book "ribbon-range-proof")

(local
 (defthm fn2-range-bisection-width
  (implies (and (natp lo) (natp hi) (< lo hi) (equal mid (floor (+ lo hi) 2))
                (implies lower (and (natp n) (<= mid n) (< n hi))))
           (<= (- (if lower hi mid) (if lower (1+ n) lo)) (floor (- hi lo) 2)))
  :rule-classes nil
  :hints (("Goal" :cases ((< (floor (+ lo hi) 2) (/ (+ lo hi) 2)))))))

(local
 (defthm fn2-overview-admitted-union
  (let* ((key *fn2-overview-range-key*) (es (fn2-range-union-spec key sources nil)))
   (implies (fn2-range-inputp *fn2-overview-entry* key sources budget)
            (and (fn2-range-natural-keysp es) (fn2-run-sorted-spec key es))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-overview-union-natural-keys (layout *fn2-overview-entry*)
                                   (key *fn2-overview-range-key*) (acc nil)))
           :in-theory (disable fn2-range-union-spec fn2-range-listsp fn2-overview-union-natural-keys)))))
(local
 (defthm fn2-range-midpoint-domain
  (implies (and (natp lo) (unsigned-byte-p 60 hi) (< lo hi))
           (let ((mid (floor (+ lo hi) 2)))
             (and (natp mid) (<= lo mid) (< mid hi))))
  :rule-classes nil))
(local
 (defthm fn2-range-below-upper-fits
  (implies (and (unsigned-byte-p 60 hi) (natp n) (< n hi)) (unsigned-byte-p 60 (+ 1 n)))
  :rule-classes nil))
(local
 (defthm fn2-range-seek-narrowing-step
  (let ((phase (fn2-seeks-phase k s)) (narrow (fn2-seek-narrow k code s r f)))
    (implies (and (natp k) (< k (fn2-seeks-rows s))
                  (if (eq code :entry) (equal phase *fn2-seek-phase-entry*)
                    (and (eq code :end) (equal phase *fn2-seek-phase-end*))))
             (equal (fn2-seek-step k budget s r rs ov ix runs curs paths cache f pool)
                    (list (mv-nth 0 narrow) (mv-nth 1 narrow) r rs curs paths f))))
  :rule-classes nil
  :hints (("Goal" :cases ((eq code :entry))
           :in-theory (e/d (fn2-seek-step)
                           (fn2-seek-narrow fn2-seek-probe fn2-range-step fn2-seeks-phase fn2-seeks-rows))))))

(local
 (defthm fn2-range-seek-narrowing-state
  (let ((phase (fn2-seeks-phase k s)))
    (implies (and (natp k) (< k (fn2-seeks-rows s))
                  (if (eq code :entry) (equal phase *fn2-seek-phase-entry*)
                    (and (eq code :end) (equal phase *fn2-seek-phase-end*))))
             (equal (mv-nth 1 (fn2-seek-step k budget s r rs ov ix runs curs paths cache f pool))
                    (mv-nth 1 (fn2-seek-narrow k code s r f)))))
  :rule-classes nil
  :hints (("Goal" :use fn2-range-seek-narrowing-step
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(mv-nth car-cons cdr-cons (:e zp) (:e binary-+)))))))

(defthm fn2-overview-seek-step-width
 (let* ((g (fn2-seeks-g k s)) (out (fn2-ranges-out g r))
        (n (nfix (fn2-fields-value (+ 1 out) f)))
        (lo (fn2-seeks-lo k s)) (hi (fn2-seeks-hi k s)) (mid (fn2-seeks-mid k s))
        (phase (fn2-seeks-phase k s)) (entry (equal phase *fn2-seek-phase-entry*))
        (step (fn2-seek-step k budget s r rs ov ix runs curs paths cache f pool))
        (after (mv-nth 1 step)))
   (implies (and (natp k) (< k (fn2-seeks-rows s)) (natp g) (< g (fn2-ranges-rows r))
                 (or entry (equal phase *fn2-seek-phase-end*))
                 (implies entry
                          (and (equal (fn2-ranges-schema g r) 3) (equal (fn2-seeks-pfield k s) 3)
                               (natp out) (< (+ 3 out) (fn2-fields-rows f)) (<= mid n) (< n hi)))
                 (natp lo) (unsigned-byte-p 60 hi) (< lo hi) (equal mid (floor (+ lo hi) 2)))
            (and (equal (mv-nth 0 step) :more)
                 (equal (fn2-seeks-phase k after) *fn2-seek-phase-probe*)
                 (<= (- (fn2-seeks-hi k after) (fn2-seeks-lo k after)) (floor (- hi lo) 2)))))
 :rule-classes nil
 :hints (("Goal"
          :cases ((equal (fn2-seeks-phase k s) *fn2-seek-phase-entry*))
          :use ((:instance fn2-range-seek-narrowing-step
                 (code (if (equal (fn2-seeks-phase k s) *fn2-seek-phase-entry*) :entry :end)))
                (:instance fn2-overview-seek-narrow-bounds
                 (code (if (equal (fn2-seeks-phase k s) *fn2-seek-phase-entry*) :entry :end)))
                (:instance fn2-range-below-upper-fits (hi (fn2-seeks-hi k s))
                 (n (nfix (fn2-fields-value (+ 1 (fn2-ranges-out (fn2-seeks-g k s) r)) f))))
                (:instance fn2-range-bisection-width
                 (lo (fn2-seeks-lo k s)) (mid (fn2-seeks-mid k s)) (hi (fn2-seeks-hi k s))
                 (n (nfix (fn2-fields-value (+ 1 (fn2-ranges-out (fn2-seeks-g k s) r)) f)))
                 (lower (and (equal (fn2-seeks-phase k s) *fn2-seek-phase-entry*)
                             (<= (nfix (fn2-fields-value (+ 3 (fn2-ranges-out (fn2-seeks-g k s) r)) f))
                                 (fn2-seeks-after k s))))))
          :in-theory (union-theories (theory 'minimal-theory)
                        '(eq natp unsigned-byte-p integer-range-p (:e expt) mv-nth car-cons cdr-cons (:e mv-nth) (:e equal) (:e not)
                          (:e binary-+) (:e unary--) (:e nfix) (:t nfix))))))

(local
 (defthm fn2-overview-narrow-source-answer
  (let* ((g (fn2-seeks-g k s)) (out (fn2-ranges-out g r))
         (lo (fn2-seeks-lo k s)) (mid (fn2-seeks-mid k s)) (hi (fn2-seeks-hi k s))
         (p (fn2-seeks-after k s)) (key *fn2-overview-range-key*) (prefix (list group))
         (window (fn2-range-spec key sources (list group mid) (list group (1- hi)) nil 0))
         (row (car window)) (answer (fn2-range-seek-spec key sources prefix p hi 3))
         (code (if (consp window) :entry :end)) (res (fn2-seek-narrow k code s r f))
         (after (mv-nth 1 res)))
    (implies (and (fn2-range-inputp *fn2-overview-entry* key sources budget)
                  (fn2-range-monotonep key sources prefix 3)
                  (natp group) (natp k) (< k (fn2-seeks-rows s)) (natp g) (< g (fn2-ranges-rows r))
                  (equal (fn2-ranges-schema g r) 3) (equal (fn2-seeks-pfield k s) 3)
                  (natp out) (< (+ out 3) (fn2-fields-rows f))
                  (natp mid) (unsigned-byte-p 60 hi) (< mid hi) (<= lo answer)
                  (implies (consp window)
                           (and (equal (fn2-fields-value (+ out 1) f) (cadr row))
                                (equal (fn2-fields-value (+ out 3) f) (nth 3 row)))))
             (and (equal (mv-nth 0 res) :more)
                  (equal (fn2-range-seek-spec key sources prefix p (fn2-seeks-hi k after) 3) answer)
                  (<= (fn2-seeks-lo k after) answer))))
  :rule-classes nil
  :hints (("Goal" :use (fn2-overview-admitted-union
                        (:instance fn2-overview-seek-narrow-preserves-answer
                         (es (fn2-range-union-spec *fn2-overview-range-key* sources nil))))
           :in-theory (union-theories (theory 'minimal-theory)
              '(fn2-range-spec fn2-range-seek-spec fn2-overview-probe-window fn2-range-monotonep
                commutativity-of-+ (:e len) (:e equal) (:e not) (:e binary-+) (:e unary--) eq))))))

(local
 (defthm fn2-overview-first-in-source-window
  (let* ((key *fn2-overview-range-key*)
         (win (fn2-range-spec key sources (list group mid) (list group (1- hi)) nil 0)))
    (implies (and (fn2-range-inputp *fn2-overview-entry* key sources budget)
                  (natp group) (natp mid) (unsigned-byte-p 60 hi) (< mid hi) (consp win))
             (and (natp (cadar win)) (<= mid (cadar win)) (< (cadar win) hi))))
  :rule-classes nil
  :hints (("Goal" :use (fn2-overview-admitted-union
                        (:instance fn2-overview-probe-first-key
                         (es (fn2-range-union-spec *fn2-overview-range-key* sources nil))))
           :in-theory (union-theories (theory 'minimal-theory)
                       '(fn2-range-spec fn2-overview-probe-window natp unsigned-byte-p integer-range-p
                         (:e expt) (:e equal) (:e not)))))))

; Once the read phase has supplied the probe window's first row (or its end),
; the next concrete seek step preserves the stream answer and halves its interval.
(defthm fn2-overview-seek-step-interval
 (let* ((g (fn2-seeks-g k s)) (out (fn2-ranges-out g r))
        (lo (fn2-seeks-lo k s)) (mid (fn2-seeks-mid k s)) (hi (fn2-seeks-hi k s))
        (p (fn2-seeks-after k s)) (key *fn2-overview-range-key*) (prefix (list group))
        (window (fn2-range-spec key sources (list group mid) (list group (1- hi)) nil 0))
        (row (car window)) (answer (fn2-range-seek-spec key sources prefix p hi 3))
        (step (fn2-seek-step k budget s r rs ov ix runs curs paths cache f pool))
        (after (mv-nth 1 step)) (new-lo (fn2-seeks-lo k after)) (new-hi (fn2-seeks-hi k after)))
   (implies (and (fn2-range-inputp *fn2-overview-entry* key sources budget)
                 (fn2-range-monotonep key sources prefix 3)
                 (natp group) (natp k) (< k (fn2-seeks-rows s)) (natp g) (< g (fn2-ranges-rows r))
                 (equal (fn2-ranges-schema g r) 3) (equal (fn2-seeks-pfield k s) 3)
                 (natp out) (< (+ out 3) (fn2-fields-rows f))
                 (natp lo) (unsigned-byte-p 60 hi) (< lo hi)
                 (equal mid (floor (+ lo hi) 2)) (<= lo answer)
                 (equal (fn2-seeks-phase k s)
                        (if (consp window) *fn2-seek-phase-entry* *fn2-seek-phase-end*))
                 (implies (consp window)
                          (and (equal (fn2-fields-value (+ out 1) f) (cadr row))
                               (equal (fn2-fields-value (+ out 3) f) (nth 3 row)))))
            (and (equal (mv-nth 0 step) :more)
                 (equal (fn2-seeks-phase k after) *fn2-seek-phase-probe*)
                 (equal (fn2-range-seek-spec key sources prefix p new-hi 3) answer)
                 (<= new-lo answer)
                 (<= (- new-hi new-lo) (floor (- hi lo) 2)))))
 :rule-classes nil
 :hints
 (("Goal"
   :cases ((let ((after (mv-nth 1 (fn2-seek-step k budget s r rs ov ix runs curs paths cache f pool)))
                 (answer (fn2-range-seek-spec *fn2-overview-range-key* sources (list group)
                                              (fn2-seeks-after k s) (fn2-seeks-hi k s) 3)))
             (and (equal (fn2-range-seek-spec *fn2-overview-range-key* sources (list group)
                                              (fn2-seeks-after k s) (fn2-seeks-hi k after) 3)
                         answer)
                  (<= (fn2-seeks-lo k after) answer))))
   :in-theory (theory 'minimal-theory))
  ("Subgoal 2"
   :use (fn2-overview-narrow-source-answer
         (:instance fn2-range-seek-narrowing-state
          (code (if (consp (fn2-range-spec *fn2-overview-range-key* sources
                            (list group (fn2-seeks-mid k s)) (list group (1- (fn2-seeks-hi k s))) nil 0))
                    :entry :end)))
         (:instance fn2-range-midpoint-domain (lo (fn2-seeks-lo k s)) (hi (fn2-seeks-hi k s))))
   :cases ((consp (fn2-range-spec *fn2-overview-range-key* sources
                   (list group (fn2-seeks-mid k s)) (list group (1- (fn2-seeks-hi k s))) nil 0)))
   :in-theory (union-theories (theory 'minimal-theory) '(eq (:e equal) (:e not))))
  ("Subgoal 1"
   :use (fn2-overview-seek-step-width
         (:instance fn2-range-midpoint-domain (lo (fn2-seeks-lo k s)) (hi (fn2-seeks-hi k s)))
         (:instance fn2-overview-first-in-source-window (mid (fn2-seeks-mid k s)) (hi (fn2-seeks-hi k s))))
   :cases ((consp (fn2-range-spec *fn2-overview-range-key* sources
                   (list group (fn2-seeks-mid k s)) (list group (1- (fn2-seeks-hi k s))) nil 0)))
   :in-theory (union-theories (theory 'minimal-theory) '(nfix natp commutativity-of-+ (:e equal) (:e not))))))
