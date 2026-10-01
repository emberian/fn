; Full actual terminal charge includes (:refused :stream-ended), which the
; stored decision accepts as decoded completion. Logical scheduling only.
(in-package "ACL2")
(include-book "decoded-worker-controller-trajectory")
(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm fn-pwzt-credit-retains-progress-coordinates
  (let ((s (fn-zin-set 7 credit fn-zin-st)))
   (and (equal (fn-pwz-progress-statep s) (fn-pwz-progress-statep fn-zin-st))
        (equal (fn-pwz-progress-phase s) (fn-pwz-progress-phase fn-zin-st))
        (equal (fn-zin-nbits s) (fn-zin-nbits fn-zin-st))
        (equal (fn-zin-tout s) (fn-zin-tout fn-zin-st))))
  :hints (("Goal" :in-theory (enable fn-pwz-progress-statep fn-pwz-progress-phase)))))
(local
 (defthm fn-pwzt-loop-returned-budget-bounds
  (implies (natp b)
   (let ((left (mv-nth 1 (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
    (and (natp left) (<= left b))))
  :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (e/d (fn-zin-loop) (fn-zin-step fn-zin-pull fn-zin-loop-counts))))))
(local
 (defthm fn-pwzt-stored-returned-budget-bounds
  (implies (and (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab))
   (let ((left (mv-nth 1 (fn-pzw-stored-chunk requested remaining start end compressed expected
                                           fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
    (and (natp left) (<= left (fn-pzw-quantum requested remaining)))))
  :hints (("Goal" :in-theory (e/d (fn-pzw-stored-chunk fn-pzw-chunk fn-zin-feed fn-pzw-quantum)
    (fn-zin-loop fn-zin-loop-counts fn-pzw-chunk-is-resumable-run
     fn-pzw-stored-chunk-is-resumable-run fn-pzw-room fn-pzw-stored-allowance min nfix))))))
(local
 (defthm fn-pwzt-stored-all-outcomes-charged-progress
  (implies (and (natp start) (fn-pwz-progress-statep fn-zin-st)
                (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab))
   (let* ((r (fn-pzw-stored-chunk requested remaining start end compressed expected
                                 fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
          (s (mv-nth 3 r)))
    (and (fn-pwz-progress-statep s)
         (<= (- (fn-pzw-quantum requested remaining) (mv-nth 1 r))
             (+ (* 9 (- (mv-nth 2 r) start))
                (* 2 (- (fn-zin-tout s) (fn-zin-tout fn-zin-st)))
                (fn-pwz-progress-phase fn-zin-st) (fn-zin-nbits fn-zin-st) 259)))))
  :rule-classes nil
  :hints (("Goal"
   :use (:instance fn-pwz-actual-loop-charge-bound
          (b (fn-pzw-quantum requested remaining)) (ip start)
          (lim (fn-pzw-room (min (nfix expected) (fn-pzw-stored-allowance compressed)) (fn-zin-tout fn-zin-st)))
          (fn-zin-st (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st))
          (fn-zin-out nil))
   :in-theory (e/d (fn-pzw-stored-chunk fn-pzw-chunk fn-zin-feed)
     (fn-zin-loop fn-zin-loop-counts fn-pzw-chunk-is-resumable-run
      fn-pzw-stored-chunk-is-resumable-run fn-pzw-room fn-pzw-quantum
      fn-pzw-stored-allowance min nfix fn-pwz-progress-statep fn-pwz-progress-phase))))))

; No status exclusion: this includes genuine stream-ended completion and
; preserves the actual remaining STEP budget, not a semantic action fuel.
(defthm fn-pwzt-actual-stored-final-global-charge-envelope
 (implies
  (and (natp start) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab)
       (fn-pwz-budget-carryp compressed expected remaining fn-zin-st))
  (let* ((r (fn-pzw-stored-chunk requested remaining start end compressed expected
                                fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
         (left (fn-pzw-budget-left requested remaining (mv-nth 1 r)))
         (s (mv-nth 3 r)))
   (and (natp left) (fn-pwz-progress-statep s)
        (<= (- (fn-pzd-budget compressed expected) left)
            (+ (* 9 (fn-zin-tin s)) (* 2 (fn-zin-tout s)) 257)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pwzt-stored-all-outcomes-charged-progress
        fn-pwzt-stored-returned-budget-bounds
        (:instance fn-pzw-stored-chunk-counts-real-input)
        (:instance fn-pzw-budget-left-bounds
          (returned (mv-nth 1 (fn-pzw-stored-chunk requested remaining start end compressed expected
                                     fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))
  :in-theory (e/d (fn-pwz-budget-carryp fn-pzw-budget-left fn-zin-window-ready-p fn-zin-tab-okp)
   (fn-pwzt-stored-returned-budget-bounds fn-pzw-stored-chunk fn-pzw-stored-chunk-counts-real-input fn-pzw-budget-left-bounds
    fn-pzw-quantum fn-pwz-progress-statep fn-pwz-progress-phase fn-pzd-budget
    fn-pzw-stored-chunk-is-resumable-run fn-zin-loop fn-zin-run fn-zin-loop-counts)))))

(defthm fn-pwzt-actual-codec-final-global-charge-envelope
 (implies
  (and (equal (nth 0 z) :codec)
       (natp (nth 6 z)) (natp (nth 7 z)) (<= (nth 6 z) (nth 7 z))
       (<= (- (nth 7 z) (nth 6 z)) 64)
       (<= (nth 7 z) (fn-octets-len fn-octets))
       (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab)
       (fn-pwz-budget-carryp (nth 12 (nth 1 z)) (nth 2 z) (nth 5 z) fn-zin-st))
  (let* ((r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))
         (next (mv-nth 1 r)) (s (mv-nth 2 r)))
   (and (natp (nth 5 next)) (fn-pwz-progress-statep s)
        (<= (- (fn-pzd-budget (nth 12 (nth 1 z)) (nth 2 z)) (nth 5 next))
            (+ (* 9 (fn-zin-tin s)) (* 2 (fn-zin-tout s)) 257)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (:instance fn-pwzt-actual-stored-final-global-charge-envelope
    (requested 1024) (remaining (nth 5 z)) (start (nth 6 z)) (end (nth 7 z))
    (compressed (nth 12 (nth 1 z))) (expected (nth 2 z)))
  :in-theory (e/d (fn-ewz-codec-tick fn-ewz-state)
   (fn-pzw-stored-chunk fn-pzw-select fn-ewb-copy fn-pzw-stored-decision
    fn-pzw-budget-left fn-pzd-budget fn-pwz-progress-statep
    fn-pwz-budget-carryp fn-pzw-stored-chunk-is-resumable-run fn-zin-loop fn-zin-run)))))

(local
 (defthm fn-pwzt-codec-retains-raw-plan
  (equal (nth 1 (mv-nth 1 (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))) (nth 1 z))
  :hints (("Goal" :do-not-induct t :in-theory
   (e/d (fn-ewz-codec-tick fn-ewz-state)
    (fn-pzw-stored-chunk fn-pzw-select fn-ewb-copy fn-pzw-budget-left fn-pzw-stored-decision fn-ewz-compressed-completep fn-ewz-decision-mode))))))

(defthm fn-pwzt-actual-decoded-codec-retains-positive-budget
 (implies
  (and (equal (nth 0 z) :codec)
       (natp (nth 12 (nth 1 z))) (natp (nth 2 z))
       (natp (nth 6 z)) (natp (nth 7 z)) (<= (nth 6 z) (nth 7 z))
       (<= (- (nth 7 z) (nth 6 z)) 64)
       (<= (nth 7 z) (fn-octets-len fn-octets))
       (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab)
       (fn-pwz-controller-budget-carryp z fn-zin-st))
  (let* ((r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)))
   (implies (equal (nth 0 (mv-nth 1 r)) :decoded)
    (<= (+ 3839 (* 7 (nth 12 (nth 1 z)))) (nth 5 (mv-nth 1 r))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pwzt-actual-codec-final-global-charge-envelope
        fn-ewz-codec-tick-preserves-input-invariant
        fn-ewz-codec-decoded-has-exact-length-and-terminal
        fn-pwzt-codec-retains-raw-plan
        (:instance fn-ewz-input-invariant-bounds-real-input
         (z (mv-nth 1 (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)))
         (fn-zin-st (mv-nth 2 (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)))))
  :in-theory (e/d (fn-pwz-controller-budget-carryp fn-pzd-budget)
   (fn-ewz-codec-tick fn-ewz-input-invariantp fn-ewz-output-invariantp
    fn-pwz-budget-carryp fn-pwz-progress-statep fn-pzw-stored-chunk)))))

(local
 (defthm fn-pwzt-codec-action-implies-codec-mode-by-definition
  (implies (equal (car (fn-ewz-next-action z pgs-digest-state)) :codec) (equal (nth 0 z) :codec))
  :hints (("Goal" :in-theory (e/d (fn-ewz-next-action) (fn-ewz-publication fn-ewz-effect))))))

(defthm fn-pwzt-actual-issued-codec-one-retains-terminal-budget
 (let ((z (fn-pww-controller fn-pww-carry)))
  (implies
   (and (fn-pwz-tokenp token) (equal token (fn-pww-token fn-pww-carry))
        (eq (fn-pww-phase fn-pww-carry) :running)
        (eq (fn-pww-borrow-phase fn-pww-carry) :owned)
        (null (fn-pww-pending-action fn-pww-carry))
        (true-listp z) (true-listp (nth 1 z))
        (equal (car (fn-ewz-next-action z pgs-digest-state)) :codec)
        (natp (nth 12 (nth 1 z))) (natp (nth 2 z))
        (natp (nth 6 z)) (natp (nth 7 z)) (<= (nth 6 z) (nth 7 z))
        (<= (- (nth 7 z) (nth 6 z)) 64)
        (<= (nth 7 z) (fn-octets-len fn-octets))
        (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab)
        (fn-pwz-controller-budget-carryp z fn-zin-st))
   (let ((r (fn-dwc-one token fn-pww-carry fn-octets pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)))
    (implies (equal (nth 0 (fn-pww-controller (mv-nth 2 r))) :decoded)
     (<= (+ 3839 (* 7 (nth 12 (nth 1 z))))
         (nth 5 (fn-pww-controller (mv-nth 2 r))))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pwzt-actual-decoded-codec-retains-positive-budget (z (fn-pww-controller fn-pww-carry)))
        (:instance fn-pwzt-codec-action-implies-codec-mode-by-definition (z (fn-pww-controller fn-pww-carry))))
  :in-theory (e/d (fn-dwc-one)
   (fn-ewz-next-action fn-ewz-codec-tick fn-ewz-hash-tick fn-pwz-tokenp
    fn-pwz-controller-budget-carryp fn-zin-window-ready-p fn-zin-tab-okp)))))
