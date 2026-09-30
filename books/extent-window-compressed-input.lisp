; Real-input carry for the actual bounded compressed controller.
(in-package "ACL2")
(include-book "extent-window-compressed-refinement")

(include-book "payload-window-width")

(defun fn-ewz-scanned-input (plan)
  (declare (xargs :guard (true-listp plan)))
  (min (nfix (nth 12 plan))
       (nfix (- (+ (nfix (nth 2 plan)) (nfix (nth 7 plan))) (nfix (nth 11 plan))))))

(defun fn-ewz-input-invariantp (z fn-zin-st)
  (declare (xargs :stobjs fn-zin-st :guard (and (true-listp z) (true-listp (nth 1 z)))))
  (let ((mode (nth 0 z)) (scanned (fn-ewz-scanned-input (nth 1 z))))
    (and (natp (nth 6 z)) (natp (nth 7 z)) (<= (nth 6 z) (nth 7 z))
         (<= (nth 7 z) 64)
         (implies (equal mode :drain) (fn-pzd-endedp (nth 8 z)))
         (cond ((eq mode :scan) (equal (fn-zin-tin fn-zin-st) scanned))
               ((eq mode :codec) (equal (+ (fn-zin-tin fn-zin-st) (- (nth 7 z) (nth 6 z))) scanned))
               (t (<= (fn-zin-tin fn-zin-st) scanned))))))
(in-theory (disable fn-ewz-scanned-input fn-ewz-input-invariantp))

(local
 (defthm ewzi-drain-decision-retains-ended-status
  (implies (equal (fn-pzw-stored-decision status compressed expected remaining complete fn-zin-st) :drain)
           (fn-pzd-endedp status))
  :hints (("Goal" :in-theory (enable fn-pzw-stored-decision fn-pzw-decision fn-zin-stored-status fn-pzd-endedp)))))

(local
 (defthm ewzi-stored-chunk-input-count-independent-of-pool-shape
  (implies (natp start)
   (let ((r (fn-pzw-stored-chunk requested remaining start end compressed expected
                                         fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
    (and (natp (mv-nth 2 r)) (<= start (mv-nth 2 r))
         (equal (fn-zin-tin (mv-nth 3 r))
                (+ (fn-zin-tin fn-zin-st) (- (mv-nth 2 r) start))))))
  :hints (("Goal" :do-not-induct t
           :cases ((and (equal (len fn-zin-win) *fn-zin-win-octets*)
                        (equal (len fn-zin-tab) *fn-zin-tab-octets*)))
           :use fn-pzw-stored-chunk-counts-real-input
           :in-theory (e/d (fn-pzw-stored-chunk fn-pzw-chunk fn-zin-feed
                            fn-zin-window-ready-p fn-zin-tab-okp)
                           (fn-zin-loop fn-pzw-stored-chunk-counts-real-input
                            fn-pzw-stored-chunk-is-resumable-run fn-pzw-quantum fn-pzw-room))))))

(defthm fn-ewz-codec-tick-preserves-input-invariant
  (implies
   (fn-ewz-input-invariantp z fn-zin-st)
   (let ((r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)))
     (fn-ewz-input-invariantp (mv-nth 1 r) (mv-nth 2 r))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance ewzi-stored-chunk-input-count-independent-of-pool-shape
                   (requested 1024) (remaining (nth 5 z)) (start (nth 6 z)) (end (nth 7 z))
                   (compressed (nth 12 (nth 1 z))) (expected (nth 2 z)))
                 (:instance fn-pzw-actual-stored-chunk-input-span
                   (requested 1024) (remaining (nth 5 z)) (start (nth 6 z)) (end (nth 7 z))
                   (compressed (nth 12 (nth 1 z))) (expected (nth 2 z))))
           :in-theory (e/d (fn-ewz-codec-tick fn-ewz-state fn-ewz-input-invariantp fn-ewz-decision-mode)
                            (fn-pzw-stored-chunk fn-pzw-select fn-ewb-copy fn-pzw-budget-left
                             fn-pzw-stored-decision fn-ewz-scanned-input nth
                             fn-pzw-stored-chunk-is-resumable-run fn-pzw-stored-chunk-counts-real-input
                             fn-pzw-actual-stored-chunk-input-span fn-zin-loop fn-zin-run update-nth
                             ewzi-stored-chunk-input-count-independent-of-pool-shape)))))

(local
 (defthm ewzi-reset-loop-below
   (implies (and (natp i) (natp j) (< j i))
            (equal (fn-zin-fld j (fn-zin-reset-loop i fn-zin-st)) (fn-zin-fld j fn-zin-st)))
   :hints (("Goal" :induct (fn-zin-reset-loop i fn-zin-st)
                  :in-theory (enable fn-zin-reset-loop)))))

(local
 (defthm ewzi-reset-loop-fields
   (implies (and (natp i) (natp j) (<= i j) (< j 18))
            (equal (fn-zin-fld j (fn-zin-reset-loop i fn-zin-st)) 0))
   :hints (("Goal" :induct (fn-zin-reset-loop i fn-zin-st)
                  :in-theory (enable fn-zin-reset-loop)))))

(defthm fn-ewz-begin-establishes-input-invariant
  (implies (natp poff)
   (let ((r (fn-ewz-begin file eoff elen poff compressed decoded offset ticket incarnation lease expected dict
                        pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
    (fn-ewz-input-invariantp (car r) (mv-nth 2 r))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-ewz-begin fn-ewz-state fn-ewz-input-invariantp
                              fn-ewz-scanned-input fn-ews-begin fn-ewp-begin fn-ewp-state
                              fn-pzw-initialize fn-zin-reset fn-zin-reset-loop fn-pzd-endedp))))

(local
 (defthm ewzi-scanned-input-monotone
  (implies (and (natp (nth 7 s)) (natp p) (<= (nth 7 s) p))
   (<= (fn-ewz-scanned-input s)
       (fn-ewz-scanned-input (fn-ewp-with-phase-pos phase p s))))
  :hints (("Goal" :in-theory (enable fn-ewz-scanned-input fn-ewp-with-phase-pos fn-ewp-state min nfix)))))

(local
 (defthm ewzi-scanned-input-span-delta
  (implies (and (natp (nth 7 s)) (equal (nth 0 s) :scan))
   (equal (fn-ewz-scanned-input
           (fn-ewp-with-phase-pos phase (+ (nth 7 s) (fn-ewp-demand s)) s))
          (+ (fn-ewz-scanned-input s)
             (cadr (fn-ewp-payload-span (nfix (nth 11 s)) (nfix (nth 12 s)) s)))))
  :hints (("Goal" :in-theory (enable fn-ewz-scanned-input fn-ewp-with-phase-pos fn-ewp-state
                                    fn-ewp-payload-span fn-ewp-demand min max nfix)))))

(local
 (defthm ewzi-scanned-input-same-position
  (equal (fn-ewz-scanned-input (fn-ewp-with-phase-pos phase (nth 7 s) s))
         (fn-ewz-scanned-input s))
  :hints (("Goal" :in-theory (enable fn-ewz-scanned-input fn-ewp-with-phase-pos fn-ewp-state)))))

(local
 (defthm ewzi-raw-read-scanned-delta
  (implies (natp (nth 7 s))
   (let ((r (fn-ews-read effect io-status s fn-octets pgs-digest-state fn-ew-buffer)))
    (equal (fn-ewz-scanned-input (mv-nth 1 r))
           (+ (fn-ewz-scanned-input s)
              (if (equal (car r) :continue)
                  (cadr (fn-ewp-payload-span (nfix (nth 11 s)) (nfix (nth 12 s)) s)) 0)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance ewzi-scanned-input-span-delta (phase :scan))
                 (:instance ewzi-scanned-input-span-delta (phase :trailer)))
           :in-theory (e/d (fn-ews-read fn-ewp-complete-read fn-ewp-finish)
                            (fn-ewz-scanned-input fn-ewp-payload-span fn-ewp-with-phase-pos
                             fn-ews-effect fn-ewp-effect fn-ewp-demand pgs-dcb-step
                             fn-b3x-words fn-ewb-capture fn-ews-read-trailer pgs-dcb-result-octets
                             nth))))))

(local
 (defthm ewzi-payload-span-bounded
  (implies (and (natp poff) (natp plen))
   (let ((span (fn-ewp-payload-span poff plen s)))
    (and (natp (car span)) (natp (cadr span))
         (<= (+ (car span) (cadr span)) 64))))
  :hints (("Goal" :in-theory (enable fn-ewp-payload-span fn-ewp-demand min max nfix)))))

(local
 (defthm ewzi-payload-span-outside-scan
  (implies (not (equal (nth 0 s) :scan))
   (equal (fn-ewp-payload-span poff plen s) '(0 0)))
  :hints (("Goal" :in-theory (enable fn-ewp-payload-span)))))

(local
 (defthm ewzi-effect-modes
  (implies (fn-ewz-effect z pgs-digest-state)
           (member-eq (nth 0 z) '(:scan :drain :decoded)))
  :hints (("Goal" :in-theory (enable fn-ewz-effect)))))

(local
 (defthm ewzi-effect-natural-position
  (implies (fn-ewz-effect z pgs-digest-state) (natp (nth 7 (nth 1 z))))
  :hints (("Goal" :in-theory (enable fn-ewz-effect fn-ews-effect fn-ews-boundp)))))

(defthm fn-ewz-read-preserves-input-invariant
  (implies (fn-ewz-input-invariantp z fn-zin-st)
   (fn-ewz-input-invariantp
    (mv-nth 1 (fn-ewz-read effect io-status z fn-octets pgs-digest-state fn-ew-buffer)) fn-zin-st))
  :hints (("Goal" :do-not-induct t
           :cases ((fn-ewz-effect z pgs-digest-state))
           :use (ewzi-effect-modes ewzi-effect-natural-position
                 (:instance ewzi-raw-read-scanned-delta (s (nth 1 z)))
                 (:instance ewzi-payload-span-bounded (poff (nfix (nth 11 (nth 1 z))))
                   (plen (nfix (nth 12 (nth 1 z)))) (s (nth 1 z))))
           :in-theory (e/d (fn-ewz-read fn-ewz-state fn-ewz-input-invariantp)
                            (fn-ews-read fn-ewz-scanned-input fn-ewp-payload-span fn-ewz-effect nth
                             ewzi-raw-read-scanned-delta ewzi-payload-span-bounded
                             ewzi-effect-modes ewzi-effect-natural-position)))))

(local
 (defthm ewzi-raw-tick-scanned-unchanged
  (equal (fn-ewz-scanned-input (mv-nth 1 (fn-ews-tick s pgs-digest-state)))
         (fn-ewz-scanned-input s))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ews-tick) (fn-ews-effect fn-ews-boundp pgs-dcb-step
                                        fn-ewp-with-phase-pos fn-ewz-scanned-input nth))))))

(defthm fn-ewz-hash-tick-preserves-input-invariant
  (implies (fn-ewz-input-invariantp z fn-zin-st)
   (fn-ewz-input-invariantp (mv-nth 1 (fn-ewz-hash-tick z pgs-digest-state fn-zin-st)) fn-zin-st))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ewz-hash-tick fn-ewz-input-invariantp fn-ewz-decision-mode fn-pzw-stored-decision fn-pzw-decision
                                 fn-zin-stored-status fn-pzd-endedp)
                            (fn-ews-tick fn-ewz-scanned-input fn-ewz-compressed-completep
                             nth update-nth)))))

(defthm fn-ewz-input-invariant-bounds-real-input
  (implies (fn-ewz-input-invariantp z fn-zin-st)
           (<= (fn-zin-tin fn-zin-st) (nfix (nth 12 (nth 1 z)))))
  :hints (("Goal" :in-theory (enable fn-ewz-input-invariantp fn-ewz-scanned-input min)))
  :rule-classes nil)
