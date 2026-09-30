; Actual controller final charge envelope, including terminal/refused outcomes.
; Source proof carry only; no native funding or activation authority.
(in-package "ACL2")
(include-book "decoded-window-budget-trajectory")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-pwz-terminal-budget-carryp (compressed expected remaining fn-zin-st)
  (declare (xargs :stobjs fn-zin-st :guard t))
  (and (natp remaining)
       (<= (- (fn-pzd-budget compressed expected) remaining)
           (+ (* 9 (fn-zin-tin fn-zin-st)) (* 2 (fn-zin-tout fn-zin-st)) 257))))

(defthm fn-pwz-terminal-active-budget-positive
  (implies (and (natp compressed) (natp expected)
                (fn-pwz-terminal-budget-carryp compressed expected remaining fn-zin-st)
                (<= (fn-zin-tin fn-zin-st) compressed)
                (<= (fn-zin-tout fn-zin-st) expected))
           (and (posp remaining) (<= (+ 3839 (* 7 compressed)) remaining)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwz-terminal-budget-carryp fn-pzd-budget))))

(local
 (defthm fn-pwz-credit-keeps-progress-coordinates
   (let ((s (fn-zin-set 7 credit fn-zin-st)))
     (and (equal (fn-pwz-progress-statep s) (fn-pwz-progress-statep fn-zin-st))
          (equal (fn-pwz-progress-phase s) (fn-pwz-progress-phase fn-zin-st))
          (equal (fn-zin-nbits s) (fn-zin-nbits fn-zin-st))
          (equal (fn-zin-tout s) (fn-zin-tout fn-zin-st))))
   :hints (("Goal" :in-theory (enable fn-pwz-progress-statep fn-pwz-progress-phase)))))


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


(local
 (defthm fn-pwz-stored-chunk-all-outcomes-charged-progress
   (implies (and (natp start) (fn-pwz-progress-statep fn-zin-st)
                 (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab)
)
            (let* ((r (fn-pzw-stored-chunk requested remaining start end compressed expected
                                          fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
                   (s (mv-nth 3 r)))
              (and (fn-pwz-progress-statep s)
                   (<= (- (fn-pzw-quantum requested remaining) (mv-nth 1 r))
                       (+ (* 9 (- (mv-nth 2 r) start))
                          (* 2 (- (fn-zin-tout s) (fn-zin-tout fn-zin-st)))
                          (fn-pwz-progress-phase fn-zin-st)
                          (fn-zin-nbits fn-zin-st) 259)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-pwz-actual-loop-charge-bound
                           (b (fn-pzw-quantum requested remaining)) (ip start)
                           (lim (fn-pzw-room (min (nfix expected) (fn-pzw-stored-allowance compressed))
                                              (fn-zin-tout fn-zin-st)))
                           (fn-zin-st (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st))
                           (fn-zin-out nil)))
            :in-theory (e/d (fn-pzw-stored-chunk fn-pzw-chunk fn-zin-feed)
                            (fn-zin-loop fn-zin-loop-counts fn-pzw-chunk-is-resumable-run
                             fn-pzw-stored-chunk-is-resumable-run fn-pzw-room fn-pzw-quantum
                             fn-pzw-stored-allowance min nfix fn-pwz-progress-statep fn-pwz-progress-phase fn-pzw-budget-left))))))


(local
 (defthm fn-pwz-stored-chunk-establishes-terminal-budget-carry
   (implies (and (natp start) (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab)
                 (fn-pwz-budget-carryp compressed expected remaining fn-zin-st)
)
            (let* ((r (fn-pzw-stored-chunk requested remaining start end compressed expected
                                          fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
              (fn-pwz-terminal-budget-carryp compressed expected
                                   (fn-pzw-budget-left requested remaining (mv-nth 1 r)) (mv-nth 3 r))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-pwz-stored-chunk-all-outcomes-charged-progress)
                          (:instance fn-pwz-stored-chunk-returned-budget-bounds)
                          (:instance fn-pwz-stored-chunk-real-input-count))
            :in-theory (e/d (fn-pwz-budget-carryp fn-pwz-terminal-budget-carryp fn-pzw-budget-left fn-pzw-quantum)
                            (fn-pwz-stored-chunk-returned-budget-bounds fn-pzw-stored-chunk-counts-real-input fn-pzw-stored-chunk fn-pzd-budget fn-pwz-progress-statep
                             fn-pwz-progress-phase fn-pwz-stored-chunk-real-input-count))))))

(local
 (defthm fn-pwz-strict-carry-implies-terminal-carry
  (implies (fn-pwz-budget-carryp compressed expected remaining fn-zin-st)
           (fn-pwz-terminal-budget-carryp compressed expected remaining fn-zin-st))
  :hints (("Goal" :in-theory (enable fn-pwz-budget-carryp fn-pwz-terminal-budget-carryp
                                    fn-pwz-progress-phase fn-pwz-progress-statep)))))

(local
 (defthm fn-pwz-actual-codec-terminal-budget-carry
   (implies (and (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab)
                 (fn-pwz-budget-carryp (nth 12 (nth 1 z)) (nth 2 z) (nth 5 z) fn-zin-st)
)
            (let* ((r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer))
                   (next (mv-nth 1 r)))
              (fn-pwz-terminal-budget-carryp (nth 12 (nth 1 next)) (nth 2 next) (nth 5 next) (mv-nth 2 r))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-pwz-stored-chunk-establishes-terminal-budget-carry
                           (requested 1024) (remaining (nth 5 z)) (start (nth 6 z)) (end (nth 7 z))
                           (compressed (nth 12 (nth 1 z))) (expected (nth 2 z))))
            :in-theory (e/d (fn-ewz-codec-tick fn-ewz-state nth)
                            (fn-pzw-stored-chunk fn-pzw-stored-chunk-is-resumable-run fn-pzw-chunk-is-resumable-run
                             fn-zin-loop fn-zin-run fn-zin-loop-counts fn-pzw-quantum fn-pzw-room
                             fn-pzw-stored-allowance min nfix fn-pzw-select fn-ewb-copy fn-pzw-budget-left
                             fn-pzw-stored-decision fn-ewz-compressed-completep fn-ewz-decision-mode
                             fn-pwz-budget-carryp fn-pwz-terminal-budget-carryp))))))

; Drain/decoded cannot execute another codec action. Their envelope covers the
; actual empty-stream decision as well as a charged terminal return.
(defun fn-pwz-controller-final-budget-envelopep (z fn-zin-st)
 (declare (xargs :stobjs fn-zin-st :guard (and (true-listp z) (true-listp (nth 1 z)))))
 (and (fn-ewz-input-invariantp z fn-zin-st)
      (fn-ewz-output-invariantp z fn-zin-st)
      (natp (nth 5 z))
      (cond ((member-eq (nth 0 z) '(:scan :codec))
             (fn-pwz-budget-carryp (nth 12 (nth 1 z)) (nth 2 z) (nth 5 z) fn-zin-st))
            ((member-eq (nth 0 z) '(:drain :decoded))
             (fn-pwz-terminal-budget-carryp (nth 12 (nth 1 z)) (nth 2 z) (nth 5 z) fn-zin-st))
            (t t))))

(defthm fn-pwz-final-envelope-active-budget-positive
 (implies (and (fn-pwz-controller-final-budget-envelopep z fn-zin-st)
               (member-eq (nth 0 z) '(:scan :codec :drain :decoded)))
          (and (posp (nth 5 z))
               (<= (+ 3839 (* 7 (nth 12 (nth 1 z)))) (nth 5 z))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-ewz-input-invariant-bounds-real-input)
                        (:instance fn-pwz-active-controller-budget-remains-positive)
                        (:instance fn-pwz-terminal-active-budget-positive
                         (compressed (nth 12 (nth 1 z))) (expected (nth 2 z)) (remaining (nth 5 z))))
          :in-theory (e/d (fn-pwz-controller-final-budget-envelopep fn-pwz-controller-budget-carryp
                           fn-ewz-output-invariantp fn-pzw-stored-admissiblep)
                          (fn-ewz-input-invariantp fn-pwz-progress-statep fn-pwz-progress-phase
                           fn-pwz-budget-carryp fn-pwz-terminal-budget-carryp fn-pzw-stored-allowance)))))
(local
 (defthm fn-pwz-budget-left-is-natural
  (natp (fn-pzw-budget-left requested remaining left))
  :hints (("Goal" :in-theory (enable fn-pzw-budget-left fn-pzw-quantum min nfix)))))

(local
 (defthm fn-pwz-actual-codec-final-envelope-ready-pools
  (implies (and (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab)
                (fn-pwz-controller-final-budget-envelopep z fn-zin-st))
           (let ((r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)))
            (fn-pwz-controller-final-budget-envelopep (mv-nth 1 r) (mv-nth 2 r))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-ewz-codec-tick-preserves-input-invariant)
                 (:instance fn-ewz-codec-tick-establishes-output-invariant)
                 (:instance fn-pwz-actual-codec-carries-budget)
                 (:instance fn-pwz-actual-codec-terminal-budget-carry)
                 (:instance fn-pwz-stored-chunk-returned-budget-bounds
                  (requested 1024) (remaining (nth 5 z)) (start (nth 6 z)) (end (nth 7 z))
                  (compressed (nth 12 (nth 1 z))) (expected (nth 2 z))))
           :in-theory (e/d (fn-pwz-controller-final-budget-envelopep fn-ewz-codec-tick fn-ewz-state
                            fn-ewz-decision-mode fn-pzw-stored-decision fn-pzw-decision
                            fn-zin-stored-status fn-pzd-endedp)
                           (fn-ewz-input-invariantp fn-ewz-output-invariantp fn-pwz-budget-carryp
                            fn-pwz-terminal-budget-carryp fn-pzw-stored-chunk
                            fn-pzw-stored-chunk-is-resumable-run fn-pzw-chunk-is-resumable-run
                            fn-zin-loop fn-pzw-select fn-ewb-copy fn-ewz-compressed-completep
                            fn-pzw-stored-allowance min nfix fn-pzd-budget fn-pwz-progress-statep
                            fn-pwz-progress-phase fn-pzw-budget-left))))))
(local
 (defthm fn-pwz-budget-left-of-full-quantum
  (equal (fn-pzw-budget-left requested remaining (fn-pzw-quantum requested remaining))
         (nfix remaining))
  :hints (("Goal" :in-theory (enable fn-pzw-budget-left fn-pzw-quantum min nfix)))))

(local
 (defthm fn-pwz-zero-minimum-of-natural
  (equal (min 0 (nfix x)) 0)
  :hints (("Goal" :in-theory (enable min nfix)))))
(local
 (defthm fn-pwz-natural-normalization
  (implies (natp x) (equal (nfix x) x))
  :hints (("Goal" :in-theory (enable nfix)))))

(defthm fn-pwz-actual-codec-preserves-final-budget-envelope
 (implies (fn-pwz-controller-final-budget-envelopep z fn-zin-st)
          (let ((r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)))
           (fn-pwz-controller-final-budget-envelopep (mv-nth 1 r) (mv-nth 2 r))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :cases ((and (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab)))
          :use ((:instance fn-pwz-actual-codec-final-envelope-ready-pools)
                (:instance fn-ewz-codec-tick-preserves-input-invariant)
                (:instance fn-ewz-codec-tick-establishes-output-invariant))
          :in-theory (e/d (fn-pwz-controller-final-budget-envelopep fn-ewz-codec-tick fn-ewz-state fn-ewz-input-invariantp fn-ewz-scanned-input
                           fn-pzw-stored-chunk fn-pzw-chunk fn-zin-feed
                           fn-ewz-decision-mode fn-pzw-stored-decision fn-pzw-decision fn-pwz-terminal-budget-carryp fn-pwz-budget-carryp)
                          (fn-ewz-output-invariantp fn-zin-loop fn-pzw-room fn-pzw-select
                           fn-ewb-copy fn-ewz-compressed-completep fn-pzw-stored-allowance
                           fn-pzw-stored-chunk-is-resumable-run fn-pzw-chunk-is-resumable-run fn-pzw-budget-left fn-pzw-quantum min nfix)))))
(local
 (defthm fn-pwz-budget-carry-remaining-natural
  (implies (fn-pwz-budget-carryp compressed expected remaining fn-zin-st) (natp remaining))
  :hints (("Goal" :in-theory (enable fn-pwz-budget-carryp)))))

(defthm fn-pwz-actual-begin-establishes-final-budget-envelope
 (implies (natp poff)
          (let ((r (fn-ewz-begin file eoff elen poff compressed decoded offset ticket incarnation lease expected dict
                               pgs-digest-state fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
           (fn-pwz-controller-final-budget-envelopep (car r) (mv-nth 2 r))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-pwz-controller-begin-establishes-budget-carry))
          :in-theory (e/d (fn-pwz-controller-final-budget-envelopep fn-pwz-controller-budget-carryp)
                          (fn-ewz-begin fn-ewz-input-invariantp fn-ewz-output-invariantp
                           fn-pwz-budget-carryp fn-pwz-terminal-budget-carryp fn-pwz-controller-begin-establishes-budget-carry)))))

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

(defthm fn-pwz-actual-read-preserves-final-budget-envelope
 (implies (fn-pwz-controller-final-budget-envelopep z fn-zin-st)
          (fn-pwz-controller-final-budget-envelopep
           (mv-nth 1 (fn-ewz-read effect io-status z fn-octets pgs-digest-state fn-ew-buffer)) fn-zin-st))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-ewz-read-preserves-input-invariant)
                       (:instance fn-ewz-read-preserves-output-invariant)
                       (:instance fn-pwz-actual-compressed-read-preserves-budget-carry))
          :in-theory (e/d (fn-pwz-controller-final-budget-envelopep fn-ewz-read fn-ewz-state nth)
                          (fn-ewz-input-invariantp fn-ewz-output-invariantp fn-pwz-budget-carryp
                           fn-pwz-terminal-budget-carryp fn-ews-read fn-ewz-effect fn-ewp-payload-span)))))
(local
 (defthm fn-pwz-complete-ended-decision-never-resumes-codec
  (implies (fn-pzd-endedp status)
           (not (member-eq (fn-ewz-decision-mode
                            (fn-pzw-stored-decision status compressed expected remaining t fn-zin-st))
                           '(:scan :codec))))
  :hints (("Goal" :in-theory (enable fn-pzd-endedp fn-ewz-decision-mode fn-pzw-stored-decision
                                    fn-pzw-decision fn-zin-stored-status)))))

(defthm fn-pwz-actual-hash-tick-preserves-final-budget-envelope
 (implies (fn-pwz-controller-final-budget-envelopep z fn-zin-st)
          (fn-pwz-controller-final-budget-envelopep
           (mv-nth 1 (fn-ewz-hash-tick z pgs-digest-state fn-zin-st)) fn-zin-st))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-ewz-hash-tick-preserves-input-invariant)
                       (:instance fn-ewz-hash-tick-preserves-output-invariant)
                       (:instance fn-pwz-actual-compressed-hash-tick-preserves-budget-carry)
                       (:instance fn-pwz-complete-ended-decision-never-resumes-codec
                        (status (nth 8 z)) (compressed (nth 12 (nth 1 z)))
                        (expected (nth 2 z)) (remaining (nth 5 z))))
          :in-theory (e/d (fn-pwz-controller-final-budget-envelopep fn-ewz-hash-tick fn-ewz-input-invariantp)
                          (fn-ewz-output-invariantp fn-pwz-budget-carryp fn-pwz-terminal-budget-carryp
                           fn-ews-tick fn-ewz-compressed-completep fn-pzw-stored-decision fn-ewz-decision-mode)))))
