; The ACT trajectory of the actual STEP called by the bounded cold loop.
; Proof model only: semantic action count differs from charged STEP count.
(in-package "ACL2")
(include-book "decoded-window-literal-trajectory")

(local
 (defthm fn-pwz-action-result-full-tuple
   (let ((r (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
     (equal (list (car r) (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r)) r))
   :hints (("Goal" :in-theory (enable fn-zin-act)))))

(local
 (defthm fn-pwz-one-action-is-action-sequence
   (equal (fn-pwz-action-sequence 1 fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
          (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
   :hints (("Goal" :use ((:instance fn-pwz-action-result-full-tuple))
            :expand ((fn-pwz-action-sequence 1 fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
            :in-theory (e/d (fn-pwz-action-sequence) (fn-pwz-action-result-full-tuple))))))

(local
 (defthm fn-pwz-bomb-match-is-one-action
   (implies (and (posp room) (equal (fn-zin-mode fn-zin-st) 12)
                 (posp (fn-zin-n fn-zin-st))
                 (<= (fn-zin-bomb-limit fn-zin-st) (fn-zin-tout fn-zin-st)))
            (equal (let ((r (fn-zin-match room fn-zin-st fn-zin-win fn-zin-out)))
                     (mv (car r) (mv-nth 1 r) (mv-nth 2 r) fn-zin-tab (mv-nth 3 r)))
                   (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
   :hints (("Goal" :in-theory (e/d (fn-zin-match fn-zin-act fn-zin-emit min nfix)
                                     (fn-zin-match-out-free fn-zin-emit-out))))))

; This observer does not execute on the served path or supply native funding.
(defun-nx fn-pwz-step-action-count (room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
  (cond ((and (equal (fn-zin-mode fn-zin-st) 12) (posp (fn-zin-n fn-zin-st)))
         (max 1 (min (fn-zin-n fn-zin-st)
                     (min (nfix room) (nfix (- (fn-zin-bomb-limit fn-zin-st)
                                               (fn-zin-tout fn-zin-st)))))))
        ((and (equal (fn-zin-mode fn-zin-st) 8) (fn-zin-freshp fn-zin-st)
              (posp room) (fn-zin-lit-ready-p fn-zin-st fn-zin-tab))
         (max 1 (car (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
        (t 1)))

(defthm fn-pwz-step-action-count-positive
  (posp (fn-pwz-step-action-count room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
  :hints (("Goal" :in-theory (enable fn-pwz-step-action-count max))))

(defthm fn-pwz-step-action-count-room-bound
  (implies (posp room)
           (<= (fn-pwz-step-action-count room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
               room))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-zin-lits-room))
           :in-theory (e/d (fn-pwz-step-action-count max min nfix)
                            (fn-zin-step fn-zin-lits fn-zin-freshp fn-zin-lit-ready-p)))))

(local
 (defthm fn-pwz-step-literal-loop-tout-monotone
   (implies (and (natp tout) (natp nbits))
            (<= tout (mv-nth 3 (fn-zin-lit-loop k bits nbits w tout limit
                                               fn-zin-tab fn-zin-win fn-zin-out))))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance fn-zin-lit-loop-counts))
            :in-theory (disable fn-zin-lit-loop-counts)))))

(local
 (defthm fn-pwz-step-ready-literal-batch-positive
   (implies (and (posp room) (fn-zin-lit-ready-p fn-zin-st fn-zin-tab))
            (< 0 (car (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
   :hints (("Goal" :do-not-induct t
            :expand ((:free (bits nbits w tout limit tab win out)
                             (fn-zin-lit-loop room bits nbits w tout limit tab win out)))
            :in-theory (e/d (fn-zin-lits fn-zin-lit-ready-p) (fn-zin-lit-loop-out-free))))))

; Every actual basic-loop STEP at positive room is existing ACTs, including
; full refusal effects and zero-output transitions. No reachable mode omitted.
(defthm fn-pwz-actual-step-is-action-trajectory
  (implies (posp room)
           (equal (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                  (fn-pwz-action-sequence
                   (fn-pwz-step-action-count room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                   fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-pwz-step-ready-literal-batch-positive)
                 (:instance fn-pwz-actual-clipped-match-is-action-trajectory)
                 (:instance fn-pwz-actual-ready-literal-step-is-action-trajectory))
           :in-theory (e/d (fn-zin-step fn-pwz-step-action-count max
                            min nfix)
                           (fn-pwz-action-sequence fn-zin-act fn-zin-lits fn-zin-match
                            fn-zin-copy fn-zin-match-out-free fn-zin-lits-out-free)))) )

; Canonical semantic replay of the actual charged schedule. It uses only the
; existing ACT and PULL transitions, retaining the original loop's charged
; budget, terminal decisions and input/output frontiers. This proof model is
; not a new hosted decoder or a native funding function.
(defun-nx fn-pwz-action-trajectory-loop
  (b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :measure (nfix b)))
  (cond ((zp b) (mv :yield 0 ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
        ((<= (nfix lim) (fn-zin-out-len fn-zin-out))
         (mv :full b ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
        ((< (fn-zin-nbits fn-zin-st) (fn-zin-need fn-zin-st))
         (if (and (natp ip) (< ip (min (nfix end) (fn-octets-len fn-octets))))
             (let ((fn-zin-st (fn-zin-pull ip fn-zin-st fn-octets)))
               (fn-pwz-action-trajectory-loop (1- b) (1+ ip) end lim fn-zin-st
                            fn-octets fn-zin-win fn-zin-tab fn-zin-out))
           (mv :more b ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
        (t
         (let ((count (fn-pwz-step-action-count
                         (- (nfix lim) (fn-zin-out-len fn-zin-out))
                         fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
           (mv-let (why fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
             (fn-pwz-action-sequence count fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
             (if why
                 (mv (list :refused why) (1- b) ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
               (fn-pwz-action-trajectory-loop (1- b) ip end lim fn-zin-st fn-octets
                                              fn-zin-win fn-zin-tab fn-zin-out)))))))

(local
 (defthm fn-pwz-actual-step-is-action-trajectory-unfolds
   (implies (posp room)
            (equal (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                   (fn-pwz-action-sequence
                    (fn-pwz-step-action-count room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                    fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
   :hints (("Goal" :use ((:instance fn-pwz-actual-step-is-action-trajectory))))))

; Actual input bytes, refusal/status, charged budget, input cursor, all decoder
; registers and history/table/output effects agree, with no reachability or
; descriptor premise replacing actual decoding.
(defthm fn-pwz-actual-loop-is-action-trajectory
  (equal (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
         (fn-pwz-action-trajectory-loop b ip end lim fn-zin-st fn-octets
                                        fn-zin-win fn-zin-tab fn-zin-out))
  :rule-classes nil
  :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets
                                       fn-zin-win fn-zin-tab fn-zin-out)
           :expand ((fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                    (fn-pwz-action-trajectory-loop b ip end lim fn-zin-st fn-octets
                                                   fn-zin-win fn-zin-tab fn-zin-out))
           :in-theory (e/d ((:induction fn-zin-loop))
                           ((:definition fn-zin-loop) fn-pwz-action-trajectory-loop fn-zin-step
                            fn-pwz-action-sequence fn-pwz-step-action-count fn-zin-pull)))
          ("Subgoal *1/1" :use ((:instance fn-pwz-actual-step-is-action-trajectory
                          (room (- (nfix lim) (fn-zin-out-len fn-zin-out))))))))

(defun-nx fn-pwz-stored-action-trajectory
  (requested remaining start end compressed expected
             fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
  (declare (ignorable fn-zin-out))
  (let* ((credit (nfix compressed))
         (bound (min (nfix expected) (fn-pzw-stored-allowance compressed)))
         (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st))
         (r (fn-pwz-action-trajectory-loop
              (fn-pzw-quantum requested remaining) start end
              (fn-pzw-room bound (fn-zin-tout s0)) s0 fn-octets
              fn-zin-win fn-zin-tab nil))
         (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin (mv-nth 3 r)) credit)) (mv-nth 3 r))))
    (mv (car r) (mv-nth 1 r) (mv-nth 2 r) s1
        (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r))))

; Exact bounded cold input and output schedule: credit is added and removed
; at the actual boundary; stale scratch output contributes no bytes.
(defthm fn-pwz-actual-stored-chunk-is-action-trajectory
  (implies (and (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab))
           (equal (fn-pzw-stored-chunk requested remaining start end compressed expected
                                      fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                  (fn-pwz-stored-action-trajectory requested remaining start end compressed expected
                                                  fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-pwz-actual-loop-is-action-trajectory
                          (b (fn-pzw-quantum requested remaining)) (ip start)
                          (lim (fn-pzw-room
                                 (min (nfix expected) (fn-pzw-stored-allowance compressed))
                                 (fn-zin-tout fn-zin-st)))
                          (fn-zin-st (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st))
                          (fn-zin-out nil)))
           :in-theory (e/d (fn-pzw-stored-chunk fn-pzw-chunk fn-zin-feed
                            fn-pwz-stored-action-trajectory)
                           (fn-zin-loop fn-pwz-action-trajectory-loop fn-pzw-room fn-pzw-quantum
                            fn-pzw-stored-allowance fn-zin-loop-counts min nfix)))))

; Replay the actual codec continuation over the normalized decoder tuple.
; Bounds, selection, remaining charge and next mode remain ACL2 decisions.
(defun-nx fn-pwz-codec-action-trajectory
  (z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
  (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z))
         (remaining (nth 5 z)) (before (fn-zin-tout fn-zin-st)))
    (if (not (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= ip end)
                  (<= (- end ip) 64) (<= end (fn-octets-len fn-octets))))
        (mv :state (update-nth 0 :state z) fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
      (mv-let (status left ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
        (fn-pwz-stored-action-trajectory 1024 remaining ip end (nth 12 plan) (nth 2 z)
                                        fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
        (mv-let (src count dst)
          (fn-pzw-select before (fn-zin-out-len fn-zin-out) (nth 3 z) (nth 4 z))
          (let* ((fn-ew-buffer (fn-ewb-copy src count dst fn-zin-out fn-ew-buffer))
                 (budget (fn-pzw-budget-left 1024 remaining left))
                 (complete (and (equal ip end) (fn-ewz-compressed-completep plan)))
                 (decision (fn-pzw-stored-decision status (nth 12 plan) (nth 2 z) budget complete fn-zin-st))
                 (next (fn-ewz-state (if (and (eq decision :input) (not (equal ip end)))
                                        :state (fn-ewz-decision-mode decision)) plan (nth 2 z) (nth 3 z)
                                    (nth 4 z) budget ip end status)))
            (mv decision next fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)))))))

(defthm fn-pwz-actual-codec-is-action-trajectory
  (implies (and (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab))
           (equal (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)
                  (fn-pwz-codec-action-trajectory z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-pwz-actual-stored-chunk-is-action-trajectory
                          (requested 1024) (remaining (nth 5 z))
                          (start (nth 6 z)) (end (nth 7 z))
                          (compressed (nth 12 (nth 1 z))) (expected (nth 2 z))))
           :in-theory (e/d (fn-ewz-codec-tick fn-pwz-codec-action-trajectory)
                           (fn-pzw-stored-chunk fn-pwz-stored-action-trajectory
                            fn-pzw-select fn-ewb-copy fn-pzw-stored-decision fn-pzw-budget-left
                            fn-ewz-state fn-ewz-decision-mode fn-ewz-compressed-completep
                            fn-pzw-stored-chunk-counts-real-input fn-pzw-chunk-counts
                            fn-pzw-stored-chunk-is-resumable-run fn-pzw-chunk-is-resumable-run
                            fn-zin-run fn-zin-loop fn-pzw-room fn-pzw-quantum
                            fn-pzw-stored-allowance min nfix nth fn-zin-loop-counts)))))
