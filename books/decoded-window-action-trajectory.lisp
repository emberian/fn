; Actual decoder actions are the semantic trajectory, not a host promise.
; Proof-only normalization support for the actual bounded cold controller.
(in-package "ACL2")
(include-book "decoded-window-copy-trajectory")

(local
 (defthm fn-pwz-action-buffer-recognizers
   (and (equal (fn-zin-win-p x) (fn-cbor-octet-listp x))
        (equal (fn-zin-tab-p x) (fn-cbor-octet-listp x))
        (equal (fn-zin-out-p x) (fn-cbor-octet-listp x)))))

; Repeat the existing actual action; no alternate inflater is implemented.
; This proof model is not hosted or charged as native execution.
(defun fn-pwz-action-sequence (k fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :stobjs (fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                  :guard (and (natp k) (fn-zin-window-ready-p fn-zin-win)
                              (fn-zin-tab-okp fn-zin-tab))
                  :measure (nfix k)
                  :guard-hints (("Goal" :in-theory
                                  (enable fn-zin-window-ready-p fn-zin-tab-okp)))))
  (if (zp k)
      (mv nil fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
    (mv-let (why fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
      (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
      (if why
          (mv why fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
        (fn-pwz-action-sequence (1- k) fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))))

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

; WIP: exact full-state normalization of actual match/literal batches and
; the fn-ewz-codec-tick composition. No helper-only completion claim.

(local
 (defthm fn-pwz-state-set-order
   (implies (and (natp i) (natp j) (< j i))
            (equal (fn-zin-set i x (fn-zin-set j y fn-zin-st))
                   (fn-zin-set j y (fn-zin-set i x fn-zin-st))))
   :hints (("Goal" :use ((:instance fn-pwz-state-set-commute))))))

(local
 (defthm fn-pwz-action-min-copy-room
   (implies (and (natp room) (natp n) (natp allowance)
                 (<= room n) (<= room allowance))
            (equal (min n (min room allowance)) room))
   :hints (("Goal" :in-theory (enable min)))))

(local
 (defthm fn-pwz-action-wrap-idempotent
   (equal (fn-zin-wrap (fn-zin-wrap w)) (fn-zin-wrap w))
   :hints (("Goal" :in-theory (enable fn-zin-wrap$inline)))))

(local
 (defthm fn-pwz-action-source-of-wrapped-position
   (equal (fn-zin-source d tout h (fn-zin-wrap w) fn-zin-win)
          (fn-zin-source d tout h w fn-zin-win))
   :hints (("Goal" :in-theory (enable fn-zin-source)))))

(local
 (defthm fn-pwz-action-sequence-zero
   (equal (fn-pwz-action-sequence 0 fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
          (mv nil fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
   :hints (("Goal" :in-theory (enable fn-pwz-action-sequence)))))

(local
 (defthm fn-pwz-action-copy-zero
   (equal (fn-zin-copy 0 w d tout h fn-zin-win fn-zin-out)
          (mv (fn-zin-wrap w) fn-zin-win fn-zin-out))
   :hints (("Goal" :in-theory (enable fn-zin-copy)))))

(local
 (defthm fn-pwz-action-copy-one
   (equal (fn-zin-copy 1 w d tout h fn-zin-win fn-zin-out)
          (mv (fn-zin-wrap (1+ (fn-zin-wrap w)))
              (fn-oct-update (fn-zin-wrap w) (fn-zin-source d tout h w fn-zin-win) fn-zin-win)
              (fn-oct-snoc fn-zin-out (fn-zin-source d tout h w fn-zin-win))))
   :hints (("Goal" :expand ((fn-zin-copy 1 w d tout h fn-zin-win fn-zin-out))
            :in-theory (disable (:definition fn-zin-copy) fn-zin-copy-out-free)))))

(local
 (defthm fn-pwz-state-set-canonical-order
   (implies (and (natp i) (natp j) (< j i))
            (equal (fn-zin-set i x (fn-zin-set j y fn-zin-st))
                   (fn-zin-set j y (fn-zin-set i x fn-zin-st))))
   :rule-classes ((:rewrite :loop-stopper nil))
   :hints (("Goal" :use ((:instance fn-pwz-state-set-commute))))))

(local
 (defthm fn-pwz-copy-actions-full-effects
   (implies
    (and (posp k) (equal (fn-zin-mode fn-zin-st) 12)
         (<= k (fn-zin-n fn-zin-st))
         (<= k (- (fn-zin-bomb-limit fn-zin-st) (fn-zin-tout fn-zin-st))))
    (equal
     (fn-pwz-action-sequence k fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
     (let ((r (fn-zin-copy k (fn-zin-wpos fn-zin-st) (fn-zin-dist fn-zin-st)
                           (fn-zin-tout fn-zin-st) (fn-zin-preset fn-zin-st)
                           fn-zin-win fn-zin-out)))
       (mv nil (fn-zin-set 3 (- (fn-zin-n fn-zin-st) k)
                          (fn-zin-set 6 (+ (fn-zin-tout fn-zin-st) k)
                                      (fn-zin-set 5 (car r) fn-zin-st)))
           (mv-nth 1 r) fn-zin-tab (mv-nth 2 r)))))
   :rule-classes nil
   :hints
   (("Goal" :induct (fn-pwz-action-sequence k fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
     :expand ((fn-pwz-action-sequence k fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
              (fn-zin-copy k (fn-zin-wpos fn-zin-st) (fn-zin-dist fn-zin-st)
                           (fn-zin-tout fn-zin-st) (fn-zin-preset fn-zin-st)
                           fn-zin-win fn-zin-out))
     :in-theory (e/d (fn-zin-match fn-zin-act fn-zin-emit fn-zin-back min nfix
                      fn-pwz-action-sequence fn-zin-copy
                      fn-pwz-action-sequence-zero fn-pwz-action-copy-zero fn-pwz-action-copy-one)
                     (fn-zin-copy-out-free fn-zin-match-out-free fn-zin-emit-out))))))

(local
 (defthm fn-pwz-action-clip-to-room
   (implies (and (natp room) (natp n) (integerp allowance)
                 (<= room n) (<= room allowance))
            (equal (min n (min (nfix room) (nfix allowance))) room))
   :hints (("Goal" :in-theory (enable min nfix)))))

(local
 (defthm fn-pwz-actual-match-batch-is-action-trajectory
   (implies
    (and (posp k) (equal (fn-zin-mode fn-zin-st) 12)
         (<= k (fn-zin-n fn-zin-st))
         (<= k (- (fn-zin-bomb-limit fn-zin-st) (fn-zin-tout fn-zin-st))))
    (equal
     (fn-pwz-action-sequence k fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
     (let ((r (fn-zin-match k fn-zin-st fn-zin-win fn-zin-out)))
       (mv (car r) (mv-nth 1 r) (mv-nth 2 r) fn-zin-tab (mv-nth 3 r)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-pwz-copy-actions-full-effects))
            :in-theory (e/d (fn-zin-match fn-zin-bomb-limit)
                            (fn-pwz-action-sequence fn-zin-copy min nfix
                             fn-zin-copy-out-free fn-zin-match-out-free))))))

(local
 (defthm fn-pwz-copy-actions-state-projection
   (implies
    (and (posp k) (equal (fn-zin-mode fn-zin-st) 12)
         (<= k (fn-zin-n fn-zin-st))
         (<= k (- (fn-zin-bomb-limit fn-zin-st) (fn-zin-tout fn-zin-st))))
    (let ((copy (fn-zin-copy k (fn-zin-wpos fn-zin-st) (fn-zin-dist fn-zin-st)
                              (fn-zin-tout fn-zin-st) (fn-zin-preset fn-zin-st)
                              fn-zin-win fn-zin-out))
          (actions (fn-pwz-action-sequence k fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
      (and (equal (mv-nth 1 actions)
                  (fn-zin-set 3 (- (fn-zin-n fn-zin-st) k)
                              (fn-zin-set 6 (+ (fn-zin-tout fn-zin-st) k)
                                          (fn-zin-set 5 (car copy) fn-zin-st))))
           (equal (mv-nth 2 actions) (mv-nth 1 copy))
           (equal (mv-nth 3 actions) fn-zin-tab)
           (equal (mv-nth 4 actions) (mv-nth 2 copy)))))
   :hints (("Goal" :use ((:instance fn-pwz-copy-actions-full-effects))
            :in-theory (disable fn-pwz-action-sequence fn-zin-copy fn-zin-copy-out-free)))))

; Logical source count for the normalized actual copy actions. This is not
; a scheduling-action budget or a native allocation count.
(defthm fn-pwz-copy-actions-output-count
  (implies
   (and (posp k) (equal (fn-zin-mode fn-zin-st) 12)
        (<= k (fn-zin-n fn-zin-st))
        (<= k (- (fn-zin-bomb-limit fn-zin-st) (fn-zin-tout fn-zin-st))))
   (equal (len (mv-nth 4 (fn-pwz-action-sequence k fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
          (+ (len fn-zin-out) k)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-pwz-copy-actions-state-projection)
                        (:instance fn-zin-copy-out-len
                                   (w (fn-zin-wpos fn-zin-st))
                                   (d (fn-zin-dist fn-zin-st))
                                   (tout (fn-zin-tout fn-zin-st))
                                   (h (fn-zin-preset fn-zin-st))))
           :in-theory (disable fn-pwz-action-sequence fn-zin-copy fn-zin-copy-out-free))))

(defthm fn-pwz-actual-codec-copy-action-effects
  (let* ((plan (nth 1 z)) (ip (nth 6 z)) (end (nth 7 z))
         (q (fn-pzw-quantum 1024 (nth 5 z)))
         (credit (nfix (nth 12 plan)))
         (bound (min (nfix (nth 2 z)) (fn-pzw-stored-allowance (nth 12 plan))))
         (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st)))
    (implies
     (and (eq (nth 0 z) :codec) (natp ip) (natp end) (<= ip end)
          (<= (- end ip) 64) (<= end (fn-octets-len fn-octets))
          (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64)
          (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0))
          (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0))))
          (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab))
     (let* ((actions (fn-pwz-action-sequence 64 s0 fn-zin-win fn-zin-tab nil))
            (s1 (mv-nth 1 actions))
            (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1))
            (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64
                                      (nth 3 z) (nth 4 z)))
            (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win
                                 fn-zin-tab fn-zin-out fn-ew-buffer)))
       (and (equal (mv-nth 2 r) s1)
            (equal (mv-nth 3 r) (mv-nth 2 actions))
            (equal (mv-nth 4 r) (mv-nth 3 actions))
            (equal (mv-nth 5 r) (mv-nth 4 actions))
            (equal (mv-nth 6 r)
                   (fn-ewb-copy (car selection) (mv-nth 1 selection)
                                (mv-nth 2 selection) (mv-nth 4 actions)
                                fn-ew-buffer))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-pwz-actual-codec-copy-effects)
                 (:instance fn-pwz-copy-actions-state-projection
                            (k 64) (fn-zin-out nil)
                            (fn-zin-st (fn-zin-set 7
                                         (+ (nfix (nth 12 (nth 1 z)))
                                            (fn-zin-tin fn-zin-st)) fn-zin-st))))
           :in-theory (e/d (fn-zin-bomb-limit mv-nth)
                           (fn-ewz-codec-tick fn-pwz-action-sequence fn-zin-copy
                            fn-ewb-copy fn-pzw-select fn-pzw-room fn-pzw-quantum)))) )

; Exact match normalization for arbitrary positive output room. The semantic
; action count is the actual clipped copy length, not one charged STEP.
(defthm fn-pwz-actual-clipped-match-is-action-trajectory
  (let ((k (min (fn-zin-n fn-zin-st)
                (min (nfix room)
                     (nfix (- (fn-zin-bomb-limit fn-zin-st)
                              (fn-zin-tout fn-zin-st)))))))
    (implies (and (equal (fn-zin-mode fn-zin-st) 12) (posp k))
             (equal (let ((r (fn-zin-match room fn-zin-st fn-zin-win fn-zin-out)))
                      (mv (car r) (mv-nth 1 r) (mv-nth 2 r) fn-zin-tab (mv-nth 3 r)))
                    (fn-pwz-action-sequence k fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-pwz-copy-actions-full-effects
                          (k (min (fn-zin-n fn-zin-st)
                                  (min (nfix room)
                                       (nfix (- (fn-zin-bomb-limit fn-zin-st)
                                                (fn-zin-tout fn-zin-st))))))))
           :in-theory (e/d (fn-zin-match min nfix)
                           (fn-pwz-action-sequence fn-zin-copy fn-zin-copy-out-free
                            fn-zin-match-out-free)))))
