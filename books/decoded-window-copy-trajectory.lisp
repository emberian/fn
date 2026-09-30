; Byte/state stuttering for the actual bounded decoded cold path.
; The controller integration follows these actual copy effects; no host
; assumption about decoded bytes or primitive lowering is introduced.
(in-package "ACL2")
(include-book "decoded-window-read")

(local
 (defthm fn-pwz-wrap-idempotent
   (equal (fn-zin-wrap (fn-zin-wrap w)) (fn-zin-wrap w))
   :hints (("Goal" :in-theory (enable fn-zin-wrap$inline)))))

(local
 (defthm fn-pwz-copy-of-wrapped-start-by-definition
   (equal (fn-zin-copy k (fn-zin-wrap w) d tout h fn-zin-win fn-zin-out)
          (fn-zin-copy k w d tout h fn-zin-win fn-zin-out))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-zin-copy k (fn-zin-wrap w) d tout h fn-zin-win fn-zin-out)
                     (fn-zin-copy k w d tout h fn-zin-win fn-zin-out))))))

(local
 (defthm fn-pwz-copy-zero-by-definition
   (equal (fn-zin-copy 0 w d tout h fn-zin-win fn-zin-out)
          (mv (fn-zin-wrap w) fn-zin-win fn-zin-out))
   :hints (("Goal" :expand ((fn-zin-copy 0 w d tout h fn-zin-win fn-zin-out))))))

; Exact ring position, ring bytes and output effects of the actual routine.
; K is the number of copied bytes, not a decoder scheduling action count.
(defthm fn-pwz-actual-copy-split-effects
  (implies (and (natp k1) (natp k2) (natp tout))
           (equal (fn-zin-copy (+ k1 k2) w d tout h fn-zin-win fn-zin-out)
                  (let ((r (fn-zin-copy k1 w d tout h fn-zin-win fn-zin-out)))
                    (fn-zin-copy k2 (car r) d (+ tout k1) h
                                 (mv-nth 1 r) (mv-nth 2 r)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-zin-copy k1 w d tout h fn-zin-win fn-zin-out)
           :expand ((fn-zin-copy (+ k1 k2) w d tout h fn-zin-win fn-zin-out)
                    (fn-zin-copy k1 w d tout h fn-zin-win fn-zin-out))
           :in-theory (e/d ((:induction fn-zin-copy))
                           ((:definition fn-zin-copy) fn-zin-copy-out-free)))))

(local
 (defthm fn-pwz-loop-full-or-yield-by-definition
   (implies (and (natp b)
                 (<= (nfix lim) (fn-zin-out-len fn-zin-out)))
            (equal (fn-zin-loop b ip end lim fn-zin-st fn-octets
                               fn-zin-win fn-zin-tab fn-zin-out)
                   (mv (if (zp b) :yield :full) b ip fn-zin-st
                       fn-zin-win fn-zin-tab fn-zin-out)))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-zin-loop b ip end lim fn-zin-st fn-octets
                                 fn-zin-win fn-zin-tab fn-zin-out))))))

(local
 (defthm fn-pwz-min-copy-room
   (implies (and (natp room) (natp n) (natp allowance)
                 (<= room n) (<= room allowance))
            (equal (min n (min room allowance)) room))
   :hints (("Goal" :in-theory (enable min)))))

; This local controller boundary exposes the actual copy fragment. Its
; stuttering composition, rather than this unfolding, is the semantic join.
(local
 (defthm fn-pwz-loop-copy-fragment-unfolds
   (implies (and (posp b) (posp room)
                 (equal (fn-zin-mode fn-zin-st) 12)
                 (<= room (fn-zin-n fn-zin-st))
                 (<= room (nfix (- (fn-zin-bomb-limit fn-zin-st)
                                  (fn-zin-tout fn-zin-st)))))
            (equal (fn-zin-loop b ip end room fn-zin-st fn-octets
                               fn-zin-win fn-zin-tab nil)
                   (let* ((r (fn-zin-copy room (fn-zin-wpos fn-zin-st)
                                         (fn-zin-dist fn-zin-st)
                                         (fn-zin-tout fn-zin-st)
                                         (fn-zin-preset fn-zin-st) fn-zin-win nil))
                          (s (fn-zin-set 5 (car r) fn-zin-st))
                          (s (fn-zin-set 6 (+ room (fn-zin-tout fn-zin-st)) s))
                          (s (fn-zin-set 3 (- (fn-zin-n fn-zin-st) room) s)))
                     (mv (if (equal b 1) :yield :full) (1- b) ip s
                         (mv-nth 1 r) fn-zin-tab (mv-nth 2 r)))))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-zin-loop b ip end room fn-zin-st fn-octets
                                 fn-zin-win fn-zin-tab nil))
            :in-theory (e/d (fn-zin-step fn-zin-match fn-zin-need)
                           (fn-zin-bomb-limit min))))))

(local
 (defthm fn-pwz-stored-copy-fragment-unfolds
   (let* ((q (fn-pzw-quantum requested remaining))
          (credit (nfix compressed))
          (bound (min (nfix expected) (fn-pzw-stored-allowance compressed)))
          (s0 (fn-zin-set 7 (+ credit (fn-zin-tin fn-zin-st)) fn-zin-st)))
     (implies
      (and (posp q) (equal (fn-pzw-room bound (fn-zin-tout s0)) 64)
           (equal (fn-zin-mode s0) 12) (<= 64 (fn-zin-n s0))
           (<= 64 (nfix (- (fn-zin-bomb-limit s0) (fn-zin-tout s0))))
           (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab))
      (equal
       (fn-pzw-stored-chunk requested remaining start end compressed expected
                            fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
       (let* ((r (fn-zin-copy 64 (fn-zin-wpos s0) (fn-zin-dist s0)
                             (fn-zin-tout s0) (fn-zin-preset s0) fn-zin-win nil))
              (s1 (fn-zin-set 5 (car r) s0))
              (s1 (fn-zin-set 6 (+ 64 (fn-zin-tout s0)) s1))
              (s1 (fn-zin-set 3 (- (fn-zin-n s0) 64) s1))
              (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1)))
         (mv (if (equal q 1) :yield :full) (1- q) start s1
             (mv-nth 1 r) fn-zin-tab (mv-nth 2 r))))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-pzw-stored-chunk fn-pzw-chunk fn-zin-feed
                                               fn-zin-out-clear)
                           (fn-zin-loop fn-pzw-room fn-pzw-quantum
                                        fn-zin-copy fn-zin-bomb-limit min))))))

; Subject: the actual compressed controller called by the dormant native
; driver. This binds its retained decoder and private requested-window
; effects to the actual copy routine, not to a semantic host promise.
(defthm fn-pwz-actual-codec-copy-effects
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
     (let* ((copy (fn-zin-copy 64 (fn-zin-wpos s0) (fn-zin-dist s0)
                              (fn-zin-tout s0) (fn-zin-preset s0) fn-zin-win nil))
            (s1 (fn-zin-set 5 (car copy) s0))
            (s1 (fn-zin-set 6 (+ 64 (fn-zin-tout s0)) s1))
            (s1 (fn-zin-set 3 (- (fn-zin-n s0) 64) s1))
            (s1 (fn-zin-set 7 (nfix (- (fn-zin-tin s1) credit)) s1))
            (selection (fn-pzw-select (fn-zin-tout fn-zin-st) 64
                                      (nth 3 z) (nth 4 z)))
            (r (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win
                                 fn-zin-tab fn-zin-out fn-ew-buffer)))
       (and (equal (mv-nth 2 r) s1)
            (equal (mv-nth 3 r) (mv-nth 1 copy))
            (equal (mv-nth 4 r) fn-zin-tab)
            (equal (mv-nth 5 r) (mv-nth 2 copy))
            (equal (mv-nth 6 r)
                   (fn-ewb-copy (car selection) (mv-nth 1 selection)
                                (mv-nth 2 selection) (mv-nth 2 copy)
                                fn-ew-buffer))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ewz-codec-tick)
                          (fn-pzw-stored-chunk fn-zin-copy fn-ewb-copy
                           fn-ewz-state fn-pzw-select fn-pzw-room
                           fn-pzw-quantum fn-zin-bomb-limit min)))))
