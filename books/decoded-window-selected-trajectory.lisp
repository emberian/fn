(in-package "ACL2")
(include-book "decoded-window-read")
(include-book "extent-window-compressed-refinement")
(local (include-book "arithmetic-5/top" :dir :system))
(local
 (defthm fn-pws-select-membership
  (implies (and (natp produced) (natp count) (<= count 64)
                (natp offset) (natp wanted) (<= wanted 16384) (natp j))
   (let ((span (fn-pzw-select produced count offset wanted)))
    (and
     (equal (and (<= (mv-nth 2 span) j)
                 (< j (+ (mv-nth 2 span) (mv-nth 1 span))))
            (and (< j wanted) (<= produced (+ offset j))
                 (< (+ offset j) (+ produced count))))
     (implies (and (<= (mv-nth 2 span) j)
                   (< j (+ (mv-nth 2 span) (mv-nth 1 span))))
      (equal (+ (car span) (- j (mv-nth 2 span)))
             (- (+ offset j) produced))))))
  :hints (("Goal" :in-theory (enable fn-pzw-select)))))
(local
 (defthm fn-pws-nth-append
  (implies (natp j)
   (equal (nth j (append a b))
          (if (< j (len a)) (nth j a) (nth (- j (len a)) b))))))
(local
 (defthm fn-pws-actual-selected-copy-accumulates
  (implies
   (and (natp offset) (natp wanted) (<= wanted 16384) (natp j)
        (<= (len scratch) 64)
        (implies (and (< j wanted) (< (+ offset j) (len prefix)))
                 (equal (nth j (nth 0 fn-ew-buffer))
                        (nth (+ offset j) prefix))))
   (let* ((span (fn-pzw-select (len prefix) (len scratch) offset wanted))
          (next (fn-ewb-copy (car span) (mv-nth 1 span) (mv-nth 2 span)
                             scratch fn-ew-buffer)))
    (implies (and (< j wanted) (< (+ offset j) (+ (len prefix) (len scratch))))
             (equal (nth j (nth 0 next))
                    (nth (+ offset j) (append prefix scratch))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-pws-select-membership
                    (produced (len prefix)) (count (len scratch)))
                 (:instance fn-ewb-copy-exact-output-and-effects
                    (src (car (fn-pzw-select (len prefix) (len scratch) offset wanted)))
                    (count (mv-nth 1 (fn-pzw-select (len prefix) (len scratch) offset wanted)))
                    (dst (mv-nth 2 (fn-pzw-select (len prefix) (len scratch) offset wanted)))
                    (fn-octets scratch)))
           :in-theory (disable fn-pzw-select fn-ewb-copy)))))

(local
 (defthm fn-pws-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

; The actual host-called codec tick carries the selected decoded prefix.
; PREFIX is the already-produced semantic output, not another decoder.
; The buffer premise concerns only the cell being observed; no runtime scan.
(defthm fn-pws-actual-codec-tick-carries-selected-prefix
 (implies
  (and (equal (nth 0 z) :codec)
       (natp (nth 6 z)) (natp (nth 7 z)) (<= (nth 6 z) (nth 7 z))
       (<= (- (nth 7 z) (nth 6 z)) 64)
       (<= (nth 7 z) (fn-octets-len fn-octets))
       (natp (nth 3 z)) (natp (nth 4 z)) (<= (nth 4 z) 16384)
       (natp j) (equal (fn-zin-tout fn-zin-st) (len prefix))
       (equal (len fn-zin-win) *fn-zin-win-octets*)
       (equal (len fn-zin-tab) *fn-zin-tab-octets*)
       (implies (and (< j (nth 4 z)) (< (+ (nth 3 z) j) (len prefix)))
                (equal (nth j (nth 0 fn-ew-buffer))
                       (nth (+ (nth 3 z) j) prefix))))
  (let* ((r (fn-pzw-stored-chunk 1024 (nth 5 z) (nth 6 z) (nth 7 z)
                                 (nth 12 (nth 1 z)) (nth 2 z)
                                 fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
         (model (append prefix (mv-nth 6 r)))
         (next (fn-ewz-codec-tick z fn-octets fn-zin-st fn-zin-win fn-zin-tab fn-zin-out fn-ew-buffer)))
   (and (equal (fn-zin-tout (mv-nth 2 next)) (len model))
        (implies (and (< j (nth 4 z)) (< (+ (nth 3 z) j) (len model)))
                 (equal (nth j (nth 0 (mv-nth 6 next)))
                        (nth (+ (nth 3 z) j) model))))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-pws-actual-selected-copy-accumulates
                  (offset (nth 3 z)) (wanted (nth 4 z))
                  (scratch (mv-nth 6 (fn-pzw-stored-chunk 1024 (nth 5 z) (nth 6 z) (nth 7 z)
                                 (nth 12 (nth 1 z)) (nth 2 z)
                                 fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
                (:instance fn-pzw-stored-chunk-counts-real-input
                  (requested 1024) (remaining (nth 5 z)) (start (nth 6 z)) (end (nth 7 z))
                  (compressed (nth 12 (nth 1 z))) (expected (nth 2 z))))
          :in-theory (e/d (fn-ewz-codec-tick fn-ewz-state)
                          (fn-pzw-stored-chunk fn-pzw-select fn-ewb-copy
                           fn-pzw-stored-chunk-is-resumable-run fn-zin-feed-unfolds
                           fn-pzw-stored-decision fn-pzw-budget-left fn-pzw-quantum
                           fn-ewz-compressed-completep fn-ewz-decision-mode))))
 :rule-classes nil)
