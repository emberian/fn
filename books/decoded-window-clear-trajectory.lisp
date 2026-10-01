; The actual codec wrapper clears scratch after every returned quantum.
; This boundary preserves prior output across those concrete scratch clears.
; Generic partial-output yields do not imply fixed-1024 caller reachability.
(in-package "ACL2")
(include-book "decoded-window-yield-trajectory")
(include-book "decoded-window-stored-trajectory")

(local
 (defthm fn-pwy-clear-loop-normalized-frontier
  (equal (fn-zin-loop b ip end (nfix lim) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
         (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
  :rule-classes nil
  :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (e/d (fn-zin-loop)
    (fn-zin-step fn-zin-act fn-zin-pull fn-zin-need fn-zin-step-out-free fn-zin-loop-counts fn-zin-act-counts fn-zin-step-counts))))))

(local
 (defthm fn-pwy-clear-loop-at-full-frontier-by-definition
  (implies (<= (nfix lim) (len fn-zin-out))
   (equal (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
    (mv (if (zp b) :yield :full) (if (zp b) 0 b) ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
  :hints (("Goal" :in-theory (e/d (fn-zin-loop) (fn-zin-step fn-zin-act fn-zin-pull fn-zin-need))))))

(defthm fn-pwy-actual-cleared-loop-preserves-complete-prefix-effects
 (implies (true-listp prefix)
  (let ((r (fn-zin-loop b ip end (nfix (- (nfix lim) (len prefix)))
                          fn-zin-st fn-octets fn-zin-win fn-zin-tab nil)))
   (equal (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab prefix)
    (mv (car r) (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r) (mv-nth 5 r)
        (append prefix (mv-nth 6 r))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :cases ((<= (len prefix) (nfix lim)))
  :use ((:instance fn-zin-loop-out-free
    (lim (nfix (- (nfix lim) (len prefix)))) (fn-zin-out prefix))
        (:instance fn-pwy-clear-loop-normalized-frontier (fn-zin-out prefix)))
  :in-theory (e/d (nfix)
   (fn-zin-loop fn-zin-step fn-zin-act fn-zin-pull fn-zin-need fn-zin-loop-out-free)))))

(local
 (defthm fn-pwy-feed-retains-cleared-prefix
  (implies (true-listp prefix)
   (equal (fn-zin-feed b fn-zin-st start end (+ (nfix room) (len prefix))
                        fn-octets fn-zin-win fn-zin-tab prefix)
    (let ((r (fn-zin-feed b fn-zin-st start end room fn-octets fn-zin-win fn-zin-tab nil)))
     (mv (car r) (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r) (mv-nth 5 r)
         (append prefix (mv-nth 6 r))))))
  :hints (("Goal" :use (:instance fn-zin-loop-out-free (ip start) (lim room) (fn-zin-out prefix))
   :in-theory (e/d (fn-zin-feed) (fn-zin-loop fn-zin-loop-out-free))))))

(defthm fn-pwy-actual-stored-cleared-chunk-complete-prefix-effects
 (implies (true-listp prefix)
  (let* ((r (fn-pzw-stored-chunk requested remaining start end compressed expected
                               fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
         (credited (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st))
         (room (fn-pzw-room (min (nfix expected) (fn-pzw-stored-allowance compressed))
                            (fn-zin-tout credited))))
   (equal (mv (car r) (mv-nth 1 r) (mv-nth 2 r)
              (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin (mv-nth 3 r))) (mv-nth 3 r))
              (mv-nth 4 r) (mv-nth 5 r) (append prefix (mv-nth 6 r)))
          (fn-zin-feed (fn-pzw-quantum requested remaining) credited start end
                       (+ (nfix room) (len prefix)) fn-octets fn-zin-win fn-zin-tab prefix))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-pwzc-actual-stored-chunk-recredited-full-tuple)
        (:instance fn-pwy-feed-retains-cleared-prefix
          (b (fn-pzw-quantum requested remaining))
          (fn-zin-st (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st))
          (room (fn-pzw-room (min (nfix expected) (fn-pzw-stored-allowance compressed))
                             (fn-zin-tout (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st))))))
  :in-theory (disable fn-pzw-stored-chunk fn-zin-feed fn-zin-loop fn-zin-set$inline fn-pzw-quantum fn-pzw-room fn-pzw-stored-allowance min nfix))))
