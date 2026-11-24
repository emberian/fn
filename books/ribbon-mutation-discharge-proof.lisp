; A nonzero byte mutation of a sealed filter is refused under the page evidence premise.
(in-package "ACL2")
(include-book "ribbon-mutation-proof")
(include-book "owed-discharge")
(local (include-book "ribbon-false-neg-discharge-proof"))
(local (include-book "format-page-status-proof"))
(local (include-book "ribbon-page-octets-proof"))
(local (include-book "ribbon-checked-hash-proof"))
(local (include-book "format-binds-trailer-proof"))

(local (in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
                         '(fc-mv-cons fc-mv-zero car-cons cdr-cons (:e mv-nth) (:e equal)
                           (:e natp) (:e binary-+) (:e <) (:e not) (:e zp)))))

(local
 (defthm fn2-ribbon-checked-parent-survives
   (let ((r (fn2-page-check-drive fuel fc ctx b3 f pool ds)))
     (and (keywordp (car r))
          (equal (fn2-digest-list 136 (mv-nth 5 r)) (fn2-digest-list 136 ds))
          (implies (equal (car r) :ok)
                   (equal (fn2-fc-phase 0 (mv-nth 1 r)) *fn2-fc-phase-idle*))))
   :hints (("Goal" :in-theory (enable fn2-page-drive-status fn2-page-drive-retains-parent
                                      fn2-page-accepted-drive-resets)))))

(local
 (defthm fn2-ribbon-checker-refuses-changed-input
   (let* ((old (fn2-ribbon-read-page pool)) (changed (fn2-ribbon-flipped-pool off x pool))
          (new (fn2-ribbon-read-page changed))
          (a (fn2-page-check-drive fuel fc ctx b3 f pool ds))
          (b (fn2-page-check-drive fuel (mv-nth 1 a) ctx (mv-nth 2 a) (mv-nth 3 a) changed (mv-nth 5 a))))
     (implies (and (fn2-ribbon-arena-p 0 1 9 0 1 65536 65536 pool)
                   (equal (fn2-pool-base 0 pool) 0) (fn2-poolp pool) (fn2-pool-wfp pool)
                   (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-idle*) (equal (fn2-fc-context-hash 0 ctx) 136)
                   (natp off) (< off 65536) (unsigned-byte-p 8 x) (not (equal x 0))
                   (equal (car a) :ok) (fn2-ribbon-page-integrity-premise old new))
              (and (keywordp (car b)) (not (equal (car b) :ok)))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-ribbon-mutated-window-differs
                  (:instance fn2-ribbon-page-read-represents-window (n 65536) (off 0))
                  (:instance fn2-ribbon-page-read-represents-window (n 65536) (off 0) (pool (fn2-ribbon-flipped-pool off x pool)))
                  (:instance fn2-ribbon-integrity-distinguishes-pages
                             (before (fn2-ribbon-read-page pool)) (after (fn2-ribbon-read-page (fn2-ribbon-flipped-pool off x pool))))
                  (:instance fn2-page-accepted-pair-has-same-hash
                             (bytes (fn2-ribbon-read-page pool)) (other (fn2-ribbon-read-page (fn2-ribbon-flipped-pool off x pool)))
                             (other-pool (fn2-ribbon-flipped-pool off x pool)) (other-ctx ctx)
                             (other-fc (mv-nth 1 (fn2-page-driver-call fn2-format-drive)))
                             (other-b3 (mv-nth 2 (fn2-page-driver-call fn2-format-drive)))
                             (other-f (mv-nth 3 (fn2-page-driver-call fn2-format-drive)))
                             (other-ds (mv-nth 5 (fn2-page-driver-call fn2-format-drive)))))))))

(local
 (defthm fn2-ribbon-sealed-page-check-accepts
   (implies (and (fn2-ribbon-keysp keys) (consp keys) (posp (len keys)) (<= (len keys) 256))
            (equal (car (fn2-ribbon-final-check keys)) :ok))
   :hints (("Goal" :use ((:instance fn2-ribbon-no-false-negative-proved (queries nil))
                         (:instance fn2-ribbon-image-reaches-final-drive (queries nil)))
            :in-theory (enable fn2-ribbon-no-false-negative$owed (:e fn2-ribbon-keysp) (:e len))))))

(local
 (defthm fn2-ribbon-adapter-refuses-flipped-page
   (implies (and (fn2-ribbon-keysp keys) (consp keys) (posp (len keys)) (<= (len keys) 256)
                 (natp off) (< off 65536) (unsigned-byte-p 8 x) (not (equal x 0))
                 (fn2-ribbon-mutation-premise keys off x))
            (let ((code (car (fn2-ribbon-rechecked-state keys off x))))
              (and (keywordp code) (not (equal code :ok)))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-ribbon-sealed-check-environment fn2-ribbon-sealed-page-check-accepts
                  fn2-ribbon-mutation-observes-checks
                  (:instance fn2-ribbon-checker-refuses-changed-input
                             (fuel (fn2-format-fuel 65536)) (fc (mv-nth 7 (fn2-ribbon-final-drive keys)))
                             (ctx (mv-nth 8 (fn2-ribbon-final-drive keys))) (b3 (mv-nth 9 (fn2-ribbon-final-drive keys)))
                             (f (mv-nth 5 (fn2-ribbon-final-drive keys))) (pool (mv-nth 6 (fn2-ribbon-final-drive keys)))
                             (ds (mv-nth 10 (fn2-ribbon-final-drive keys)))))
            :in-theory (e/d (fn2-ribbon-final-check fn2-ribbon-rechecked-state fn2-rba-check fc-drive-keeps-pool)
                            (fn2-ribbon-sealed-page-check-accepts))))))

(local
 (defthmd fn2-ribbon-nonempty-keys-have-positive-length
   (implies (consp keys) (posp (len keys)))
   :hints (("Goal" :expand ((len keys)) :in-theory (current-theory 'fc-u32-reconstruct)))))

(defthm fn2-ribbon-mutation-refused-proved
  (fn2-ribbon-mutation-refused$owed keys off x)
  :rule-classes nil
  :hints (("Goal" :use (fn2-ribbon-mutated-image-rechecks-page fn2-ribbon-adapter-refuses-flipped-page)
           :in-theory (enable fn2-ribbon-mutation-refused$owed fn2-ribbon-nonempty-keys-have-positive-length))))

(fn2-owed-discharge fn2-ribbon-mutation-refused fn2-ribbon-mutation-refused-proved)
