; Budgeted search on the cursor's actual page and field rows.
(in-package "ACL2")
(include-book "runs-served")

(defthm fn2-run-seek-resumes-with-remaining-budget
  (let* ((first (fn2-run-seek sid lv steps lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool))
         (full (fn2-run-seek sid lv (+ steps extra) lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)))
    (implies (and (natp steps) (natp extra) (not (equal (car full) :more)))
             (equal (if (eq (car first) :more)
                        (fn2-run-seek sid lv extra (mv-nth 1 first) (mv-nth 2 first)
                                      (mv-nth 3 first) (mv-nth 4 first) qbase rb slot gen pk ps pg qk qs qg
                                      (mv-nth 5 first) pool)
                      first)
                    full)))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-run-seek sid lv steps lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)
           :in-theory (e/d (fn2-run-seek)
                           (fn2-run-header-value fn2-run-directory fn2-run-layout-compare
                            fn2-run-layout-decode fn2-run-restart-offset floor mv-nth)))))

(defthm fn2-run-seek-terminal-budget
  (let ((result (fn2-run-seek sid lv steps lo hi idx off qbase rb slot gen pk ps pg qk qs qg f pool)))
    (implies (and (natp steps) (natp extra) (not (equal (car result) :more)))
             (equal (fn2-run-seek sid lv (+ steps extra) lo hi idx off qbase rb slot gen
                                  pk ps pg qk qs qg f pool)
                    result)))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-run-seek sid lv steps lo hi idx off qbase rb slot gen
                                        pk ps pg qk qs qg f pool)
           :in-theory (e/d (fn2-run-seek)
                           (fn2-run-header-value fn2-run-directory fn2-run-layout-compare
                            fn2-run-layout-decode fn2-run-restart-offset floor mv-nth)))))

(local
 (defthm fn2-run-save-page-search
  (let* ((saved (fn2-run-cursor-save c *fn2-run-cursor-phase-seek* level slot gen lo hi idx off
                                     unit counter curs)) (after (mv-nth 1 saved)))
    (implies (and (natp c) (< c (fn2-run-cursors-rows curs))
                  (unsigned-byte-p 8 level) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                  (unsigned-byte-p 60 unit) (unsigned-byte-p 60 counter)
                  (unsigned-byte-p 32 lo) (unsigned-byte-p 32 hi)
                  (unsigned-byte-p 32 idx) (unsigned-byte-p 32 off))
             (and (equal (car saved) :ok)
                  (equal (fn2-run-cursors-phase c after) *fn2-run-cursor-phase-seek*)
                  (equal (fn2-run-cursors-lo c after) lo)
                  (equal (fn2-run-cursors-hi c after) hi)
                  (equal (fn2-run-cursors-idx c after) idx)
                  (equal (fn2-run-cursors-off c after) off))))
  :hints (("Goal" :in-theory
           (e/d (fn2-run-cursor-save nth-update-nth
                 fn2-run-cursors-phase fn2-run-cursors-lo fn2-run-cursors-hi
                 fn2-run-cursors-idx fn2-run-cursors-off
                 fn2-run-cursors-set-phase
                 fn2-run-cursors-set-level
                 fn2-run-cursors-set-slot
                 fn2-run-cursors-set-gen
                 fn2-run-cursors-set-lo
                 fn2-run-cursors-set-hi
                 fn2-run-cursors-set-idx
                 fn2-run-cursors-set-off
                 fn2-run-cursors-set-unit
                 fn2-run-cursors-set-counter
                 update-fn2-run-cursors-phase$ai
                 update-fn2-run-cursors-level$ai
                 update-fn2-run-cursors-slot$ai
                 update-fn2-run-cursors-gen$ai
                 update-fn2-run-cursors-lo$ai
                 update-fn2-run-cursors-hi$ai
                 update-fn2-run-cursors-idx$ai
                 update-fn2-run-cursors-off$ai
                 update-fn2-run-cursors-unit$ai
                 update-fn2-run-cursors-counter$ai)
                (fn2-run-cursors-rows nth update-nth unsigned-byte-p))))))

(defthm fn2-run-yielded-cursor-preserves-page-search
  (let* ((first (fn2-run-seek sid level steps lo hi idx off qbase rb slot gen
                              pk ps pg qk qs qg f pool))
         (full (fn2-run-seek sid level (+ steps extra) lo hi idx off qbase rb slot gen
                             pk ps pg qk qs qg f pool))
         (step (fn2-run-step-seek c sid nil level steps lo hi idx off qbase slot gen unit counter
                                  rb pk ps pg qk qs qg curs f pool))
         (after (mv-nth 1 step)))
    (implies (and (natp steps) (natp extra) (natp c) (< c (fn2-run-cursors-rows curs))
                  (unsigned-byte-p 8 level) (unsigned-byte-p 60 unit) (unsigned-byte-p 60 counter)
                  (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                  (unsigned-byte-p 32 (mv-nth 1 first)) (unsigned-byte-p 32 (mv-nth 2 first))
                  (unsigned-byte-p 32 (mv-nth 3 first)) (unsigned-byte-p 32 (mv-nth 4 first))
                  (eq (car first) :more) (not (eq (car full) :more)))
             (and (eq (car step) :more)
                  (equal (fn2-run-cursors-phase c after) *fn2-run-cursor-phase-seek*)
                  (equal (fn2-run-seek sid level extra (fn2-run-cursors-lo c after)
                                       (fn2-run-cursors-hi c after) (fn2-run-cursors-idx c after)
                                       (fn2-run-cursors-off c after) qbase rb slot gen
                                       pk ps pg qk qs qg (mv-nth 2 step) pool)
                         full))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-run-seek-resumes-with-remaining-budget (lv level)))
           :in-theory (e/d (fn2-run-step-seek)
                           (fn2-run-seek fn2-run-cursor-save fn2-run-cursors-phase
                            fn2-run-cursors-lo fn2-run-cursors-hi fn2-run-cursors-idx
                            fn2-run-cursors-off fn2-run-cursors-rows unsigned-byte-p)))))
