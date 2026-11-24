; Relate the catalog's input length to the completed builder's own row count.
(in-package "ACL2")
(include-book "range-served")
(include-book "runs-builder-input-count-proof")
(local (include-book "range-initial-writer-proof"))

(local
 (defthm fn2-range-build-starts-with-whole-input
   (let ((start (fn2-run-build-start 0 3 run 0 0 136 h hg 0 2048 1 1 9 0 1 b w p)))
     (implies (equal (car start) :ok)
              (fn2-run-input-accounted-p entries (mv-nth 1 start) entries)))
   :hints (("Goal" :use fn2-range-start-initializes-first-writer :do-not '(preprocess)
            :in-theory (union-theories (theory 'minimal-theory)
                 '(fn2-run-input-accounted-p fn2-range-empty-build-state-p (:t len) nthcdr not implies
                   (:e natp) (:e zp) (:e equal) (:e binary-+) unicity-of-0 fix))))))

(local
 (defthm fn2-range-started-build-counts-its-input
   (let* ((start (fn2-run-build-start 0 3 run 0 0 136 h hg 0 2048 1 1 9 0 1 b w p))
          (result (fn2-run-run-loop fuel layout entries src sg 0 unit nil (mv-nth 1 start)
                       curs paths cache (mv-nth 2 start) rs f (mv-nth 3 start) fc ctx b3 ds))
          (after (mv-nth 2 result)))
     (implies (and (equal (car start) :ok)
                   (equal (fn2-run-builds-phase 0 after) *fn2-run-build-phase-done*))
              (equal (fn2-run-builds-entries 0 after) (len entries))))
   :hints (("Goal" :use
            ((:instance fn2-run-completed-builder-counts-all-input
               (rows entries) (off 0) (pages nil)
               (b (mv-nth 1 (fn2-run-build-start 0 3 run 0 0 136 h hg 0 2048 1 1 9 0 1 b w p)))
               (w (mv-nth 2 (fn2-run-build-start 0 3 run 0 0 136 h hg 0 2048 1 1 9 0 1 b w p)))
               (p (mv-nth 3 (fn2-run-build-start 0 3 run 0 0 136 h hg 0 2048 1 1 9 0 1 b w p)))))
            :in-theory (union-theories (theory 'minimal-theory) '(fn2-range-build-starts-with-whole-input))))))

(defthmd fn2-range-completed-build-counts-input
  (let* ((build (fn2-rga-call fn2-rga-build 3 *fn2-overview-entry* entries k))
         (after (mv-nth 6 build)))
    (implies (and (consp entries) (equal (car build) :ok)
                  (equal (fn2-run-builds-phase 0 after) *fn2-run-build-phase-done*))
             (equal (fn2-run-builds-entries 0 after) (len entries))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (union-theories (theory 'minimal-theory)
                '(fn2-rga-build fn2-range-started-build-counts-its-input
                  (:t fn2-pool-reserve) (:t fn2-run-build-start) (:t fn2-run-run-loop)
                  (:t fn2-rga-install-pages) atom eq mv-nth car-cons cdr-cons
                  (:e mv-nth) (:e zp) (:e consp) (:e binary-+) (:e equal) (:e not))))))
