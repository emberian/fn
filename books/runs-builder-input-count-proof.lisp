; A completed build has accepted all its input, including rows retried
; after a full leaf or a full parent. Count only successful leaf appends.
(in-package "ACL2")
(include-book "runs-served")

(local
 (defthm fn2-run-row-count-after-builder-update
   (and (equal (fn2-run-builds-entries 0 (fn2-run-builds-set-entries 0 n b)) n)
        (equal (fn2-run-builds-entries 0 (fn2-run-builds-set-height 0 h b)) (fn2-run-builds-entries 0 b))
        (equal (fn2-run-builds-entries 0 (fn2-run-builds-set-pages 0 n b)) (fn2-run-builds-entries 0 b))
        (equal (fn2-run-builds-entries 0 (fn2-run-builds-set-phase 0 ph b)) (fn2-run-builds-entries 0 b)))
   :hints (("Goal" :in-theory (e/d (fn2-run-builds-entries fn2-run-builds-entries$ai
                          fn2-run-builds-set-entries update-fn2-run-builds-entries$ai
                          fn2-run-builds-set-pages update-fn2-run-builds-pages$ai
                          fn2-run-builds-set-phase update-fn2-run-builds-phase$ai
                          fn2-run-builds-set-height update-fn2-run-builds-height$ai nth-update-nth)
                         (nth update-nth))))))

(local
 (defmacro fn2-run-row-count-theory (&rest rules)
   `(union-theories (theory 'minimal-theory)
       '(mv-nth car-cons cdr-cons eq eql not member-equal
         (:e mv-nth) (:e zp) (:e consp) (:e equal) (:e binary-+) (:e member-equal)
         fn2-run-row-count-after-builder-update ,@rules))))

(local
 (defthm fn2-run-page-work-keeps-row-count
   (equal (fn2-run-builds-entries 0 (mv-nth 2 (fn2-run-build-work 0 budget b w rs f p fc ctx b3 ds)))
          (fn2-run-builds-entries 0 b))
   :hints (("Goal" :do-not '(preprocess) :in-theory (fn2-run-row-count-theory fn2-run-build-work)))))

(local
 (defthm fn2-run-page-allocation-keeps-builder
   (equal (mv-nth 1 (fn2-run-build-page 0 l slot gen unit epoch counter b w p)) b)
   :hints (("Goal" :in-theory (fn2-run-row-count-theory fn2-run-build-page fn2-run-build-page-kind)))))

(local
 (defthm fn2-run-index-promotion-keeps-row-count
   (equal (fn2-run-builds-entries 0 (mv-nth 1 (fn2-run-build-promote 0 l b w rs f p ds)))
          (fn2-run-builds-entries 0 b))
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (fn2-run-row-count-theory fn2-run-build-promote fn2-run-promote-check)))))

(local
 (defthm fn2-run-finish-keeps-row-count
   (equal (fn2-run-builds-entries 0 (mv-nth 1 (fn2-run-build-finish 0 b))) (fn2-run-builds-entries 0 b))
   :hints (("Goal" :in-theory (fn2-run-row-count-theory fn2-run-build-finish)))))

(local
 (defthm fn2-run-append-counts-accepted-row
   (let ((add (fn2-run-build-add 0 base b w rs f p)))
     (equal (fn2-run-builds-entries 0 (mv-nth 1 add))
            (if (equal (car add) :ok) (1+ (fn2-run-builds-entries 0 b)) (fn2-run-builds-entries 0 b))))
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (fn2-run-row-count-theory fn2-run-build-add fn2-run-close-full)))))

(local
 (defthm fn2-run-intake-phase-after-builder-update
   (and (equal (fn2-run-builds-phase 0 (fn2-run-builds-set-entries 0 n b)) (fn2-run-builds-phase 0 b))
        (equal (fn2-run-builds-phase 0 (fn2-run-builds-set-height 0 h b)) (fn2-run-builds-phase 0 b))
        (equal (fn2-run-builds-phase 0 (fn2-run-builds-set-pages 0 n b)) (fn2-run-builds-phase 0 b)))
   :hints (("Goal" :in-theory (e/d (fn2-run-builds-phase fn2-run-builds-phase$ai
                          fn2-run-builds-set-entries update-fn2-run-builds-entries$ai
                          fn2-run-builds-set-pages update-fn2-run-builds-pages$ai
                          fn2-run-builds-set-height update-fn2-run-builds-height$ai nth-update-nth)
                         (nth update-nth))))))

(local
 (defmacro fn2-run-input-phase-theory (&rest rules)
   `(union-theories (theory 'minimal-theory)
       '(mv-nth car-cons cdr-cons eq eql not
         (:e mv-nth) (:e zp) (:e consp) (:e equal) (:e binary-+)
         fn2-run-intake-phase-after-builder-update ,@rules))))

(local
 (defthm fn2-run-scan-before-finishing-cannot-select-root
   (not (equal (car (fn2-run-scan l b nil builds w)) :root))
   :hints (("Goal" :induct (fn2-run-scan l b nil builds w)
            :in-theory (fn2-run-input-phase-theory fn2-run-scan)))))

(local
 (defthm fn2-run-page-work-preserves-intake
   (implies (equal (fn2-run-builds-phase 0 b) *fn2-run-build-phase-adding*)
            (equal (fn2-run-builds-phase 0 (mv-nth 2 (fn2-run-build-work 0 budget b w rs f p fc ctx b3 ds)))
                   *fn2-run-build-phase-adding*))
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (fn2-run-input-phase-theory fn2-run-build-work fn2-run-scan-before-finishing-cannot-select-root)))))

(local
 (defthm fn2-run-index-promotion-preserves-phase
   (equal (fn2-run-builds-phase 0 (mv-nth 1 (fn2-run-build-promote 0 l b w rs f p ds)))
          (fn2-run-builds-phase 0 b))
   :hints (("Goal" :do-not '(preprocess)
            :in-theory (fn2-run-input-phase-theory fn2-run-build-promote fn2-run-promote-check)))))

(local
 (defthm fn2-run-append-preserves-phase
   (equal (fn2-run-builds-phase 0 (mv-nth 1 (fn2-run-build-add 0 base b w rs f p)))
          (fn2-run-builds-phase 0 b))
   :hints (("Goal" :do-not '(preprocess) :in-theory (fn2-run-input-phase-theory fn2-run-build-add)))))

(defun-nx fn2-run-input-accounted-p (entries b rows)
  (and (natp (fn2-run-builds-entries 0 b))
       (equal (+ (fn2-run-builds-entries 0 b) (len entries)) (len rows))
       (equal entries (nthcdr (fn2-run-builds-entries 0 b) rows))
       (implies (consp entries) (equal (fn2-run-builds-phase 0 b) *fn2-run-build-phase-adding*))))

(local
 (defthm fn2-run-suffix-after-one-append
   (implies (natp count) (equal (nthcdr (1+ count) rows) (cdr (nthcdr count rows))))
   :hints (("Goal" :induct (nthcdr count rows)))))

(local
 (defthm fn2-run-consume-one-count-one
   (implies (and (consp entries) (natp count))
            (and (natp (1+ count))
                 (equal (+ (1+ count) (len (cdr entries))) (+ count (len entries)))))
   :hints (("Goal" :expand ((len entries))))))

(local
 (defthm fn2-run-build-result-field
   (equal (mv-nth i (cons a b)) (if (zp i) a (mv-nth (1- i) b)))
   :hints (("Goal" :expand ((mv-nth i (cons a b)))))))

(defthmd fn2-run-build-step-accounts-for-input
  (let ((step (fn2-run-run-onestep layout entries src sg off unit pages b curs paths cache w rs f p fc ctx b3 ds)))
    (implies (fn2-run-input-accounted-p entries b rows)
             (fn2-run-input-accounted-p (mv-nth 2 step) (mv-nth 6 step) rows)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (union-theories (theory 'minimal-theory)
               '((:t fn2-run-build-work) (:t fn2-run-build-promote) (:t fn2-pool-reserve) (:t fn2-run-build-page)
                 (:t fn2-run-load-values) (:t fn2-run-build-add) (:t fn2-run-build-finish)
                 fn2-run-run-onestep fn2-run-input-accounted-p fn2-run-page-work-keeps-row-count
                 fn2-run-page-allocation-keeps-builder fn2-run-index-promotion-keeps-row-count
                 fn2-run-finish-keeps-row-count fn2-run-append-counts-accepted-row
                 fn2-run-page-work-preserves-intake fn2-run-index-promotion-preserves-phase
                 fn2-run-append-preserves-phase fn2-run-suffix-after-one-append fn2-run-consume-one-count-one
                 fn2-run-build-result-field car-cons cdr-cons eq eql not implies member-equal
                 (:e mv-nth) (:e equal) (:e zp) (:e consp) (:e binary-+) (:e unary--) (:e member-equal))))))

(local
 (defthm fn2-run-finished-input-count
   (implies (and (fn2-run-input-accounted-p entries b rows)
                 (equal (fn2-run-builds-phase 0 b) *fn2-run-build-phase-done*))
            (equal (fn2-run-builds-entries 0 b) (len rows)))
   :hints (("Goal" :cases ((consp entries)) :expand ((len entries))
            :in-theory (e/d (fn2-run-input-accounted-p) (fn2-run-builds-entries fn2-run-builds-phase))))))

(defthmd fn2-run-completed-builder-counts-all-input
  (let* ((run (fn2-run-run-loop fuel layout entries src sg off unit pages b curs paths cache w rs f p fc ctx b3 ds))
         (after (mv-nth 2 run)))
    (implies (and (fn2-run-input-accounted-p entries b rows)
                  (equal (fn2-run-builds-phase 0 after) *fn2-run-build-phase-done*))
             (equal (fn2-run-builds-entries 0 after) (len rows))))
  :hints (("Goal" :induct (fn2-run-run-loop fuel layout entries src sg off unit pages b curs paths cache w rs f p fc ctx b3 ds)
           :in-theory (union-theories (theory 'minimal-theory)
                '((:t fn2-run-run-onestep) fn2-run-run-loop fn2-run-build-step-accounts-for-input fn2-run-finished-input-count
                  fn2-run-build-result-field car-cons cdr-cons eq not (:e mv-nth) (:e zp) (:e consp) (:e binary-+) (:e equal))))
          ("Subgoal *1/2" :use
           (fn2-run-build-step-accounts-for-input
            (:instance fn2-run-finished-input-count
              (entries (mv-nth 2 (fn2-run-run-onestep layout entries src sg off unit pages b curs paths cache w rs f p fc ctx b3 ds)))
              (b (mv-nth 6 (fn2-run-run-onestep layout entries src sg off unit pages b curs paths cache w rs f p fc ctx b3 ds))))))))
