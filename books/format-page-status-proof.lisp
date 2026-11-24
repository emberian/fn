; Both malformed pages and successful reads return checker status keywords.
(in-package "ACL2")
(include-book "format-check")

(local (defthm fn2-page-first-result (equal (mv-nth 0 x) (car x))))
(local
 (defthm fn2-page-select-output
   (equal (mv-nth i (cons a rest)) (if (zp i) a (mv-nth (1- i) rest)))
   :hints (("Goal" :expand (mv-nth i (cons a rest))))))

(local (in-theory (union-theories
        (set-difference-theories (theory 'minimal-theory) '(mv-nth))
        '(fn2-page-first-result fn2-page-select-output car-cons cdr-cons eq eql not
          (:e zp) (:e binary-+) (:e keywordp) (:e mv-nth) (:e equal) (:e member-equal)))))

(defmacro fn2-page-status-lemma (name call &key recursive scalar)
  `(defthm ,name
     (keywordp ,(if scalar call (list 'car call)))
     :hints (("Goal" :do-not '(preprocess)
              ,@(and recursive (list :induct call :expand (list call)))
              :in-theory (enable ,(if recursive (list :induction (car call)) (car call)))))))

(local (fn2-page-status-lemma fn2-page-handle-status (fn2-pool-handle-code slot gen pool) :scalar t))
(local (fn2-page-status-lemma fn2-page-read-access-status (fn2-pool-readable-code slot gen pk ps pg pool) :scalar t))
(local (fn2-page-status-lemma fn2-page-range-status (fn2-layout-range-code slot gen off end nil pk ps pg pool) :scalar t))
(local (fn2-page-status-lemma fn2-page-read-status (fn2-pool-read slot gen off pk ps pg pool)))
(local (fn2-page-status-lemma fn2-page-hash-read-status (fn2-b3-read slot gen off pk ps pg pool)))
(local (fn2-page-status-lemma fn2-page-hash-feed-status
  (fn2-b3-feed row slot gen off left consumed pk ps pg ds b3 pool) :recursive t))
(local (fn2-page-status-lemma fn2-page-hash-update-status (fn2-b3-update row slot gen off n pk ps pg ds b3 pool)))
(local (fn2-page-status-lemma fn2-page-span-status (fn2-fc-page-span fuel row slot gen off len base pk ps pg fc ctx b3 f pool ds)))
(local (fn2-page-status-lemma fn2-page-checked-byte-status (fn2-fc-check-byte row :page off pos byte fc ctx ds) :scalar t))
(local (fn2-page-status-lemma fn2-page-byte-status (fn2-fc-byte row :page nil slot gen off len base pk ps pg fc ctx b3 f pool ds)))
(local (fn2-page-status-lemma fn2-page-advance-status (fn2-fc-advance fuel row :page nil slot gen off len base pk ps pg fc ctx b3 f pool ds)))
(local (fn2-page-status-lemma fn2-page-run-status (fn2-fc-run-bytes fuel row :page nil slot gen off len base pk ps pg fc ctx b3 f pool ds) :recursive t))
(local (fn2-page-status-lemma fn2-page-header-byte-status (fn2-format-page-header-byte phase pos v high size payload byte)))
(local (defthm fn2-page-header-fields-consume-input
  (not (fn2-format-page-header-empty-p phase))
  :hints (("Goal" :in-theory (enable fn2-format-page-header-empty-p)))))

(local (in-theory (enable member-equal (:e unsigned-byte-p) (:e natp) (:e <) (:e member-equal))))

(local
 (defthm fn2-page-header-complete-status
   (keywordp (car (fn2-format-page-header-scan fuel base *fn2-format-page-header-phase-done*
                     pos v high size ref payload next slot gen end pk ps pg f pool)))
   :hints (("Goal" :in-theory (enable fn2-format-page-header-scan)))))

(local (fn2-page-status-lemma fn2-page-header-scan-status
  (fn2-format-page-header-scan fuel base phase pos v high size ref payload next slot gen end pk ps pg f pool) :recursive t))
(local (fn2-page-status-lemma fn2-page-header-step-status (fn2-format-page-header-decode-step base slot gen off end pk ps pg budget f pool)))
(local (fn2-page-status-lemma fn2-page-decode-step-status (fn2-fc-decode-step :page base slot gen off end pk ps pg budget f pool)))
(local (fn2-page-status-lemma fn2-page-identity-status (fn2-fc-identity row :page base len ctx f) :scalar t))
(local (fn2-page-status-lemma fn2-page-decoded-status (fn2-fc-decoded row :page off len base next fc ctx b3 f pool ds)))
(local (fn2-page-status-lemma fn2-page-step-status (fn2-fc-step row :page nil slot gen off len base pk ps pg budget fc ctx b3 f pool ds)))
(local (fn2-page-status-lemma fn2-page-format-status (fn2-format-run :page nil row slot gen off len base pk ps pg budget fc ctx b3 f pool ds)))
(fn2-page-status-lemma fn2-page-drive-status (fn2-format-drive fuel row :page nil slot gen off len base pk ps pg budget fc ctx b3 f pool ds) :recursive t)

(local
 (defthm fn2-page-reset-phase
   (equal (fn2-fc-phase 0 (fn2-fc-reset 0 fc)) *fn2-fc-phase-idle*)
   :hints (("Goal" :in-theory (e/d (fn2-fc-reset fn2-fc-phase fn2-fc-phase$ai fn2-fc-set-phase update-fn2-fc-phase$ai
                                    nth-update-nth update-nth-array (:e nfix) (:e binary-+))
                                   (mv-nth))))))

(local
 (defthm fn2-page-terminal-run-resets
   (let ((r (fn2-format-run :page nil 0 slot gen off len base pk ps pg budget fc ctx b3 f pool ds)))
     (implies (equal (car r) :ok) (equal (fn2-fc-phase 0 (mv-nth 1 r)) *fn2-fc-phase-idle*)))
   :hints (("Goal" :in-theory (enable fn2-format-run)))))

(defthmd fn2-page-accepted-drive-resets
  (let ((r (fn2-format-drive fuel 0 :page nil slot gen off len base pk ps pg budget fc ctx b3 f pool ds)))
    (implies (equal (car r) :ok)
             (equal (fn2-fc-phase 0 (mv-nth 1 r)) *fn2-fc-phase-idle*)))
  :hints (("Goal" :induct (fn2-format-drive fuel 0 :page nil slot gen off len base pk ps pg budget fc ctx b3 f pool ds)
           :expand ((fn2-format-drive fuel 0 :page nil slot gen off len base pk ps pg budget fc ctx b3 f pool ds))
           :in-theory (enable (:induction fn2-format-drive)))))
