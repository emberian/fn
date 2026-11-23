; Discharges the allocator obligations owed in books/alloc.lisp:
;   fn2-alloc-release-safe      (alloc.lisp:923)
;   fn2-alloc-ids-never-repeat  (alloc.lisp:959)
; Each -proved theorem is the obligation's own $owed statement.
(in-package "ACL2")
(include-book "alloc")
(include-book "owed-discharge")

; The generated writers are disabled and each carries a -NTH frame rule; keep
; stobj reads as (nth k p) so those rules, not car/cdr expansion, do the work.
(local (in-theory (disable nth update-nth)))

; fn2-alloc-release-safe. A release code of :ok is the classifier's own :ok:
; a protector is an edge kind or nil, never :ok. fn2-alloc-free then writes
; the free state to row i and no later write touches column 0.
(local (defthm fn2-alloc-protector-list-not-ok
  (implies (not (member-equal :ok kinds))
           (not (equal (fn2-alloc-protector-list i kinds except p) :ok)))))
(local (defthm fn2-alloc-protector-not-ok
  (not (equal (fn2-alloc-protector i except p) :ok))
  :hints (("Goal" :in-theory (enable fn2-alloc-protector)))))
(local (defthm fn2-alloc-account-nth
  (implies (and (natp k) (< k 35))
           (equal (nth k (fn2-alloc-account i s r p)) (nth k p)))
  :hints (("Goal" :in-theory (enable fn2-alloc-account)))))
(local (in-theory (disable fn2-alloc-account)))
(local (defthm fn2-alloc-unlink-nth
  (implies (and (natp k) (< k 35) (not (equal k 8)) (not (equal k 9)))
           (equal (nth k (fn2-alloc-unlink i p)) (nth k p)))
  :hints (("Goal" :in-theory (enable fn2-alloc-unlink)))))
(local (in-theory (disable fn2-alloc-unlink)))
(local (defthm fn2-alloc-free-state
  (equal (fn2-extents-state i (fn2-alloc-free i p)) *fn2-extent-state-free*)
  :hints (("Goal" :in-theory (enable fn2-alloc-free)))))
(local (defthm fn2-alloc-free-nth
  (implies (member k '(31 32))
           (equal (nth k (fn2-alloc-free i p)) (nth k p)))
  :hints (("Goal" :in-theory (enable fn2-alloc-free)))))
(local (in-theory (disable fn2-alloc-free)))
(defthm fn2-alloc-release-safe-proved
  (fn2-alloc-release-safe$owed i epoch counter p)
  :hints (("Goal" :in-theory (e/d (fn2-alloc-release-safe$owed fn2-alloc-release fn2-alloc-release-code)
                                  (fn2-alloc-invp fn2-alloc-releasablep fn2-alloc-free-linksp
                                   fn2-alloc-handle-code fn2-extents-state))))
  :rule-classes nil)
(fn2-owed-discharge fn2-alloc-release-safe fn2-alloc-release-safe-proved)

; fn2-alloc-ids-never-repeat. Fields 31 and 32 are the watermark
; (fn2-alloc-current-epoch, fn2-alloc-next-counter). Every step except reserve
; and begin-epoch frames both; reserve issues the old watermark and advances
; the counter by one; begin-epoch strictly raises the epoch. The issued
; identity is fresh because fn2-alloc-rows-ok puts every live row's
; (epoch counter) strictly below the watermark.
(local (defthm fn2-alloc-account-watermark
  (implies (member k '(31 32))
           (equal (nth k (fn2-alloc-account i s r p)) (nth k p)))))
(local (defthm fn2-alloc-set-edge-nth
  (implies (member k '(31 32))
           (equal (nth k (fn2-alloc-set-edge i kind v p)) (nth k p)))
  :hints (("Goal" :in-theory (enable fn2-alloc-set-edge)))))
(local (defthm fn2-alloc-cancel-reservation-nth
  (implies (member k '(31 32))
           (equal (nth k (mv-nth 1 (fn2-alloc-cancel-reservation i epoch counter p))) (nth k p)))
  :hints (("Goal" :in-theory (e/d (fn2-alloc-cancel-reservation fn2-alloc-cancel-reservation-transition)
                                  (fn2-alloc-handle-code fn2-alloc-free-linksp fn2-extents-state))))))
(local (defthm fn2-alloc-release-nth
  (implies (member k '(31 32))
           (equal (nth k (mv-nth 1 (fn2-alloc-release i epoch counter p))) (nth k p)))
  :hints (("Goal" :in-theory (e/d (fn2-alloc-release) (fn2-alloc-release-code))))))
(local (defthm fn2-alloc-commit-allocation-nth
  (implies (member k '(31 32))
           (equal (nth k (mv-nth 1 (fn2-alloc-commit-allocation i epoch counter ok oi p))) (nth k p)))
  :hints (("Goal" :in-theory (e/d (fn2-alloc-commit-allocation)
                                  (fn2-alloc-handle-code fn2-extents-state))))))
(local (defthm fn2-alloc-retire-nth
  (implies (member k '(31 32))
           (equal (nth k (mv-nth 1 (fn2-alloc-retire i epoch counter commit p))) (nth k p)))
  :hints (("Goal" :in-theory (e/d (fn2-alloc-retire)
                                  (fn2-alloc-handle-code fn2-extents-state fn2-alloc-link-statep
                                   fn2-alloc-retirement-intentp fn2-alloc-slotp))))))
(local (defthm fn2-alloc-edge-add-nth
  (implies (member k '(31 32))
           (equal (nth k (mv-nth 1 (fn2-alloc-edge-add edge holder i epoch counter kind p edges))) (nth k p)))
  :hints (("Goal" :in-theory (e/d (fn2-alloc-edge-add)
                                  (fn2-alloc-handle-code fn2-extents-state fn2-alloc-edge-count
                                   fn2-alloc-retirement-intentp fn2-alloc-durable-edgep
                                   fn2-alloc-edge-slotp member-equal))))))
(local (defthm fn2-alloc-edge-drop-nth
  (implies (member k '(31 32))
           (equal (nth k (mv-nth 1 (fn2-alloc-edge-drop edge holder i epoch counter kind p edges))) (nth k p)))
  :hints (("Goal" :in-theory (e/d (fn2-alloc-edge-drop)
                                  (fn2-alloc-handle-code fn2-extents-state fn2-alloc-edge-count
                                   fn2-alloc-edge-matchesp fn2-alloc-edge-slotp member-equal))))))
(local (defthm fn2-alloc-checkpoint-drain-nth
  (implies (member k '(31 32))
           (equal (nth k (mv-nth 1 (fn2-alloc-checkpoint-drain cut budget p))) (nth k p)))
  :hints (("Goal" :in-theory (e/d (fn2-alloc-checkpoint-drain)
                                  (fn2-alloc-link-statep fn2-alloc-slotp fn2-extents-retirement
                                   fn2-extents-next-retired))))))
(local (defthm fn2-alloc-checkpoint-advance-nth
  (implies (member k '(31 32))
           (equal (nth k (mv-nth 1 (fn2-alloc-checkpoint-advance cut budget p))) (nth k p)))
  :hints (("Goal" :in-theory (e/d (fn2-alloc-checkpoint-advance) (fn2-alloc-checkpoint-drain))))))
(local (defthm fn2-alloc-reserve-watermark
  (and (equal (nth 31 (mv-nth 5 (fn2-alloc-reserve p))) (nth 31 p))
       (equal (nth 32 (mv-nth 5 (fn2-alloc-reserve p)))
              (if (equal (mv-nth 0 (fn2-alloc-reserve p)) :ok) (+ 1 (nth 32 p)) (nth 32 p)))
       (implies (equal (mv-nth 0 (fn2-alloc-reserve p)) :ok)
                (and (equal (mv-nth 3 (fn2-alloc-reserve p)) (nth 31 p))
                     (equal (mv-nth 4 (fn2-alloc-reserve p)) (nth 32 p)))))
  :hints (("Goal" :in-theory (e/d (fn2-alloc-reserve fn2-alloc-reserve-transition)
                                  (fn2-alloc-link-statep fn2-alloc-slotp fn2-alloc-pressure
                                   fn2-extents-next-free))))))
(local (defthm fn2-alloc-watermark-not-live
  (implies (fn2-alloc-rows-ok n p)
           (not (member-equal (list (nth 31 p) (nth 32 p))
                              (fn2-alloc-live-ids (fn2-alloc-view-aux n p)))))
  :hints (("Goal" :in-theory (disable fn2-alloc-counts-view (:e fn2-alloc-counts-view))))))
(defthm fn2-alloc-ids-never-repeat-proved
  (fn2-alloc-ids-never-repeat$owed op i epoch counter arg p edges)
  :hints (("Goal" :in-theory (e/d (fn2-alloc-ids-never-repeat$owed fn2-alloc-id-progress
                                   fn2-alloc-id-step fn2-alloc-id-progressp
                                   fn2-alloc-begin-epoch fn2-alloc-view)
                                  (fn2-alloc-reserve fn2-alloc-cancel-reservation fn2-alloc-release
                                   fn2-alloc-commit-allocation fn2-alloc-retire fn2-alloc-edge-add
                                   fn2-alloc-edge-drop fn2-alloc-checkpoint-advance
                                   fn2-alloc-rows-ok fn2-alloc-view-aux fn2-alloc-live-ids
                                   fn2-alloc-free-chain fn2-alloc-retired-chain
                                   fn2-alloc-count-state fn2-alloc-count-reason
                                   no-duplicatesp-equal))))
  :rule-classes nil)
(fn2-owed-discharge fn2-alloc-ids-never-repeat fn2-alloc-ids-never-repeat-proved)
