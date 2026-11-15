; Exact two-pass metadata recipe. Preview rows are not allocation reservations,
; completed writes, checked pages, or publication authority.
(in-package "ACL2")
(include-book "columns")
(include-book "c-snapshot-state")
(include-book "alloc")
(fn2-book-layer :c)

(defcolumns fn2-checkpoint-planning
 ((phase (:enum fn2-checkpoint-planning-phase (:idle :clear :preview :size :append :planned :materialize :cancel :cancel-empty :uncertain :complete)))
  (candidate :u32) (token :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (cut-commit :u60) (cut-event :u60)
  (first-free :u32) (epoch :u60) (first-counter :u60) (next-free :u32)
  (clear-row :u32) (abort-row :u32) (count :u32) (root1-count :u32) (event-pages :u32) (map-pages :u32) (arena-pages :u32) (tickets :u32) (suffix-role :u8) (suffix-ordinal :u32) (schedule :bool) (directory-proposed :u60) (sealed :u32) (position :u32) (reserved :u32)))

(defcolumns fn2-checkpoint-recipe
 ((used :bool) (creation-index :u32) (extent :u32) (epoch :u60) (allocation :u60) (next-free :u32)
  (packing (:enum fn2-checkpoint-recipe-packing (:builder :fixed-slot :journal-ticket)))
  (role :u8) (ordinal :u60) (intended :u60) (kind :u8) (level :u8)
  (sealed :bool) (issued :bool) (cursor :u32) (entries :u60) (restarts :u32)
  (word0 :u32) (word1 :u32) (word2 :u32) (word3 :u32)
  (word4 :u32) (word5 :u32) (word6 :u32) (word7 :u32)))

(defcolumns fn2-checkpoint-recipe-order ((extent :u32)))

; Loss of this predicate refuses progress; it never opens the allocator.
(defun fn2-checkpoint-planning-ownerp (c token kind owner gen fn2-checkpoint-planning fn2-csnapshot fn2-extents)
 (declare (xargs :stobjs (fn2-checkpoint-planning fn2-csnapshot fn2-extents)
  :guard (and (fn2-checkpoint-planning-wfp fn2-checkpoint-planning) (fn2-csnapshot-wfp fn2-csnapshot) (fn2-extents-wfp fn2-extents))))
 (and (< 0 (fn2-checkpoint-planning-rows fn2-checkpoint-planning))
      (posp token) (equal (fn2-alloc-freeze-phase fn2-extents) 3)
      (fn2-csnapshot-ownerp token kind owner gen fn2-csnapshot)
      (equal (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)
      (equal c (fn2-checkpoint-planning-candidate 0 fn2-checkpoint-planning))
      (equal token (fn2-checkpoint-planning-token 0 fn2-checkpoint-planning))
      (equal kind (fn2-checkpoint-planning-owner-kind 0 fn2-checkpoint-planning))
      (equal owner (fn2-checkpoint-planning-owner-slot 0 fn2-checkpoint-planning))
      (equal gen (fn2-checkpoint-planning-owner-gen 0 fn2-checkpoint-planning))
      (equal token (fn2-alloc-freeze-token fn2-extents))
      (equal kind (fn2-alloc-freeze-owner-kind fn2-extents))
      (equal owner (fn2-alloc-freeze-owner-slot fn2-extents))
      (equal gen (fn2-alloc-freeze-owner-gen fn2-extents))
      (equal (fn2-checkpoint-planning-cut-commit 0 fn2-checkpoint-planning) (fn2-csnapshot-cut-commit 0 fn2-csnapshot))
      (equal (fn2-checkpoint-planning-cut-event 0 fn2-checkpoint-planning) (fn2-csnapshot-cut-event 0 fn2-csnapshot))
      (equal (fn2-checkpoint-planning-epoch 0 fn2-checkpoint-planning) (fn2-alloc-current-epoch fn2-extents))))
