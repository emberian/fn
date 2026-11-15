; Actual fresh member-run capture before source build1 is reused for root3's
; manifest. Root1's completed manifest build2 remains the live authority source.
(in-package "ACL2")
(include-book "event-archive-work")
(include-book "event-archive-state")
(include-book "event-archive-format")
(fn2-book-layer :c)




(defun fn2-event-archive-copy-digest (r kind i row fn2-digests fn2-event-archive)
 (declare (xargs :stobjs (fn2-digests fn2-event-archive) :measure (nfix (- 8 (nfix i)))
 :guard (and (fn2-digests-wfp fn2-digests) (fn2-event-archive-wfp fn2-event-archive)
             (natp r) (< r 2) (member-eq kind '(:member :manifest :cut-seal)) (natp i) (<= i 8) (fn2-digest-rowp row fn2-digests))))
 (if (>= (nfix i) 8) fn2-event-archive
  (let ((fn2-event-archive (update-fn2-event-archive-wordsi
          (+ (* r 24) (case kind (:member 0) (:manifest 8) (otherwise 16)) i)
          (fn2-digest-word row i fn2-digests) fn2-event-archive)))
   (fn2-event-archive-copy-digest r kind (+ 1 (nfix i)) row fn2-digests fn2-event-archive))))
(fn2-event-archive-preserves fn2-event-archive-copy-digest (r kind i row fn2-digests fn2-event-archive) :position nil)

(fn2-event-archive-operation fn2-event-archive-fresh-start
 (fn2-event-archive fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build fn2-checkpoint-source
  fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-fc fn2-fields fn2-pool fn2-commit-root)
 (fn2-event-archive fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-pool)
 (b* (((unless (and (< 1 (fn2-event-archive-rows fn2-event-archive))
                    (equal (fn2-event-archive-phase 1 fn2-event-archive) *fn2-event-archive-phase-idle*)
                    (< 0 (fn2-commit-root-rows fn2-commit-root))
                    (equal (fn2-commit-root-base-batch 0 fn2-commit-root) 0)
                    (equal (fn2-commit-root-base-event 0 fn2-commit-root) 0)))
       (mv :base fn2-event-archive fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-pool))
      ((mv code fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-pool)
       (fn2-event-archive-begin fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build fn2-checkpoint-source
        fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-fc fn2-fields fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-event-archive fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-pool))
      (cut (fn2-csnapshot-cut-event 0 fn2-csnapshot))
      (fn2-event-archive (fn2-event-archive-put 1 (phase *fn2-event-archive-phase-members*) (origin *fn2-event-archive-origin-fresh*)
       (token (fn2-checkpoint-root1-token 0 fn2-checkpoint-root1))
       (owner-kind (fn2-checkpoint-root1-owner-kind 0 fn2-checkpoint-root1))
       (owner-slot (fn2-checkpoint-root1-owner-slot 0 fn2-checkpoint-root1)) (owner-gen (fn2-checkpoint-root1-owner-gen 0 fn2-checkpoint-root1))
       (candidate (fn2-checkpoint-build-candidate 0 fn2-checkpoint-build)) (checkpoint (fn2-checkpoint-build-checkpoint 0 fn2-checkpoint-build))
       (history (fn2-checkpoint-build-history 0 fn2-checkpoint-build)) (incarnation (fn2-checkpoint-build-history-incarnation 0 fn2-checkpoint-build))
       (cut-commit (fn2-csnapshot-cut-commit 0 fn2-csnapshot)) (cut-event cut) (previous-cut 0) (previous-event 0)
       (first-event (if (equal cut 0) 0 1)) (last-event cut) (member-runs (if (equal cut 0) 0 1))
       (manifest-entries 0) (member-unit 0) (member-epoch 0) (member-allocation 0) (member-height 0) (member-entries 0)
       (manifest-unit 0) (manifest-epoch 0) (manifest-allocation 0) (manifest-height 0)
       (header-unit 0) (header-epoch 0) (header-allocation 0) (source-tag 0) (source-generation 0) (scan 0) (next-event 1))))
  (mv :ok fn2-event-archive fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-pool)))

; The source Ref comes only from the actual completed writer/page verification.
; Capture before resetting build1 for schema10; there is no supplied Ref or hash.
(fn2-event-archive-operation fn2-event-archive-capture-member
 (fn2-event-archive fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build fn2-checkpoint-source
  fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-event-read
  fn2-checkpoint-page fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents fn2-pool fn2-fc fn2-digests
  fn2-checkpoint-summary-authority fn2-checkpoint-refs fn2-checkpoint-bytes fn2-commit-root fn2-alloc-edges fn2-ops
  fn2-checkpoint-restore-events fn2-checkpoint-restore-events-work)
 (fn2-event-archive fn2-digests)
 (b* (((unless (and (fn2-event-archive-ownerp 1 fn2-event-archive fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build
                     fn2-checkpoint-source fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-run-builds fn2-run-writers)
                    (equal (fn2-event-archive-phase 1 fn2-event-archive) *fn2-event-archive-phase-members*)
                    (equal (fn2-event-archive-origin 1 fn2-event-archive) *fn2-event-archive-origin-fresh*)
                    (fn2-event-archive-builderp fn2-event-archive fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build fn2-checkpoint-source
                     fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-checkpoint-metadata fn2-run-builds fn2-run-writers)
                    (fn2-event-read-ownerp fn2-event-read fn2-csnapshot)
                    (equal (fn2-event-read-phase 0 fn2-event-read) *fn2-event-read-phase-complete*)
                    (equal (fn2-run-builds-phase *fn2-checkpoint-source-build* fn2-run-builds) *fn2-run-build-phase-done*)
                    (equal (fn2-run-builds-entries *fn2-checkpoint-source-build* fn2-run-builds) (fn2-event-archive-cut-event 1 fn2-event-archive))))
       (mv :source fn2-event-archive fn2-digests))
      (b *fn2-checkpoint-source-build*) (empty (equal (fn2-event-archive-cut-event 1 fn2-event-archive) 0))
      (level (nfix (- (fn2-run-builds-height b fn2-run-builds) 1)))
      ((unless (or empty
                   (and (equal (fn2-checkpoint-metadata-phase 0 fn2-checkpoint-metadata) *fn2-checkpoint-metadata-phase-source-drained*)
                        (fn2-checkpoint-metadata-page-complete-p b level fn2-checkpoint-metadata fn2-csnapshot fn2-run-builds fn2-run-writers
                         fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents fn2-checkpoint-page fn2-pool))))
       (mv :page-pending fn2-event-archive fn2-digests))
      (seal (fn2-b-event-expected-digest (fn2-fc-rows fn2-fc) (fn2-extents-rows fn2-extents)))
      ((unless (fn2-digest-rowp seal fn2-digests)) (mv :bounds fn2-event-archive fn2-digests))
      ((mv code fn2-digests) (fn2-event-source-seal (fn2-event-archive-cut-commit 1 fn2-event-archive) seal
        fn2-checkpoint-summary-authority fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-commit-root fn2-extents fn2-alloc-edges
        fn2-ops fn2-fc fn2-checkpoint-restore-events fn2-checkpoint-restore-events-work fn2-digests))
      ((unless (eq code :ok)) (mv code fn2-event-archive fn2-digests))
      (fn2-event-archive (fn2-event-archive-copy-digest 1 :cut-seal 0 seal fn2-digests fn2-event-archive))
      ((when empty)
       (let ((fn2-event-archive (fn2-event-archive-put 1 (phase *fn2-event-archive-phase-member-complete*) (member-pages 0))))
        (mv :ok fn2-event-archive fn2-digests)))
      (writer (fn2-run-level-writer b level))
      (extent (floor (fn2-run-writers-unit writer fn2-run-writers) *fn2-storage-extent-units*))
      ((mv code fn2-digests) (fn2-checkpoint-metadata-page-consume b level fn2-checkpoint-metadata fn2-csnapshot fn2-run-builds fn2-run-writers
        fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents fn2-checkpoint-page fn2-pool fn2-digests))
      ((unless (eq code :ok)) (mv code fn2-event-archive fn2-digests))
      (hash (+ (fn2-run-builds-hbase b fn2-run-builds) level))
      ((unless (and (< extent (fn2-checkpoint-page-verified-rows fn2-checkpoint-page-verified)) (fn2-digest-rowp hash fn2-digests)))
       (mv :bounds fn2-event-archive fn2-digests))
      (fn2-event-archive (fn2-event-archive-copy-digest 1 :member 0 hash fn2-digests fn2-event-archive))
      (fn2-event-archive (fn2-event-archive-put 1 (phase *fn2-event-archive-phase-member-complete*)
       (member-unit (fn2-run-writers-unit writer fn2-run-writers)) (member-epoch (fn2-run-writers-epoch writer fn2-run-writers))
       (member-allocation (fn2-run-writers-counter writer fn2-run-writers)) (member-height (fn2-run-builds-height b fn2-run-builds))
       (member-entries (fn2-run-builds-entries b fn2-run-builds)) (member-pages (fn2-run-builds-pages b fn2-run-builds)))))
  (mv :ok fn2-event-archive fn2-digests)))
