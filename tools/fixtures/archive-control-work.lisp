; Shared writer/construction/physical-completion path for an archive member run.
; A sealed page parks this producer until the existing page worker completes;
; only its verified hash may enter a parent reference.
(in-package "ACL2")
(include-book "event-archive-producer")
(fn2-book-layer :c)

(defun fn2-event-archive-builderp (fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build fn2-checkpoint-source
 fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-checkpoint-metadata fn2-run-builds fn2-run-writers)
 (declare (xargs :stobjs (fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build fn2-checkpoint-source
 fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-checkpoint-metadata fn2-run-builds fn2-run-writers)
 :guard (and (fn2-checkpoint-root1-wfp fn2-checkpoint-root1) (fn2-checkpoint-windows-wfp fn2-checkpoint-windows)
 (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoint-build-wfp fn2-checkpoint-build) (fn2-checkpoint-source-wfp fn2-checkpoint-source)
 (fn2-checkpoint-metadata-manifest-wfp fn2-checkpoint-metadata-manifest) (fn2-checkpoints-wfp fn2-checkpoints)
 (fn2-checkpoint-metadata-wfp fn2-checkpoint-metadata) (fn2-run-builds-wfp fn2-run-builds) (fn2-run-writers-wfp fn2-run-writers))))
 (and (fn2-event-archive-sourcep fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build fn2-checkpoint-source
       fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-run-builds fn2-run-writers)
      (fn2-checkpoint-metadata-ownerp fn2-checkpoint-metadata fn2-csnapshot fn2-run-builds fn2-run-writers)
      (equal (fn2-checkpoint-metadata-build 0 fn2-checkpoint-metadata) *fn2-checkpoint-source-build*)
      (equal (fn2-checkpoint-metadata-source-kind 0 fn2-checkpoint-metadata) 2)
      (equal (fn2-run-builds-schema *fn2-checkpoint-source-build* fn2-run-builds) *fn2-event-archive-schema*)
      (equal (fn2-run-builds-run *fn2-checkpoint-source-build* fn2-run-builds) (fn2-checkpoint-build-checkpoint 0 fn2-checkpoint-build))))

(fn2-event-archive-operation fn2-event-archive-finish
 (fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build fn2-checkpoint-source fn2-checkpoint-metadata-manifest
  fn2-checkpoints fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-event-read fn2-mk fn2-digests)
 (fn2-run-builds)
 (b* (((unless (and (fn2-event-archive-builderp fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build fn2-checkpoint-source
                     fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-checkpoint-metadata fn2-run-builds fn2-run-writers)
                    (equal (fn2-checkpoint-metadata-held 0 fn2-checkpoint-metadata) 0)
                    (fn2-event-read-ownerp fn2-event-read fn2-csnapshot)
                    (equal (fn2-event-read-phase 0 fn2-event-read) *fn2-event-read-phase-complete*)
                    (equal (fn2-event-read-pending 0 fn2-event-read) 0)
                    (fn2-mk-ready (fn2-event-read-checker 0 fn2-event-read) fn2-mk fn2-digests)
                    (equal (fn2-mk-size (fn2-event-read-checker 0 fn2-event-read) fn2-mk) (fn2-csnapshot-cut-event 0 fn2-csnapshot))
                    (equal (fn2-run-builds-entries *fn2-checkpoint-source-build* fn2-run-builds) (fn2-csnapshot-cut-event 0 fn2-csnapshot))
                    (equal (fn2-checkpoint-metadata-position 0 fn2-checkpoint-metadata) (fn2-csnapshot-cut-event 0 fn2-csnapshot))))
       (mv :coverage fn2-run-builds)))
  (fn2-run-build-finish *fn2-checkpoint-source-build* fn2-run-builds)))

(fn2-event-archive-operation fn2-event-archive-page-bind
 (fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build fn2-checkpoint-source fn2-checkpoint-metadata-manifest
  fn2-checkpoints fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-checkpoint-page fn2-checkpoint-page-verified
  fn2-checkpoint-construction fn2-extents fn2-pool fn2-fc fn2-fields)
 (fn2-checkpoint-page)
 (b* (((unless (and (fn2-event-archive-builderp fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build fn2-checkpoint-source
                     fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-checkpoint-metadata fn2-run-builds fn2-run-writers)
                    (equal (fn2-checkpoint-metadata-held 0 fn2-checkpoint-metadata) 1)))
       (mv :source fn2-checkpoint-page))
      (b *fn2-checkpoint-source-build*)
      (level (- (fn2-checkpoint-metadata-writer 0 fn2-checkpoint-metadata) (fn2-run-builds-wbase b fn2-run-builds)))
      ((unless (and (natp level) (< level *fn2-run-max-levels*) (< level (fn2-run-builds-height b fn2-run-builds))))
       (mv :state fn2-checkpoint-page)))
  (fn2-checkpoint-metadata-page-bind b level fn2-checkpoint-metadata fn2-csnapshot fn2-run-builds fn2-run-writers
   fn2-checkpoint-page fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents fn2-pool fn2-fc fn2-fields)))

(fn2-event-archive-operation fn2-event-archive-work
 (fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build fn2-checkpoint-source fn2-checkpoint-metadata-manifest
  fn2-checkpoints fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-run-restarts fn2-checkpoint-page fn2-checkpoint-page-verified
  fn2-checkpoint-construction fn2-extents fn2-control fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-run-restarts fn2-checkpoint-construction fn2-extents fn2-control
  fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (b* (((unless (and (fn2-event-archive-builderp fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-build fn2-checkpoint-source
                     fn2-checkpoint-metadata-manifest fn2-checkpoints fn2-checkpoint-metadata fn2-run-builds fn2-run-writers)
                    (equal (fn2-checkpoint-metadata-phase 0 fn2-checkpoint-metadata) *fn2-checkpoint-metadata-phase-feeding*)))
       (mv :source fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-run-restarts fn2-checkpoint-construction fn2-extents fn2-control fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      (b *fn2-checkpoint-source-build*)
      ; Do not advance DONE/promote state while physical completion is pending.
      ((when (equal (fn2-checkpoint-metadata-held 0 fn2-checkpoint-metadata) 1))
       (b* ((level (- (fn2-checkpoint-metadata-writer 0 fn2-checkpoint-metadata) (fn2-run-builds-wbase b fn2-run-builds)))
            ((unless (and (natp level) (< level *fn2-run-max-levels*) (< level (fn2-run-builds-height b fn2-run-builds))))
             (mv :state fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-run-restarts fn2-checkpoint-construction fn2-extents fn2-control fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
            ((mv code fn2-digests) (fn2-checkpoint-metadata-page-consume b level fn2-checkpoint-metadata fn2-csnapshot fn2-run-builds fn2-run-writers
              fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents fn2-checkpoint-page fn2-pool fn2-digests))
            (fn2-checkpoint-metadata (if (eq code :ok) (fn2-checkpoint-metadata-set-held 0 0 fn2-checkpoint-metadata) fn2-checkpoint-metadata)))
        (mv (if (eq code :ok) :more code) fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-run-restarts fn2-checkpoint-construction fn2-extents fn2-control fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
      ((mv code level fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-run-build-work b 4096 fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
      ((when (eq code :need-page))
       (b* (((unless (and (natp level) (< level *fn2-run-max-levels*)
                         (equal (fn2-checkpoint-windows-live level fn2-checkpoint-windows) 1)))
             (mv :bounds fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-run-restarts fn2-checkpoint-construction fn2-extents fn2-control fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
            ((mv code fn2-checkpoint-metadata fn2-checkpoint-construction fn2-extents fn2-control fn2-run-builds fn2-run-writers fn2-pool)
             (fn2-checkpoint-metadata-page level (fn2-checkpoint-windows-slot level fn2-checkpoint-windows)
              (fn2-checkpoint-windows-generation level fn2-checkpoint-windows) fn2-checkpoint-metadata fn2-csnapshot fn2-checkpoint-construction
              fn2-extents fn2-control fn2-run-builds fn2-run-writers fn2-pool)))
        (mv (if (eq code :ok) :more code) fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-run-restarts fn2-checkpoint-construction fn2-extents fn2-control fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
      ((when (eq code :sealed))
       (let ((fn2-checkpoint-metadata (fn2-checkpoint-metadata-put 0 (held 1) (writer (fn2-run-level-writer b level)))))
        (mv :page fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-run-restarts fn2-checkpoint-construction fn2-extents fn2-control fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
      ((when (eq code :promote))
       (b* (((mv code fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-digests)
             (fn2-checkpoint-metadata-promote b level fn2-checkpoint-metadata fn2-csnapshot fn2-checkpoint-page fn2-checkpoint-page-verified
              fn2-checkpoint-construction fn2-extents fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-digests)))
        (mv (if (member-eq code '(:ok :need-page)) :more code) fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-run-restarts fn2-checkpoint-construction fn2-extents fn2-control fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
      ((when (eq code :root))
       (b* (((unless (fn2-checkpoint-metadata-page-complete-p b level fn2-checkpoint-metadata fn2-csnapshot fn2-run-builds fn2-run-writers
                       fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents fn2-checkpoint-page fn2-pool))
             (let ((fn2-checkpoint-metadata (fn2-checkpoint-metadata-set-phase 0 *fn2-checkpoint-metadata-phase-uncertain* fn2-checkpoint-metadata)))
              (mv :source-changed fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-run-restarts fn2-checkpoint-construction fn2-extents fn2-control fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
            (fn2-checkpoint-metadata (fn2-checkpoint-metadata-set-phase 0 *fn2-checkpoint-metadata-phase-source-drained* fn2-checkpoint-metadata)))
        (mv :member-run-complete fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-run-restarts fn2-checkpoint-construction fn2-extents fn2-control fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))))
  (mv code fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-run-restarts fn2-checkpoint-construction fn2-extents fn2-control fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
