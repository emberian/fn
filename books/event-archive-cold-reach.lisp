; Archive page adapters share the real cold map/descriptor generation. No
; allocator state, source edge, or serving readiness is reconstructed here.
(in-package "ACL2")
(include-book "event-archive-cold-read")
(include-book "checkpoint-restore-reach")
(fn2-book-layer :c)
(defun fn2-event-archive-cold-reach-current-p (fn2-event-archive fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
 fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control)
 (declare (xargs :stobjs (fn2-event-archive fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control)
 :guard (and (fn2-event-archive-wfp fn2-event-archive) (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs)
             (fn2-checkpoint-bytes-wfp fn2-checkpoint-bytes) (fn2-checkpoint-restore-map-wfp fn2-checkpoint-restore-map)
             (fn2-checkpoint-restore-map-control-wfp fn2-checkpoint-restore-map-control) (fn2-checkpoint-restore-reach-control-wfp fn2-checkpoint-restore-reach-control))))
 (and (fn2-event-archive-cold-source-p fn2-event-archive fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes)
      (fn2-checkpoint-restore-reach-current-p fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control)
      (equal (fn2-event-archive-candidate 1 fn2-event-archive) (fn2-checkpoint-restore-reach-control-candidate 0 fn2-checkpoint-restore-reach-control))
      (posp (fn2-event-archive-source-generation 1 fn2-event-archive))
      (equal (fn2-event-archive-source-generation 1 fn2-event-archive) (fn2-checkpoint-restore-reach-control-generation 0 fn2-checkpoint-restore-reach-control))))

(defun fn2-event-archive-reached-page-p (unit epoch allocation fn2-checkpoint-restore-reach fn2-checkpoint-restore-reach-control)
 (declare (xargs :stobjs (fn2-checkpoint-restore-reach fn2-checkpoint-restore-reach-control)
 :guard (and (fn2-checkpoint-restore-reach-wfp fn2-checkpoint-restore-reach) (fn2-checkpoint-restore-reach-control-wfp fn2-checkpoint-restore-reach-control))))
 (let ((e (floor (nfix unit) *fn2-storage-extent-units*)))
  (and (natp unit) (equal (mod unit *fn2-storage-extent-units*) 0)
       (< e (fn2-checkpoint-restore-reach-rows fn2-checkpoint-restore-reach))
       (< 0 (fn2-checkpoint-restore-reach-control-rows fn2-checkpoint-restore-reach-control))
       (posp (fn2-checkpoint-restore-reach-control-generation 0 fn2-checkpoint-restore-reach-control))
       (equal (fn2-checkpoint-restore-reach-generation e fn2-checkpoint-restore-reach) (fn2-checkpoint-restore-reach-control-generation 0 fn2-checkpoint-restore-reach-control))
       (equal (fn2-checkpoint-restore-reach-state e fn2-checkpoint-restore-reach) *fn2-checkpoint-restore-reach-state-mapped*)
       (equal (fn2-checkpoint-restore-reach-epoch e fn2-checkpoint-restore-reach) epoch)
       (equal (fn2-checkpoint-restore-reach-allocation e fn2-checkpoint-restore-reach) allocation)
       (logbitp *fn2-checkpoint-restore-reach-role-event-archive* (fn2-checkpoint-restore-reach-role-bits e fn2-checkpoint-restore-reach)))))

(fn2-event-archive-operation fn2-event-archive-cold-header-reach
 (fn2-event-archive fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-extents fn2-checkpoint-restore-reader
  fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach fn2-checkpoint-restore-reach-control
  fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (fn2-event-archive fn2-checkpoint-restore-reader fn2-checkpoint-restore-reach fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (b* (((unless (and (fn2-checkpoint-restore-reach-current-p fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control)
                    (< 0 (fn2-checkpoint-restore-reader-rows fn2-checkpoint-restore-reader))
                    (equal (fn2-checkpoint-restore-reader-candidate 0 fn2-checkpoint-restore-reader) (fn2-checkpoint-restore-reach-control-candidate 0 fn2-checkpoint-restore-reach-control))
                    (posp (fn2-checkpoint-restore-reach-control-generation 0 fn2-checkpoint-restore-reach-control))))
       (mv :source fn2-event-archive fn2-checkpoint-restore-reader fn2-checkpoint-restore-reach fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((mv code fn2-event-archive fn2-checkpoint-restore-reader fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-event-archive-cold-header-step fn2-event-archive fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-extents fn2-checkpoint-restore-reader
        fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((unless (eq code :header))
       (mv code fn2-event-archive fn2-checkpoint-restore-reader fn2-checkpoint-restore-reach fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((mv code fn2-checkpoint-restore-reach) (fn2-checkpoint-restore-reach-claim *fn2-checkpoint-restore-reach-role-event-archive*
        (fn2-event-archive-header-unit 1 fn2-event-archive) (fn2-event-archive-header-epoch 1 fn2-event-archive) (fn2-event-archive-header-allocation 1 fn2-event-archive)
        fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach fn2-checkpoint-restore-reach-control))
      (fn2-event-archive (if (eq code :ok) (fn2-event-archive-set-source-generation 1
        (fn2-checkpoint-restore-reach-control-generation 0 fn2-checkpoint-restore-reach-control) fn2-event-archive) fn2-event-archive)))
  (mv (if (eq code :ok) :header code) fn2-event-archive fn2-checkpoint-restore-reader fn2-checkpoint-restore-reach fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))

(fn2-event-archive-operation fn2-event-archive-cold-step-reach
 (fn2-event-archive fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control
  fn2-checkpoint-restore-reach fn2-checkpoint-restore-reach-control fn2-run-loads fn2-run-cursors fn2-run-paths fn2-run-cache
  fn2-boot-config fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (fn2-event-archive fn2-checkpoint-restore-reach fn2-run-loads fn2-run-cursors fn2-run-paths fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (:bytes *fn2-run-entry-visit-bytes*)
 (b* (((unless (and (fn2-event-archive-cold-reach-current-p fn2-event-archive fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                     fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach-control)
                    (fn2-b-fixed-cursor-rows-p (fn2-run-loads-rows fn2-run-loads))
                    (equal (fn2-run-loads-rows fn2-run-loads) (fn2-run-cursors-rows fn2-run-cursors))))
       (mv :source fn2-event-archive fn2-checkpoint-restore-reach fn2-run-loads fn2-run-cursors fn2-run-paths fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      (c (fn2-b-event-archive-cursor-from-rows (fn2-run-loads-rows fn2-run-loads)))
      ((unless (or (not (equal (fn2-run-loads-phase c fn2-run-loads) *fn2-run-load-phase-ready*))
                   (equal (fn2-run-cursors-phase c fn2-run-cursors) *fn2-run-cursor-phase-miss*)
                   (fn2-event-archive-reached-page-p (fn2-run-loads-unit c fn2-run-loads) (fn2-run-loads-epoch c fn2-run-loads)
                    (fn2-run-loads-allocation c fn2-run-loads) fn2-checkpoint-restore-reach fn2-checkpoint-restore-reach-control)))
       (mv :reach fn2-event-archive fn2-checkpoint-restore-reach fn2-run-loads fn2-run-cursors fn2-run-paths fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((mv code fn2-event-archive fn2-run-loads fn2-run-cursors fn2-run-paths fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-event-archive-cold-cursor-step fn2-event-archive fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-run-loads fn2-run-cursors fn2-run-paths fn2-run-cache
        fn2-boot-config fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((mv claimed fn2-checkpoint-restore-reach)
       (if (eq code :ready)
        (fn2-checkpoint-restore-reach-claim *fn2-checkpoint-restore-reach-role-event-archive*
         (fn2-run-loads-unit c fn2-run-loads) (fn2-run-loads-epoch c fn2-run-loads) (fn2-run-loads-allocation c fn2-run-loads)
         fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-reach fn2-checkpoint-restore-reach-control)
        (mv :ok fn2-checkpoint-restore-reach))))
  (mv (if (eq claimed :ok) code claimed) fn2-event-archive fn2-checkpoint-restore-reach fn2-run-loads fn2-run-cursors fn2-run-paths fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
