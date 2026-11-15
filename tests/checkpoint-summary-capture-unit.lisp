; Actual run writer -> typed cold entry -> catalog capture. The existing
; fixture's descriptor/map/page-authentication premises are synthetic: this
; does not witness persisted boot, selected adoption or sufficient summary.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint-restore-semantic-work-unit")
(include-book "../books/checkpoint-summary-catalog")
(defun fn2-csc-body (mode fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader
 fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-fields fn2-pool fn2-checkpoint-restore-semantic
 fn2-run-writers fn2-run-restarts fn2-checkpoint-summary fn2-checkpoint-summary-sources)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader
 fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-fields fn2-pool fn2-checkpoint-restore-semantic
 fn2-run-writers fn2-run-restarts fn2-checkpoint-summary fn2-checkpoint-summary-sources) :verify-guards nil))
 (b* (((mv intake fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader
        fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-fields fn2-pool fn2-checkpoint-restore-semantic)
       (fn2-crsu-body :children fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader
        fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-fields fn2-pool fn2-checkpoint-restore-semantic))
      (fn2-checkpoint-summary (fn2-checkpoint-summary-init 1 fn2-checkpoint-summary))
      (fn2-checkpoint-summary-sources (fn2-checkpoint-summary-sources-init 6 fn2-checkpoint-summary-sources))
      ((mv begun fn2-checkpoint-summary) (fn2-checkpoint-summary-begin fn2-checkpoint-summary fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
        fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-checkpoint-restore-semantic))
      (fn2-fields (fn2-fields-init 512 fn2-fields))
      (fn2-run-writers (fn2-run-writers-init 1 fn2-run-writers))
      (fn2-run-restarts (fn2-run-restarts-init *fn2-run-restart-capacity* fn2-run-restarts))
      (slot (fn2-checkpoint-restore-semantic-slot 0 fn2-checkpoint-restore-semantic))
      (gen (fn2-checkpoint-restore-semantic-gen 0 fn2-checkpoint-restore-semantic))
      ((mv opened fn2-run-writers fn2-pool)
       (fn2-run-open 0 slot gen 10 1 0 7 0 *page-kind-manifest* *fn2-storage-extent-units* 4 31 0 0 7 0 1 0 *fn2-format-page-size* fn2-run-writers fn2-pool))
      ((mv zeroed fn2-pool) (fn2-run-zero 32 slot gen 20000 7 0 1 fn2-pool))
      (eb 200)
      (fn2-fields (fn2-fields-set-value (+ eb *fn2-manifest-entry-field-schema*) 3 fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ eb *fn2-manifest-entry-field-run*) (if (eq mode :rank) 2 1) fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ eb *fn2-manifest-entry-field-height*) 1 fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ eb *fn2-manifest-entry-field-entries*) 0 fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ eb *fn2-manifest-entry-field-root-unit*) (* 5 *fn2-storage-extent-units*) fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ eb *fn2-manifest-entry-field-root-epoch*) 4 fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ eb *fn2-manifest-entry-field-root-allocation*) 35 fn2-fields))
      (fn2-fields (fn2-fields-put (+ eb *fn2-manifest-entry-field-root-hash*) (value 1) (ref-slot slot) (ref-gen gen) (ref-off 20000) (ref-len 32)))
      (fn2-fields (fn2-fields-put (+ eb *fn2-manifest-entry-field-filter-hash*) (value 1) (ref-slot slot) (ref-gen gen) (ref-off 20000) (ref-len 32)))
      ((mv added fn2-run-writers fn2-run-restarts fn2-fields fn2-pool) (fn2-run-add 0 10 eb fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
      ((mv closed fn2-run-writers) (fn2-run-close 0 fn2-run-writers))
      ((mv padded fn2-run-writers fn2-fields fn2-pool) (fn2-crsw-close 64 fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
      ((mv headed fn2-run-writers fn2-fields fn2-pool) (fn2-run-head 0 fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
      ; Isolate the catalog seam after the actual typed writer. This is the
      ; same explicit authentication premise as the included DFS control.
      (fn2-checkpoint-restore-semantic (fn2-checkpoint-restore-semantic-put 0
       (phase *fn2-checkpoint-restore-semantic-phase-entries*) (field-base 256) (checker-row 0)
       (schema 10) (run 7) (level 0) (entries 1) (cursor 0) (seen 0) (directory 1) (entry-stage 0)))
      (fn2-checkpoint-restore-map-control (if (eq mode :stale)
       (fn2-checkpoint-restore-map-control-set-reach-generation 0
        (+ 1 (fn2-checkpoint-restore-map-control-reach-generation 0 fn2-checkpoint-restore-map-control)) fn2-checkpoint-restore-map-control)
       fn2-checkpoint-restore-map-control))
      ((mv captured fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-fields)
       (fn2-checkpoint-summary-capture 256 fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-restore-semantic
        fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-fields fn2-pool))
      ((mv repeated fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-fields)
       (fn2-checkpoint-summary-capture 256 fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-restore-semantic
        fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-fields fn2-pool)))
  (mv (and intake (eq begun :ok) (eq opened :ok) (eq zeroed :ok) (eq added :ok) (eq closed :ok) (eq padded :ok) (eq headed :ok)
       (= (fn2-checkpoint-restore-semantic-cursor 0 fn2-checkpoint-restore-semantic) 0)
       (if mode
        (and (eq captured (if (eq mode :rank) :rank :source)) (= (fn2-checkpoint-summary-count 0 fn2-checkpoint-summary) 0)
             (= (fn2-checkpoint-summary-sources-tag 5 fn2-checkpoint-summary-sources) 0))
        (and (eq captured :captured) (eq repeated :captured) (= (fn2-checkpoint-summary-count 0 fn2-checkpoint-summary) 1)
             (= (fn2-checkpoint-summary-sources-schema 5 fn2-checkpoint-summary-sources) 3)
             (= (fn2-checkpoint-summary-sources-rank 5 fn2-checkpoint-summary-sources) 1)
             (= (fn2-checkpoint-summary-sources-allocation 5 fn2-checkpoint-summary-sources) 35))))
   fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control
   fn2-fields fn2-pool fn2-checkpoint-restore-semantic fn2-run-writers fn2-run-restarts fn2-checkpoint-summary fn2-checkpoint-summary-sources)))
(defun fn2-csc-test (mode)
 (declare (xargs :verify-guards nil))
 (fn2-run-with-local (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader fn2-checkpoint-restore-map
 fn2-checkpoint-restore-map-control fn2-fields fn2-pool fn2-checkpoint-restore-semantic fn2-run-writers fn2-run-restarts fn2-checkpoint-summary fn2-checkpoint-summary-sources)
  (fn2-csc-body mode fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader fn2-checkpoint-restore-map
   fn2-checkpoint-restore-map-control fn2-fields fn2-pool fn2-checkpoint-restore-semantic fn2-run-writers fn2-run-restarts fn2-checkpoint-summary fn2-checkpoint-summary-sources)))
(assert-event (fn2-csc-test nil))
(assert-event (fn2-csc-test :rank))
(assert-event (fn2-csc-test :stale))
