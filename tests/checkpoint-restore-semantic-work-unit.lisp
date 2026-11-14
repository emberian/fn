; Actual typed run writer→nth→cold queue/find controls. Descriptor/map/page
; authentication premises are synthetic; these do NOT witness persisted boot
; hashes. Every allocation row comes through the real encoded map/FIFO intake.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint-restore-semantic-unit")
(include-book "../books/checkpoint-restore-semantic-work")
(defun fn2-crsw-close (fuel fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-run-writers fn2-run-restarts fn2-fields fn2-pool) :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) (mv :fuel fn2-run-writers fn2-fields fn2-pool)
  (mv-let (code fn2-run-writers fn2-fields fn2-pool)
   (fn2-run-close-step 0 4096 fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
   (if (eq code :more) (fn2-crsw-close (- fuel 1) fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
    (mv code fn2-run-writers fn2-fields fn2-pool)))))
(defun fn2-crsw-find (fuel fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control
 fn2-checkpoint-restore-semantic fn2-checkpoint-restore-semantic-work fn2-fc fn2-pool)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control
 fn2-checkpoint-restore-semantic fn2-checkpoint-restore-semantic-work fn2-fc fn2-pool) :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) (mv :fuel fn2-checkpoint-restore-semantic fn2-fc fn2-pool)
  (mv-let (code fn2-checkpoint-restore-semantic fn2-fc fn2-pool)
   (fn2-checkpoint-restore-semantic-find fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control
    fn2-checkpoint-restore-semantic fn2-checkpoint-restore-semantic-work fn2-fc fn2-pool)
   (if (eq code :more) (fn2-crsw-find (- fuel 1) fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control
    fn2-checkpoint-restore-semantic fn2-checkpoint-restore-semantic-work fn2-fc fn2-pool)
    (mv code fn2-checkpoint-restore-semantic fn2-fc fn2-pool)))))
(defun fn2-crsw-body (mode fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader
 fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-fields fn2-pool fn2-checkpoint-restore-semantic
 fn2-checkpoint-restore-semantic-work fn2-run-writers fn2-run-restarts fn2-digests fn2-fc)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader
 fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-fields fn2-pool fn2-checkpoint-restore-semantic
 fn2-checkpoint-restore-semantic-work fn2-run-writers fn2-run-restarts fn2-digests fn2-fc) :verify-guards nil))
 (b* (((mv intake fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader
        fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-fields fn2-pool fn2-checkpoint-restore-semantic)
       (fn2-crsu-body :children fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader
        fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control fn2-fields fn2-pool fn2-checkpoint-restore-semantic))
      (fn2-fields (fn2-fields-init 512 fn2-fields))
      (fn2-checkpoint-restore-semantic-work (fn2-checkpoint-restore-semantic-work-init 6 fn2-checkpoint-restore-semantic-work))
      (fn2-run-writers (fn2-run-writers-init 1 fn2-run-writers))
      (fn2-run-restarts (fn2-run-restarts-init *fn2-run-restart-capacity* fn2-run-restarts))
      (fn2-digests (fn2-digests-init 256 fn2-digests)) (fn2-fc (fn2-fc-init 1 fn2-fc))
      (slot (fn2-checkpoint-restore-semantic-slot 0 fn2-checkpoint-restore-semantic))
      (gen (fn2-checkpoint-restore-semantic-gen 0 fn2-checkpoint-restore-semantic))
      ((mv opened fn2-run-writers fn2-pool)
       (fn2-run-open 0 slot gen 10 1 0 7 0 *page-kind-manifest* *fn2-storage-extent-units* 4 31 0 0 7 0 1 0 *fn2-format-page-size* fn2-run-writers fn2-pool))
      ((mv zeroed fn2-pool) (fn2-run-zero 32 slot gen 20000 7 0 1 fn2-pool))
      (eb 200)
      (fn2-fields (fn2-fields-set-value (+ eb *fn2-manifest-entry-field-schema*) 3 fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ eb *fn2-manifest-entry-field-run*) 9 fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ eb *fn2-manifest-entry-field-height*) 1 fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ eb *fn2-manifest-entry-field-entries*) 0 fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ eb *fn2-manifest-entry-field-root-unit*) (* (if (eq mode :foreign) 2 5) *fn2-storage-extent-units*) fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ eb *fn2-manifest-entry-field-root-epoch*) (if (eq mode :epoch) 5 4) fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ eb *fn2-manifest-entry-field-root-allocation*) (if (eq mode :foreign) 32 35) fn2-fields))
      (fn2-fields (fn2-fields-put (+ eb *fn2-manifest-entry-field-root-hash*) (value 1) (ref-slot slot) (ref-gen gen) (ref-off 20000) (ref-len 32)))
      (fn2-fields (fn2-fields-put (+ eb *fn2-manifest-entry-field-filter-hash*) (value 1) (ref-slot slot) (ref-gen gen) (ref-off 20000) (ref-len 32)))
      ((mv added fn2-run-writers fn2-run-restarts fn2-fields fn2-pool) (fn2-run-add 0 10 eb fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
      ((mv closed fn2-run-writers) (fn2-run-close 0 fn2-run-writers))
      ((mv padded fn2-run-writers fn2-fields fn2-pool) (fn2-crsw-close 64 fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
      ((mv headed fn2-run-writers fn2-fields fn2-pool) (fn2-run-head 0 fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
      ; Synthetic authentication premise: actual bytes were produced above;
      ; this source control does not execute the B page hash checker.
      (fn2-checkpoint-restore-semantic (fn2-checkpoint-restore-semantic-put 0
       (phase *fn2-checkpoint-restore-semantic-phase-entries*) (field-base 256) (checker-row 0)
       (schema 10) (run 7) (level 0) (entries 1) (cursor 0) (seen (if (eq mode :overflow) (- (expt 2 60) 1) 0))
       (expected-known (if (eq mode :count) 1 0)) (expected-count 2)))
      ((mv consumed fn2-checkpoint-restore-semantic fn2-checkpoint-restore-semantic-work fn2-fields fn2-digests)
       (fn2-checkpoint-restore-semantic-consume 256 fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control
        fn2-checkpoint-restore-semantic fn2-checkpoint-restore-semantic-work fn2-fields fn2-pool fn2-digests))
      (prefix (and intake (eq opened :ok) (eq zeroed :ok) (eq added :ok) (eq closed :ok) (eq padded :ok) (eq headed :ok)))
      ((when (member-eq mode '(:foreign :epoch :overflow)))
       (mv (and prefix (eq consumed (if (eq mode :overflow) :bounds :reference))
                (equal (fn2-checkpoint-restore-semantic-pending-count 0 fn2-checkpoint-restore-semantic) 0)
                (equal (fn2-checkpoint-restore-semantic-pending-head 0 fn2-checkpoint-restore-semantic) *fn2-alloc-none*) (equal (fn2-checkpoint-restore-semantic-cursor 0 fn2-checkpoint-restore-semantic) 0)
                (equal (fn2-checkpoint-restore-semantic-work-tag 5 fn2-checkpoint-restore-semantic-work) 0))
        fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control
        fn2-fields fn2-pool fn2-checkpoint-restore-semantic fn2-checkpoint-restore-semantic-work fn2-run-writers fn2-run-restarts fn2-digests fn2-fc))
      (fn2-checkpoint-restore-semantic (if (eq mode :repeat) (fn2-checkpoint-restore-semantic-set-cursor 0 0 fn2-checkpoint-restore-semantic) fn2-checkpoint-restore-semantic))
      ((mv ended fn2-checkpoint-restore-semantic fn2-checkpoint-restore-semantic-work fn2-fields fn2-digests)
       (fn2-checkpoint-restore-semantic-consume 256 fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control
        fn2-checkpoint-restore-semantic fn2-checkpoint-restore-semantic-work fn2-fields fn2-pool fn2-digests))
      (fn2-checkpoint-bytes (if (eq mode :replacement) (fn2-checkpoint-bytes-set-value 0 1 fn2-checkpoint-bytes) fn2-checkpoint-bytes))
      (fn2-checkpoint-restore-map-control (if (eq mode :replacement) (update-fn2-checkpoint-restore-map-control-descriptori 0 1 fn2-checkpoint-restore-map-control) fn2-checkpoint-restore-map-control))
      (fn2-checkpoint-restore-semantic-work (if (eq mode :unit)
       (fn2-checkpoint-restore-semantic-work-set-unit 5 0 fn2-checkpoint-restore-semantic-work) fn2-checkpoint-restore-semantic-work))
      (fn2-checkpoint-restore-semantic-work (cond
       ((eq mode :queue-tag) (fn2-checkpoint-restore-semantic-work-set-tag 5 0 fn2-checkpoint-restore-semantic-work))
       ((eq mode :queue-next) (fn2-checkpoint-restore-semantic-work-set-next 5 5 fn2-checkpoint-restore-semantic-work))
       (t fn2-checkpoint-restore-semantic-work)))
      ((mv found fn2-checkpoint-restore-semantic fn2-fc fn2-pool)
       (fn2-crsw-find 8 fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control
        fn2-checkpoint-restore-semantic fn2-checkpoint-restore-semantic-work fn2-fc fn2-pool)))
  (mv (and prefix (eq consumed :more)
       (cond ((eq mode :repeat) (eq ended :repeated-reference))
             ((eq mode :count) (eq ended :count))
             ((member-eq mode '(:queue-tag :queue-next)) (and (eq ended :find) (eq found :queue)))
             ((eq mode :unit) (and (eq ended :find) (eq found :identity)))
             ((eq mode :replacement) (and (eq ended :find) (eq found :source)
               (equal (fn2-checkpoint-restore-semantic-unit 0 fn2-checkpoint-restore-semantic) *fn2-storage-extent-units*)))
             (t (and (eq ended :find) (eq found :read)
                (equal (fn2-checkpoint-restore-semantic-pending-count 0 fn2-checkpoint-restore-semantic) 0)
                (equal (fn2-checkpoint-restore-semantic-pending-head 0 fn2-checkpoint-restore-semantic) *fn2-alloc-none*)
                (equal (fn2-checkpoint-restore-semantic-pending-tail 0 fn2-checkpoint-restore-semantic) *fn2-alloc-none*)
                (equal (fn2-checkpoint-restore-semantic-unit 0 fn2-checkpoint-restore-semantic) (* 5 *fn2-storage-extent-units*))
                (equal (fn2-checkpoint-restore-semantic-schema 0 fn2-checkpoint-restore-semantic) 3)
                (equal (fn2-checkpoint-restore-semantic-run 0 fn2-checkpoint-restore-semantic) 9)
                (equal (fn2-checkpoint-restore-semantic-work-state 5 fn2-checkpoint-restore-semantic-work) *fn2-checkpoint-restore-semantic-work-state-pending*)
                (equal (fn2-checkpoint-restore-semantic-work-unit 5 fn2-checkpoint-restore-semantic-work) (* 5 *fn2-storage-extent-units*))))))
   fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control
   fn2-fields fn2-pool fn2-checkpoint-restore-semantic fn2-checkpoint-restore-semantic-work fn2-run-writers fn2-run-restarts fn2-digests fn2-fc)))
(defun fn2-crsw-test (mode)
 (declare (xargs :verify-guards nil))
 (fn2-run-with-local (fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control
 fn2-fields fn2-pool fn2-checkpoint-restore-semantic fn2-checkpoint-restore-semantic-work fn2-run-writers fn2-run-restarts fn2-digests fn2-fc)
  (fn2-crsw-body mode fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-restore-reader fn2-checkpoint-restore-map fn2-checkpoint-restore-map-control
   fn2-fields fn2-pool fn2-checkpoint-restore-semantic fn2-checkpoint-restore-semantic-work fn2-run-writers fn2-run-restarts fn2-digests fn2-fc)))
(assert-event (fn2-crsw-test nil))
(assert-event (fn2-crsw-test :repeat))
(assert-event (fn2-crsw-test :foreign))
(assert-event (fn2-crsw-test :epoch))
(assert-event (fn2-crsw-test :count))
(assert-event (fn2-crsw-test :replacement))

(assert-event (fn2-crsw-test :overflow))
(assert-event (fn2-crsw-test :unit))

(assert-event (fn2-crsw-test :queue-tag))
(assert-event (fn2-crsw-test :queue-next))
