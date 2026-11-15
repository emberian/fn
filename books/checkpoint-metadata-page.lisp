; Canonical C page -> checked B page -> parent reference. The worker freezes
; the writer workspace from BIND until CONSUME; all promotion uses this seam.
(in-package "ACL2")
(include-book "checkpoint-metadata")
(include-book "checkpoint-page-io")
(fn2-book-layer :c)

(defun fn2-checkpoint-metadata-writerp (b level fn2-checkpoint-metadata fn2-csnapshot fn2-run-builds fn2-run-writers)
 (declare (xargs :stobjs (fn2-checkpoint-metadata fn2-csnapshot fn2-run-builds fn2-run-writers)
  :guard (and (fn2-checkpoint-metadata-wfp fn2-checkpoint-metadata) (fn2-csnapshot-wfp fn2-csnapshot)
              (fn2-run-builds-wfp fn2-run-builds) (fn2-run-writers-wfp fn2-run-writers))))
 (and (fn2-checkpoint-metadata-ownerp fn2-checkpoint-metadata fn2-csnapshot fn2-run-builds fn2-run-writers)
      (fn2-run-buildp b fn2-run-builds fn2-run-writers)
      (natp level) (< level *fn2-run-max-levels*) (< level (fn2-run-builds-height b fn2-run-builds))
      (equal (fn2-run-builds-okind b fn2-run-builds) (fn2-checkpoint-metadata-owner-kind 0 fn2-checkpoint-metadata))
      (equal (fn2-run-builds-oslot b fn2-run-builds) (fn2-checkpoint-metadata-owner-slot 0 fn2-checkpoint-metadata))
      (equal (fn2-run-builds-ogen b fn2-run-builds) (fn2-checkpoint-metadata-owner-gen 0 fn2-checkpoint-metadata))
      (let ((w (fn2-run-level-writer b level)))
       (and (equal (fn2-run-writers-phase w fn2-run-writers) *fn2-run-writer-phase-sealed*)
            (equal (fn2-run-writers-history w fn2-run-writers) (fn2-checkpoint-metadata-history 0 fn2-checkpoint-metadata))
            (equal (fn2-run-writers-incarnation w fn2-run-writers) (fn2-checkpoint-metadata-history-incarnation 0 fn2-checkpoint-metadata))
            (equal (mod (fn2-run-writers-unit w fn2-run-writers) *fn2-storage-extent-units*) 0)))))

; All Ref inputs derive from the actual sealed writer and retained reservation,
; never a caller-provided page identity or checked flag.
(defun fn2-checkpoint-metadata-page-bind (b level fn2-checkpoint-metadata fn2-csnapshot fn2-run-builds fn2-run-writers
                                         fn2-checkpoint-page fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents
                                         fn2-pool fn2-fc fn2-fields)
 (declare (xargs :stobjs (fn2-checkpoint-metadata fn2-csnapshot fn2-run-builds fn2-run-writers fn2-checkpoint-page
                          fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents fn2-pool fn2-fc fn2-fields)
  :guard (and (fn2-checkpoint-metadata-wfp fn2-checkpoint-metadata) (fn2-csnapshot-wfp fn2-csnapshot)
              (fn2-run-builds-wfp fn2-run-builds) (fn2-run-writers-wfp fn2-run-writers)
              (fn2-checkpoint-page-wfp fn2-checkpoint-page) (fn2-checkpoint-page-verified-wfp fn2-checkpoint-page-verified)
              (fn2-checkpoint-construction-wfp fn2-checkpoint-construction) (fn2-extents-wfp fn2-extents)
              (fn2-pool-wfp fn2-pool) (fn2-fc-wfp fn2-fc) (fn2-fields-wfp fn2-fields))))
 (b* (((unless (fn2-checkpoint-metadata-writerp b level fn2-checkpoint-metadata fn2-csnapshot fn2-run-builds fn2-run-writers))
       (mv :source fn2-checkpoint-page))
      (w (fn2-run-level-writer b level))
      (extent (floor (fn2-run-writers-unit w fn2-run-writers) *fn2-storage-extent-units*))
      ((unless (< extent (fn2-checkpoint-construction-rows fn2-checkpoint-construction))) (mv :bounds fn2-checkpoint-page)))
  (fn2-checkpoint-page-begin (fn2-checkpoint-metadata-token 0 fn2-checkpoint-metadata)
   (fn2-checkpoint-metadata-owner-kind 0 fn2-checkpoint-metadata) (fn2-checkpoint-metadata-owner-slot 0 fn2-checkpoint-metadata)
   (fn2-checkpoint-metadata-owner-gen 0 fn2-checkpoint-metadata)
        (fn2-checkpoint-metadata-role b fn2-checkpoint-metadata fn2-run-builds)
   (fn2-checkpoint-construction-ordinal extent fn2-checkpoint-construction) extent
   (fn2-run-writers-epoch w fn2-run-writers) (fn2-run-writers-counter w fn2-run-writers)
   (fn2-run-writers-slot w fn2-run-writers) (fn2-run-writers-gen w fn2-run-writers)
   (fn2-run-writers-page-kind w fn2-run-writers) (fn2-run-writers-history w fn2-run-writers)
   (fn2-run-writers-incarnation w fn2-run-writers) *fn2-run-page-size*
   fn2-checkpoint-page fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-csnapshot fn2-extents fn2-pool fn2-fc fn2-fields)))

; Fixed eight-word copy of the hash of bytes actually verified and written.
; It replaces the pre-write C sealing scratch before parent Ref construction.
(defun fn2-checkpoint-metadata-page-hash (i extent hrow fn2-checkpoint-page-verified fn2-digests)
 (declare (xargs :stobjs (fn2-checkpoint-page-verified fn2-digests) :measure (nfix (- 8 (nfix i)))
  :guard (and (fn2-checkpoint-page-verified-wfp fn2-checkpoint-page-verified) (fn2-digest-rowp hrow fn2-digests)
              (natp extent) (< extent (fn2-checkpoint-page-verified-rows fn2-checkpoint-page-verified)) (natp i) (<= i 8))))
 (if (>= i 8) fn2-digests
  (let ((fn2-digests (fn2-digest-set-word hrow i (fn2-checkpoint-page-verified-word extent i fn2-checkpoint-page-verified) fn2-digests)))
   (fn2-checkpoint-metadata-page-hash (+ 1 i) extent hrow fn2-checkpoint-page-verified fn2-digests))))

(defun fn2-checkpoint-metadata-page-complete-p (b level fn2-checkpoint-metadata fn2-csnapshot fn2-run-builds fn2-run-writers
                                               fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents fn2-checkpoint-page fn2-pool)
 (declare (xargs :stobjs (fn2-checkpoint-metadata fn2-csnapshot fn2-run-builds fn2-run-writers
                          fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents fn2-checkpoint-page fn2-pool)
  :guard (and (fn2-checkpoint-metadata-wfp fn2-checkpoint-metadata) (fn2-csnapshot-wfp fn2-csnapshot)
              (fn2-run-builds-wfp fn2-run-builds) (fn2-run-writers-wfp fn2-run-writers)
              (fn2-checkpoint-page-verified-wfp fn2-checkpoint-page-verified)
              (fn2-checkpoint-construction-wfp fn2-checkpoint-construction) (fn2-extents-wfp fn2-extents)
              (fn2-checkpoint-page-wfp fn2-checkpoint-page) (fn2-pool-wfp fn2-pool))))
 (and (fn2-checkpoint-metadata-writerp b level fn2-checkpoint-metadata fn2-csnapshot fn2-run-builds fn2-run-writers)
      (let* ((w (fn2-run-level-writer b level))
             (e (floor (fn2-run-writers-unit w fn2-run-writers) *fn2-storage-extent-units*)))
       (and (eq (fn2-pool-workspace-code (fn2-run-writers-slot w fn2-run-writers) (fn2-run-writers-gen w fn2-run-writers)
                  (fn2-checkpoint-metadata-owner-kind 0 fn2-checkpoint-metadata) (fn2-checkpoint-metadata-owner-slot 0 fn2-checkpoint-metadata)
                  (fn2-checkpoint-metadata-owner-gen 0 fn2-checkpoint-metadata) fn2-pool) :ok)
            (or (not (< 0 (fn2-checkpoint-page-rows fn2-checkpoint-page)))
                (not (equal e (fn2-checkpoint-page-extent 0 fn2-checkpoint-page)))
                (equal (fn2-checkpoint-page-transferred 0 fn2-checkpoint-page) 0))
            (< e (fn2-checkpoint-construction-rows fn2-checkpoint-construction))
            (< e (fn2-checkpoint-page-verified-rows fn2-checkpoint-page-verified))
            (fn2-checkpoint-page-completed-extent-p (fn2-checkpoint-metadata-token 0 fn2-checkpoint-metadata)
             (fn2-checkpoint-metadata-owner-kind 0 fn2-checkpoint-metadata) (fn2-checkpoint-metadata-owner-slot 0 fn2-checkpoint-metadata)
             (fn2-checkpoint-metadata-owner-gen 0 fn2-checkpoint-metadata)
        (fn2-checkpoint-metadata-role b fn2-checkpoint-metadata fn2-run-builds)
             (fn2-checkpoint-construction-ordinal e fn2-checkpoint-construction) e
             fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents)
            (equal (fn2-checkpoint-page-verified-epoch e fn2-checkpoint-page-verified) (fn2-run-writers-epoch w fn2-run-writers))
            (equal (fn2-checkpoint-page-verified-allocation e fn2-checkpoint-page-verified) (fn2-run-writers-counter w fn2-run-writers))
            (equal (fn2-checkpoint-page-verified-page-kind e fn2-checkpoint-page-verified) (fn2-run-writers-page-kind w fn2-run-writers))
            (equal (fn2-checkpoint-page-verified-history e fn2-checkpoint-page-verified) (fn2-run-writers-history w fn2-run-writers))
            (equal (fn2-checkpoint-page-verified-incarnation e fn2-checkpoint-page-verified) (fn2-run-writers-incarnation w fn2-run-writers))
            (equal (fn2-checkpoint-page-verified-encoded-length e fn2-checkpoint-page-verified) *fn2-run-page-size*)))))

(defun fn2-checkpoint-metadata-page-consume (b level fn2-checkpoint-metadata fn2-csnapshot fn2-run-builds fn2-run-writers
                                           fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents fn2-checkpoint-page fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-checkpoint-metadata fn2-csnapshot fn2-run-builds fn2-run-writers
                          fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents fn2-checkpoint-page fn2-pool fn2-digests)
  :guard (and (fn2-checkpoint-metadata-wfp fn2-checkpoint-metadata) (fn2-csnapshot-wfp fn2-csnapshot)
              (fn2-run-builds-wfp fn2-run-builds) (fn2-run-writers-wfp fn2-run-writers)
              (fn2-checkpoint-page-verified-wfp fn2-checkpoint-page-verified)
              (fn2-checkpoint-construction-wfp fn2-checkpoint-construction) (fn2-extents-wfp fn2-extents)
              (fn2-checkpoint-page-wfp fn2-checkpoint-page) (fn2-pool-wfp fn2-pool)
              (fn2-digests-wfp fn2-digests))))
 (b* (((unless (fn2-checkpoint-metadata-page-complete-p b level fn2-checkpoint-metadata fn2-csnapshot fn2-run-builds fn2-run-writers
                fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents fn2-checkpoint-page fn2-pool)) (mv :page-pending fn2-digests))
      (w (fn2-run-level-writer b level))
      (extent (floor (fn2-run-writers-unit w fn2-run-writers) *fn2-storage-extent-units*))
      (hrow (+ (fn2-run-builds-hbase b fn2-run-builds) level))
      ((unless (fn2-digest-rowp hrow fn2-digests)) (mv :bounds fn2-digests))
      (fn2-digests (fn2-checkpoint-metadata-page-hash 0 extent hrow fn2-checkpoint-page-verified fn2-digests)))
  (mv :ok fn2-digests)))

; Parent entries are built only after the child's physical write completed;
; the hash comes from the verified bytes, including B's actual geometry.
(defun fn2-checkpoint-metadata-promote (b level fn2-checkpoint-metadata fn2-csnapshot fn2-checkpoint-page fn2-checkpoint-page-verified
                                       fn2-checkpoint-construction fn2-extents fn2-run-builds fn2-run-writers
                                       fn2-run-restarts fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-checkpoint-metadata fn2-csnapshot fn2-checkpoint-page fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents
                          fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-digests)
  :guard (and (fn2-checkpoint-metadata-wfp fn2-checkpoint-metadata) (fn2-csnapshot-wfp fn2-csnapshot)
              (fn2-checkpoint-page-verified-wfp fn2-checkpoint-page-verified) (fn2-checkpoint-construction-wfp fn2-checkpoint-construction)
              (fn2-extents-wfp fn2-extents) (fn2-checkpoint-page-wfp fn2-checkpoint-page) (fn2-run-builds-wfp fn2-run-builds) (fn2-run-writers-wfp fn2-run-writers)
              (fn2-run-restarts-wfp fn2-run-restarts) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests))))
 (b* (((mv code fn2-digests) (fn2-checkpoint-metadata-page-consume b level fn2-checkpoint-metadata fn2-csnapshot fn2-run-builds fn2-run-writers
       fn2-checkpoint-page-verified fn2-checkpoint-construction fn2-extents fn2-checkpoint-page fn2-pool fn2-digests))
      ((unless (eq code :ok))
       (mv code fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-digests)))
  (fn2-run-build-promote b level fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-digests)))
