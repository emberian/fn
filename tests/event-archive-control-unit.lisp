; Active/pending metadata isolation only, not a persistence/coverage witness.
(in-package "ACL2")
(include-book "../books/event-archive-control")
(defun fn2-eacu-isolation ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-event-archive
  (mv-let (answer fn2-event-archive)
   (with-local-stobj fn2-digests
    (mv-let (answer fn2-event-archive fn2-digests)
     (b* ((fn2-event-archive (fn2-event-archive-init 2 fn2-event-archive))
          (fn2-digests (fn2-digests-init 1 fn2-digests))
          (fn2-digests (fn2-digest-set-word 0 0 123 fn2-digests))
          (fn2-event-archive (fn2-event-archive-copy-digest 1 :cut-seal 0 0 fn2-digests fn2-event-archive)))
      (mv (and (= (fn2-event-archive-word 1 :cut-seal 0 fn2-event-archive) 123)
               (= (fn2-event-archive-word 0 :cut-seal 0 fn2-event-archive) 0)
               (= (fn2-event-archive-word 1 :member 0 fn2-event-archive) 0)
               (= (fn2-event-archive-word 1 :manifest 0 fn2-event-archive) 0)) fn2-event-archive fn2-digests))
     (mv answer fn2-event-archive))) answer)))
(assert-event (fn2-eacu-isolation))

; The same role helper separates sourcebuild1's root3 manifest from root1's
; still-complete build2. Removing the archive marker refuses internal20.
(defun fn2-eacu-roles ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-checkpoint-metadata
  (mv-let (answer fn2-checkpoint-metadata)
   (with-local-stobj fn2-run-builds
    (mv-let (answer fn2-checkpoint-metadata fn2-run-builds)
     (b* ((fn2-checkpoint-metadata (fn2-checkpoint-metadata-init 1 fn2-checkpoint-metadata))
          (fn2-run-builds (fn2-run-builds-init 3 fn2-run-builds))
          (fn2-checkpoint-metadata (fn2-checkpoint-metadata-put 0 (source-kind 2) (build 1)))
          (fn2-run-builds (fn2-run-builds-set-schema 1 10 fn2-run-builds))
          (fn2-run-builds (fn2-run-builds-set-schema 2 10 fn2-run-builds))
          (archive (= (fn2-checkpoint-metadata-role 1 fn2-checkpoint-metadata fn2-run-builds) 3))
          (root1 (= (fn2-checkpoint-metadata-role 2 fn2-checkpoint-metadata fn2-run-builds) 1))
          (fn2-run-builds (fn2-run-builds-set-schema 1 *fn2-event-archive-schema* fn2-run-builds))
          (fn2-checkpoint-metadata (fn2-checkpoint-metadata-set-source-kind 0 0 fn2-checkpoint-metadata)))
      (mv (and archive root1 (not (fn2-checkpoint-metadata-role 1 fn2-checkpoint-metadata fn2-run-builds))) fn2-checkpoint-metadata fn2-run-builds))
     (mv answer fn2-checkpoint-metadata))) answer)))
(assert-event (fn2-eacu-roles))

; Shared field binding only; source admission/bytes remain separate contracts.
(defun fn2-eacu-manifest-fields ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-fields
  (mv-let (answer fn2-fields)
   (b* ((fn2-fields (fn2-fields-init *fn2-manifest-entry-num-fields* fn2-fields))
        ((mv code fn2-fields) (fn2-manifest-bind-unfiltered 0 20 7 1 4 16 2 9 0 1 fn2-fields)))
    (mv (and (eq code :ok)
             (= (fn2-fields-value *fn2-manifest-entry-field-height* fn2-fields) 1)
             (= (fn2-fields-value *fn2-manifest-entry-field-entries* fn2-fields) 4)
             (= (fn2-fields-value *fn2-manifest-entry-field-root-unit* fn2-fields) 16)
             (= (fn2-fields-ref-len *fn2-manifest-entry-field-root-hash* fn2-fields) 32)
             (= (fn2-fields-value *fn2-manifest-entry-field-filter-unit* fn2-fields) 0)
             (= (fn2-fields-ref-off *fn2-manifest-entry-field-filter-hash* fn2-fields) 32)) fn2-fields)) answer)))
(assert-event (fn2-eacu-manifest-fields))
