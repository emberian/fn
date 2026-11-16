; A schema owns one builder across every original-source rescan. Dense output
; rank changes once per schema, never once per original or intermediate page.
(in-package "ACL2")
(include-book "checkpoint-compaction-output")
(include-book "checkpoint-predecessors")
(fn2-book-layer :c)

(defmacro fn2-checkpoint-compaction-schema-guard ()
 '(and (fn2-checkpoint-compaction-output-guard)
       (fn2-checkpoint-predecessors-wfp fn2-checkpoint-predecessors)
       (fn2-checkpoint-predecessor-control-wfp fn2-checkpoint-predecessor-control)))

(defun fn2-checkpoint-compaction-schema-begin
 (fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
 fn2-overlays fn2-run-installed fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fc fn2-fields fn2-pool
 fn2-checkpoint-predecessors fn2-checkpoint-predecessor-control)
 (declare (xargs :stobjs (fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
 fn2-overlays fn2-run-installed fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fc fn2-fields fn2-pool
 fn2-checkpoint-predecessors fn2-checkpoint-predecessor-control)
 :guard (fn2-checkpoint-compaction-schema-guard)))
 (b* (((unless (and (fn2-checkpoint-predecessor-ready-p fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
                     fn2-overlays fn2-run-installed fn2-checkpoint-predecessors fn2-checkpoint-predecessor-control)
                    (fn2-checkpoint-compaction-windowsp fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-pool)
                    (equal (fn2-checkpoint-root1-phase 0 fn2-checkpoint-root1) *fn2-checkpoint-root1-phase-select*)
                    (equal (fn2-checkpoint-compaction-phase 0 fn2-checkpoint-compaction) *fn2-checkpoint-compaction-phase-sources*)
                    (equal (fn2-checkpoint-compaction-schema-found 0 fn2-checkpoint-compaction) 1)
                    (equal (fn2-checkpoint-compaction-schema-open 0 fn2-checkpoint-compaction) 0)
                    (equal (fn2-checkpoint-compaction-configured 0 fn2-checkpoint-compaction) 1)
                    (equal (fn2-checkpoint-compaction-scan-kind 0 fn2-checkpoint-compaction) 0)
                    (equal (fn2-checkpoint-compaction-scan-row 0 fn2-checkpoint-compaction) 0)
                    (< 0 (fn2-checkpoint-metadata-rows fn2-checkpoint-metadata))))
       (fn2-checkpoint-compaction-output-mv :source))
      (rank (+ 1 (fn2-checkpoint-compaction-output-rank 0 fn2-checkpoint-compaction)))
      ((unless (unsigned-byte-p 60 rank)) (fn2-checkpoint-compaction-output-mv :exhausted))
      (token (fn2-checkpoint-compaction-token 0 fn2-checkpoint-compaction))
      (kind (fn2-checkpoint-compaction-owner-kind 0 fn2-checkpoint-compaction))
      (owner (fn2-checkpoint-compaction-owner-slot 0 fn2-checkpoint-compaction))
      (gen (fn2-checkpoint-compaction-owner-gen 0 fn2-checkpoint-compaction))
      (fcrows (fn2-fc-rows fn2-fc))
      (crow (fn2-b-semantic-retention-row fcrows))
      (lb (fn2-checkpoint-compaction-lower-base 0 fn2-checkpoint-compaction))
      (eb (fn2-checkpoint-compaction-entry-base 0 fn2-checkpoint-compaction))
      (sid (fn2-checkpoint-compaction-schema 0 fn2-checkpoint-compaction))
      ((unless (and (<= 9 fcrows) (equal eb (fn2-checkpoint-source-ebase fcrows))
                    (equal lb (fn2-checkpoint-manifest-ebase fcrows))
                    (<= (+ lb *fn2-run-entry-rows*) (fn2-fields-rows fn2-fields))))
       (fn2-checkpoint-compaction-output-mv :fields))
      ((mv code fn2-pool) (fn2-pool-reset (fn2-checkpoint-compaction-lower-slot 0 fn2-checkpoint-compaction)
                                             (fn2-checkpoint-compaction-lower-gen 0 fn2-checkpoint-compaction) kind owner gen fn2-pool))
      ((unless (eq code :ok)) (fn2-checkpoint-compaction-output-mv code))
      ((mv code fn2-fields) (fn2-range-key-least 0 (fn2-run-layout-keys sid) sid lb
       (fn2-checkpoint-compaction-lower-slot 0 fn2-checkpoint-compaction) (fn2-checkpoint-compaction-lower-gen 0 fn2-checkpoint-compaction) fn2-fields))
      ((unless (eq code :ok)) (fn2-checkpoint-compaction-output-mv code))
      ((mv code fn2-run-builds fn2-run-writers fn2-pool)
       (fn2-run-build-start *fn2-checkpoint-source-build* sid rank (fn2-checkpoint-source-wbase) crow
        (+ (* *fn2-digest-stride* crow) *fn2-seal-hash-region*)
        (fn2-checkpoint-windows-slot 12 fn2-checkpoint-windows) (fn2-checkpoint-windows-generation 12 fn2-checkpoint-windows)
        (fn2-checkpoint-work-fbase fcrows) *fn2-run-page-size*
        (fn2-checkpoint-build-history 0 fn2-checkpoint-build) (fn2-checkpoint-build-history-incarnation 0 fn2-checkpoint-build)
        kind owner gen fn2-run-builds fn2-run-writers fn2-pool))
      ((unless (eq code :ok)) (fn2-checkpoint-compaction-output-mv code))
      (ordinal (if (equal token (fn2-checkpoint-metadata-token 0 fn2-checkpoint-metadata))
                   (fn2-checkpoint-metadata-ordinal 0 fn2-checkpoint-metadata) 0))
      (fn2-checkpoint-metadata (fn2-checkpoint-metadata-put 0
       (phase *fn2-checkpoint-metadata-phase-feeding*) (token token) (owner-kind kind) (owner-slot owner) (owner-gen gen)
       (run-rank rank) (build *fn2-checkpoint-source-build*) (cursor (fn2-checkpoint-compaction-cursor 0 fn2-checkpoint-compaction))
       (position 0) (entry-base eb) (ordinal ordinal)
       (scratch (fn2-checkpoint-compaction-best-slot 0 fn2-checkpoint-compaction))
       (scratch-gen (fn2-checkpoint-compaction-best-gen 0 fn2-checkpoint-compaction))
       (held 0) (copy-field 0) (copy-offset 0) (copy-end 0) (retention-stage 0)
       (history (fn2-checkpoint-build-history 0 fn2-checkpoint-build))
       (history-incarnation (fn2-checkpoint-build-history-incarnation 0 fn2-checkpoint-build))))
      (fn2-checkpoint-compaction (fn2-checkpoint-compaction-put 0
       (schema-open 1) (output-rank rank) (has-lower 0) (best 0) (lower-round 0) (source-started 0)
       (copy-field 0) (copy-offset 0) (copy-end 0))))
  (fn2-checkpoint-compaction-output-mv :more)))

(defun fn2-checkpoint-compaction-schema-finish
 (fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
 fn2-overlays fn2-run-installed fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fc fn2-fields fn2-pool
 fn2-checkpoint-predecessors fn2-checkpoint-predecessor-control)
 (declare (xargs :stobjs (fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
 fn2-overlays fn2-run-installed fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fc fn2-fields fn2-pool
 fn2-checkpoint-predecessors fn2-checkpoint-predecessor-control)
 :guard (fn2-checkpoint-compaction-schema-guard)))
 (b* (((unless (and (fn2-checkpoint-predecessor-ready-p fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
                     fn2-overlays fn2-run-installed fn2-checkpoint-predecessors fn2-checkpoint-predecessor-control)
                    (fn2-checkpoint-compaction-output-bound-p fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
                     fn2-overlays fn2-run-installed fn2-checkpoint-metadata fn2-run-builds fn2-run-writers fn2-run-restarts fn2-fc fn2-fields fn2-pool)
                    (equal (fn2-checkpoint-compaction-phase 0 fn2-checkpoint-compaction) *fn2-checkpoint-compaction-phase-schema-done*)
                    (equal (fn2-checkpoint-compaction-scan-kind 0 fn2-checkpoint-compaction) 1)
                    (equal (fn2-checkpoint-compaction-scan-row 0 fn2-checkpoint-compaction) (fn2-run-installed-rows fn2-run-installed))
                    (equal (fn2-checkpoint-compaction-best 0 fn2-checkpoint-compaction) 0)
                    (equal (fn2-checkpoint-metadata-held 0 fn2-checkpoint-metadata) 0)))
       (fn2-checkpoint-compaction-output-mv :source))
      ; Zero-entry LIVE roots are original retirement obligations, not fake
      ; replacement roots. They never enter this nonempty-schema constructor.
      ((unless (posp (fn2-checkpoint-metadata-position 0 fn2-checkpoint-metadata)))
       (fn2-checkpoint-compaction-output-mv :source-count))
      ((mv code fn2-run-builds) (fn2-run-build-finish *fn2-checkpoint-source-build* fn2-run-builds))
      (fn2-checkpoint-metadata (if (eq code :ok)
       (fn2-checkpoint-metadata-set-phase 0 *fn2-checkpoint-metadata-phase-source-drained* fn2-checkpoint-metadata) fn2-checkpoint-metadata)))
  (fn2-checkpoint-compaction-output-mv code)))
