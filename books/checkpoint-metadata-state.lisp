; Rebuild held C sources through the served run engine. Resident cache units
; never enter persistent headers: every page gets its B reservation first.
(in-package "ACL2")
(include-book "checkpoint-construction-owner")
(include-book "run-entry-rehome")
(include-book "checkpoint-metadata-source")
(fn2-book-layer :c)

(defcolumns fn2-checkpoint-metadata
 ((phase (:enum fn2-checkpoint-metadata-phase (:idle :feeding :source-drained :uncertain)))
  (token :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (source-kind :u8) (source-order :u60) (run-rank :u60) (cursor :u32) (build :u32) (source-row :u32) (position :u60) (entry-base :u32)
  (ordinal :u60) (extent :u32) (writer :u32)
  (scratch :u32) (scratch-gen :u60) (held :bool) (copy-field :u32) (copy-offset :u32) (copy-end :u32) (retention-stage :u8)
  ; Physical identity captured from the owner-bound configured origin.
  (history :u60) (history-incarnation :u60)))

(defun fn2-checkpoint-metadata-ownerp (fn2-checkpoint-metadata fn2-csnapshot fn2-run-builds fn2-run-writers)
 (declare (xargs :stobjs (fn2-checkpoint-metadata fn2-csnapshot fn2-run-builds fn2-run-writers)
  :guard (and (fn2-checkpoint-metadata-wfp fn2-checkpoint-metadata) (fn2-csnapshot-wfp fn2-csnapshot)
              (fn2-run-builds-wfp fn2-run-builds) (fn2-run-writers-wfp fn2-run-writers))))
 (and (< 0 (fn2-checkpoint-metadata-rows fn2-checkpoint-metadata))
      (fn2-csnapshot-ownerp (fn2-checkpoint-metadata-token 0 fn2-checkpoint-metadata)
       (fn2-checkpoint-metadata-owner-kind 0 fn2-checkpoint-metadata)
       (fn2-checkpoint-metadata-owner-slot 0 fn2-checkpoint-metadata)
       (fn2-checkpoint-metadata-owner-gen 0 fn2-checkpoint-metadata) fn2-csnapshot)
      (equal (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)
      (let ((b (fn2-checkpoint-metadata-build 0 fn2-checkpoint-metadata)))
       (and (fn2-run-buildp b fn2-run-builds fn2-run-writers)
            (equal (fn2-run-builds-history b fn2-run-builds) (fn2-checkpoint-metadata-history 0 fn2-checkpoint-metadata))
            (equal (fn2-run-builds-incarnation b fn2-run-builds) (fn2-checkpoint-metadata-history-incarnation 0 fn2-checkpoint-metadata))
            (equal (fn2-run-builds-okind b fn2-run-builds) (fn2-checkpoint-metadata-owner-kind 0 fn2-checkpoint-metadata))
            (equal (fn2-run-builds-oslot b fn2-run-builds) (fn2-checkpoint-metadata-owner-slot 0 fn2-checkpoint-metadata))
            (equal (fn2-run-builds-ogen b fn2-run-builds) (fn2-checkpoint-metadata-owner-gen 0 fn2-checkpoint-metadata))))))


; Source builders are reused sequentially after root1 completion. Internal
; archive bytes belong to root3's typed closure, never to semantic root1.
(defun fn2-checkpoint-metadata-role (b fn2-checkpoint-metadata fn2-run-builds)
 (declare (xargs :stobjs (fn2-checkpoint-metadata fn2-run-builds)
  :guard (and (fn2-checkpoint-metadata-wfp fn2-checkpoint-metadata) (fn2-run-builds-wfp fn2-run-builds))))
 (and (natp b) (< b (fn2-run-builds-rows fn2-run-builds))
      (< 0 (fn2-checkpoint-metadata-rows fn2-checkpoint-metadata))
      (if (and (equal (fn2-checkpoint-metadata-source-kind 0 fn2-checkpoint-metadata) 2)
               (equal b (fn2-checkpoint-metadata-build 0 fn2-checkpoint-metadata)))
          (and (member (fn2-run-builds-schema b fn2-run-builds) (list *fn2-event-archive-schema* 10)) 3)
        (and (not (fn2-run-layout-internal-p (fn2-run-builds-schema b fn2-run-builds))) 1))))
