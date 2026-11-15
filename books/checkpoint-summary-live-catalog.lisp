; Pending live root1 intake uses the same typed directory recorder as cold
; restore. The actual root1 driver calls it only after successful EMIT.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint-summary-entry")
(include-book "checkpoint-build-state")
(include-book "checkpoint-metadata-manifest")
(fn2-book-layer :c)

(defun fn2-checkpoint-summary-live-current-p
 (fn2-checkpoint-summary fn2-checkpoint-build fn2-csnapshot)
 (declare (xargs :stobjs (fn2-checkpoint-summary fn2-checkpoint-build fn2-csnapshot)
  :guard (and (fn2-checkpoint-summary-wfp fn2-checkpoint-summary)
              (fn2-checkpoint-build-wfp fn2-checkpoint-build) (fn2-csnapshot-wfp fn2-csnapshot))))
 (and (< 1 (fn2-checkpoint-summary-rows fn2-checkpoint-summary))
      (< 0 (fn2-checkpoint-build-rows fn2-checkpoint-build))
      (posp (fn2-checkpoint-summary-tag 1 fn2-checkpoint-summary))
      (= (fn2-checkpoint-summary-phase 1 fn2-checkpoint-summary) *fn2-checkpoint-summary-phase-capture*)
      (fn2-checkpoint-build-ownerp
       (fn2-checkpoint-summary-generation 1 fn2-checkpoint-summary)
       (fn2-checkpoint-summary-owner-kind 1 fn2-checkpoint-summary)
       (fn2-checkpoint-summary-owner-slot 1 fn2-checkpoint-summary)
       (fn2-checkpoint-summary-owner-gen 1 fn2-checkpoint-summary)
       fn2-checkpoint-build fn2-csnapshot)
      (= (fn2-checkpoint-summary-candidate 1 fn2-checkpoint-summary) (fn2-checkpoint-build-candidate 0 fn2-checkpoint-build))
      (= (fn2-checkpoint-summary-checkpoint 1 fn2-checkpoint-summary) (fn2-checkpoint-build-checkpoint 0 fn2-checkpoint-build))
      (= (fn2-checkpoint-summary-cut-commit 1 fn2-checkpoint-summary) (fn2-checkpoint-build-cut-commit 0 fn2-checkpoint-build))
      (= (fn2-checkpoint-summary-cut-event 1 fn2-checkpoint-summary) (fn2-checkpoint-build-cut-event 0 fn2-checkpoint-build))
      (= (fn2-checkpoint-summary-history 1 fn2-checkpoint-summary) (fn2-checkpoint-build-history 0 fn2-checkpoint-build))
      (= (fn2-checkpoint-summary-incarnation 1 fn2-checkpoint-summary) (fn2-checkpoint-build-history-incarnation 0 fn2-checkpoint-build))))

; A previous pending catalog must be explicitly retired and made IDLE by its
; actual release path. No failed or partial capture is silently overwritten.
(defun fn2-checkpoint-summary-live-begin
 (token kind owner generation fn2-checkpoint-summary fn2-checkpoint-build fn2-csnapshot)
 (declare (xargs :stobjs (fn2-checkpoint-summary fn2-checkpoint-build fn2-csnapshot)
  :guard (and (fn2-checkpoint-summary-wfp fn2-checkpoint-summary)
              (fn2-checkpoint-build-wfp fn2-checkpoint-build) (fn2-csnapshot-wfp fn2-csnapshot))))
 (b* (((unless (and (< 1 (fn2-checkpoint-summary-rows fn2-checkpoint-summary))
                    (fn2-checkpoint-build-ownerp token kind owner generation fn2-checkpoint-build fn2-csnapshot)
                    (= (fn2-checkpoint-build-phase 0 fn2-checkpoint-build) *fn2-checkpoint-build-phase-await-roots*)
                    (= (fn2-checkpoint-summary-phase 1 fn2-checkpoint-summary) *fn2-checkpoint-summary-phase-idle*)
                    (= (fn2-checkpoint-summary-installed 1 fn2-checkpoint-summary) 0)
                    (= (fn2-checkpoint-summary-lease-count 1 fn2-checkpoint-summary) 0)))
       (mv :source fn2-checkpoint-summary))
      (tag (fn2-checkpoint-summary-fresh-tag fn2-checkpoint-summary))
      ((unless (unsigned-byte-p 60 tag)) (mv :tag-exhausted fn2-checkpoint-summary))
      (fn2-checkpoint-summary (update-fn2-checkpoint-summary-next-tag tag fn2-checkpoint-summary))
      (fn2-checkpoint-summary
       (fn2-checkpoint-summary-put 1 (phase *fn2-checkpoint-summary-phase-capture*)
        (tag tag) (candidate (fn2-checkpoint-build-candidate 0 fn2-checkpoint-build))
        (checkpoint (fn2-checkpoint-build-checkpoint 0 fn2-checkpoint-build))
        (cut-commit (fn2-checkpoint-build-cut-commit 0 fn2-checkpoint-build))
        (cut-event (fn2-checkpoint-build-cut-event 0 fn2-checkpoint-build))
        (history (fn2-checkpoint-build-history 0 fn2-checkpoint-build))
        (incarnation (fn2-checkpoint-build-history-incarnation 0 fn2-checkpoint-build))
        (generation token) (semantic-tag 0) (owner-kind kind) (owner-slot owner) (owner-gen generation)
        (priority-base 0) (application-stage 0) (count 0) (cursor 0) (installed 0) (lease-count 0))))
  (mv :ok fn2-checkpoint-summary)))

; Called in the successful manifest EMIT branch before the source selector
; advances again. EMIT already checked the actual completed physical page.
; It leaves entry-base disjoint from writer decode scratch, and its hash
; workspace remains owned until this immediate bounded copy completes.
(defun fn2-checkpoint-summary-live-record
 (fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-build fn2-csnapshot
  fn2-checkpoint-source fn2-checkpoint-metadata-manifest fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-build fn2-csnapshot
                        fn2-checkpoint-source fn2-checkpoint-metadata-manifest fn2-fields fn2-pool)
  :guard (and (fn2-checkpoint-summary-wfp fn2-checkpoint-summary)
              (fn2-checkpoint-summary-sources-wfp fn2-checkpoint-summary-sources)
              (fn2-checkpoint-build-wfp fn2-checkpoint-build) (fn2-csnapshot-wfp fn2-csnapshot)
              (fn2-checkpoint-source-wfp fn2-checkpoint-source)
              (fn2-checkpoint-metadata-manifest-wfp fn2-checkpoint-metadata-manifest)
              (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (if (not (and (fn2-checkpoint-summary-live-current-p fn2-checkpoint-summary fn2-checkpoint-build fn2-csnapshot)
               (fn2-checkpoint-source-ownerp fn2-checkpoint-source fn2-csnapshot)
               (< 0 (fn2-checkpoint-metadata-manifest-rows fn2-checkpoint-metadata-manifest))
               (= (fn2-checkpoint-source-phase 0 fn2-checkpoint-source) *fn2-checkpoint-source-phase-scan*)
               (= (fn2-checkpoint-source-token 0 fn2-checkpoint-source) (fn2-checkpoint-summary-generation 1 fn2-checkpoint-summary))
               (= (fn2-checkpoint-source-rank 0 fn2-checkpoint-source)
                  (fn2-checkpoint-metadata-manifest-entries 0 fn2-checkpoint-metadata-manifest))))
     (mv :source fn2-checkpoint-summary fn2-checkpoint-summary-sources)
  (fn2-checkpoint-summary-record-fields 1
   (fn2-checkpoint-metadata-manifest-entry-base 0 fn2-checkpoint-metadata-manifest)
   (fn2-checkpoint-summary-owner-kind 1 fn2-checkpoint-summary)
   (fn2-checkpoint-summary-owner-slot 1 fn2-checkpoint-summary)
   (fn2-checkpoint-summary-owner-gen 1 fn2-checkpoint-summary)
   fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-fields fn2-pool)))
