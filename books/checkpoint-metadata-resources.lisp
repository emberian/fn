; Root1 owns private bounded working resources, not a second resident store.
; Drain the C cut before atomic admission, so reservation cannot strand staged
; transactions needing journal windows. Refusal must release the cut, never wait.
(in-package "ACL2")
(include-book "run-installed-geometry")
(include-book "checkpoint-working-reserve")
(include-book "checkpoint-metadata-manifest")
(include-book "checkpoint-compaction-state")
(include-book "checkpoint-predecessors")
(include-book "checkpoint-payload")
(include-book "checkpoint-semantic-retention")
(include-book "machines-c-sealer")
(include-book "checkpoint-future-resources")
(fn2-book-layer :c)

(defconst *fn2-checkpoint-source-build* 1)
(defconst *fn2-checkpoint-manifest-build* 2)

(defconst *fn2-checkpoint-work-field-rows*
 (+ (* 2 *fn2-run-build-fields*) (* 2 *fn2-run-entry-rows*) *fn2-run-reader-fields*))
(assert-event (<= *fn2-checkpoint-work-field-rows* *fn2-b-checkpoint-field-rows*))

(defun fn2-checkpoint-source-wbase () *fn2-seal-writer-rows*)
(defun fn2-checkpoint-manifest-wbase () (+ *fn2-seal-writer-rows* *fn2-run-max-levels*))
(defun fn2-checkpoint-source-cursor (trows rrows)
 (declare (xargs :guard t))
 (+ (nfix trows) (* 9 (nfix rrows)) *fn2-idc-seal-cursors*))
(defun fn2-checkpoint-work-fbase (fcrows)
 (declare (xargs :guard t)) (* 128 (nfix fcrows)))
(defun fn2-checkpoint-manifest-fbase (fcrows)
 (declare (xargs :guard t)) (+ (fn2-checkpoint-work-fbase fcrows) *fn2-run-build-fields*))
(defun fn2-checkpoint-source-ebase (fcrows)
 (declare (xargs :guard t)) (+ (fn2-checkpoint-manifest-fbase fcrows) *fn2-run-build-fields*))
(defun fn2-checkpoint-manifest-ebase (fcrows)
 (declare (xargs :guard t)) (+ (fn2-checkpoint-source-ebase fcrows) *fn2-run-entry-rows*))
(defun fn2-checkpoint-source-rbase (fcrows)
 (declare (xargs :guard t)) (+ (fn2-checkpoint-manifest-ebase fcrows) *fn2-run-entry-rows*))

; Windows 0..5 source levels; 6..11 directory levels; 12/13 hash arrays;
; 14 held decoded entry; 15 directory digest; 16 authenticated semantic page;
; 17 semantic read/payload manifest; 18 payload data; appended physical-source
; page/read windows have dedicated declared indices. Sharing window17 is
; sequential: semantic holds its authenticated page while payload uses17/18.









; All declared working leases share one per-class preflight and one non-yielding acquisition.
; Future workers borrow actual protected leases; a free-count promise alone is
; insufficient because ordinary readers may still allocate while C is held.








(fn2-sealer-child fn2-core-checkpoint-root1 fn2-checkpoint-root1 (fn2-checkpoint-root1-init 1 fn2-checkpoint-root1)
 "The actual root1 source continuation and admitted window ownership survive yields.")
(fn2-sealer-child fn2-core-checkpoint-windows fn2-checkpoint-windows (fn2-checkpoint-windows-init *fn2-checkpoint-window-count* fn2-checkpoint-windows)
 "Fixed working windows are tried atomically at the exact held cut; refusal retains no bundle.")
(fn2-sealer-child fn2-core-checkpoint-metadata fn2-checkpoint-metadata (fn2-checkpoint-metadata-init 1 fn2-checkpoint-metadata)
 "The held source's actual entry and run assembly continuation.")
(fn2-sealer-child fn2-core-checkpoint-source fn2-checkpoint-source (fn2-checkpoint-source-init 1 fn2-checkpoint-source)
 "Ordered selection exhausts the actual held overlays and resident runs.")
(fn2-sealer-child fn2-core-checkpoint-metadata-manifest fn2-checkpoint-metadata-manifest (fn2-checkpoint-metadata-manifest-init (fn2-b-capacity :extent-slots 16 profile) fn2-checkpoint-metadata-manifest)
 "Directory control and one pending typed source root per actual physical extent; capture grants no publication authority.")
(fn2-sealer-child fn2-core-checkpoint-retained-entry fn2-checkpoint-retained-entry (fn2-checkpoint-retained-entry-init 1 fn2-checkpoint-retained-entry)
 "One protected authenticated entry passes between semantic and payload walkers.")
; The canonical payload carrier/physical completion hook is registered by boot-kind.
; Live source admission remains in checkpoint-payload and cannot bind cold-active state.
(fn2-sealer-child fn2-core-checkpoint-semantic fn2-checkpoint-semantic (fn2-checkpoint-semantic-init 1 fn2-checkpoint-semantic)
 "Authenticated semantic tree traversal retains its actual page and entry origin."
 :harvest (fn2-checkpoint-semantic-harvest ((fn2-core-checkpoint-semantic fn2-checkpoint-semantic))))
(fn2-sealer-child fn2-core-checkpoint-semantic-work fn2-checkpoint-semantic-work
 (fn2-checkpoint-semantic-work-init (fn2-b-capacity :extent-slots 16 profile) fn2-checkpoint-semantic-work)
 "One exact semantic traversal row per allocator extent, with no arbitrary data cap.")

(defcost fn2-checkpoint-root1-reserve-op :child fn2-checkpoint-root1-reserve :answers t
 :tables (fn2-core-checkpoint-root1 fn2-core-checkpoint-windows fn2-core-checkpoint-future fn2-core-checkpoint-future-windows fn2-core-csnapshot fn2-core-pool)
 :effects :per-use
 :doc "Try all declared root, staging, journal and anchor leases atomically for the exact HELD cut; refusal requires immediate cut release.")
(defcost fn2-checkpoint-root1-workspaces-op :child fn2-checkpoint-root1-workspaces :answers t
 :tables (fn2-core-checkpoint-root1 fn2-core-checkpoint-windows fn2-core-pool)
 :doc "Derive the stable descriptor/page/scratch/read tuple from actual admitted root1 ownership.")

; Profile geometry, not a stored-history limit: every actual original C row
; receives one inventory slot, including physical rows appended to R.
(defun fn2-checkpoint-predecessor-rows (profile)
 (declare (xargs :guard t))
 (+ (nfix (fn2-b-capacity :identity-overlays *fn2-idc-overlays-default* profile))
    (fn2-run-installed-row-count
     (nfix (fn2-b-capacity :identity-runs 64 profile))
     (nfix (fn2-b-capacity :extent-slots 16 profile)))))
(defun fn2-checkpoint-predecessor-profilep (profile)
 (declare (xargs :guard t))
 (and (natp (fn2-b-capacity :identity-overlays *fn2-idc-overlays-default* profile))
      (natp (fn2-b-capacity :identity-runs 64 profile))
      (natp (fn2-b-capacity :extent-slots 16 profile))
      (unsigned-byte-p 32 (fn2-checkpoint-predecessor-rows profile))))
(defun fn2-checkpoint-predecessors-init-for (profile fn2-checkpoint-predecessors)
 (declare (xargs :stobjs fn2-checkpoint-predecessors
  :guard (fn2-checkpoint-predecessor-profilep profile)))
 (fn2-checkpoint-predecessors-init (fn2-checkpoint-predecessor-rows profile) fn2-checkpoint-predecessors))
(defthm fn2-checkpoint-predecessors-init-for-type
 (implies (and (fn2-checkpoint-predecessorsp fn2-checkpoint-predecessors) (fn2-checkpoint-predecessor-profilep profile))
  (fn2-checkpoint-predecessorsp (fn2-checkpoint-predecessors-init-for profile fn2-checkpoint-predecessors))))
(defthm fn2-checkpoint-predecessors-init-for-wfp
 (implies (fn2-checkpoint-predecessor-profilep profile)
  (fn2-checkpoint-predecessors-wfp (fn2-checkpoint-predecessors-init-for profile fn2-checkpoint-predecessors))))
(defcorechild fn2-core-checkpoint-predecessors fn2-checkpoint-predecessors
 :init (fn2-checkpoint-predecessors-init-for profile fn2-checkpoint-predecessors)
 :profilep (fn2-checkpoint-predecessor-profilep profile)
 :why "Exact original held source inventory has O+R rows; many originals may map to one durable schema output.")
(fn2-sealer-child fn2-core-checkpoint-predecessor-control fn2-checkpoint-predecessor-control
 (fn2-checkpoint-predecessor-control-init 1 fn2-checkpoint-predecessor-control)
 "Current held candidate/token and bounded capture/check/retirement cursor retain original-source obligations.")
(fn2-sealer-child fn2-core-checkpoint-compaction fn2-checkpoint-compaction
 (fn2-checkpoint-compaction-init 1 fn2-checkpoint-compaction)
 "The actual schema merge's authenticated seek/equality/park continuation survives bounded rescans.")
