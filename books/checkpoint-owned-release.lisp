; Ownership provenance is extent-lifetime state. Candidate disposal does not
; clear it. Only an exact physical release may clear the matching live bit.
(in-package "ACL2")
(include-book "checkpoint-construction")
(fn2-book-layer :b)
(defun fn2-checkpoint-owned-release-ledger-code (e epoch allocation fn2-checkpoint-construction)
 (declare (xargs :stobjs fn2-checkpoint-construction
  :guard (fn2-checkpoint-construction-wfp fn2-checkpoint-construction)))
 (cond ((not (and (natp e) (< e (fn2-checkpoint-construction-rows fn2-checkpoint-construction)))) :ownership)
       ((equal (fn2-checkpoint-construction-live e fn2-checkpoint-construction) 0) :ok)
       ((and (or (fn2-checkpoint-construction-native-p e fn2-checkpoint-construction)
                  (equal (fn2-checkpoint-construction-role e fn2-checkpoint-construction) *fn2-checkpoint-owned-restored-role*))
              (equal (fn2-checkpoint-construction-epoch e fn2-checkpoint-construction) epoch)
              (equal (fn2-checkpoint-construction-counter e fn2-checkpoint-construction) allocation)) :ok)
       (t :ownership)))
; Internal post-transition mutation: the same no-yield caller preflights the
; exact handle before allocator mutation. No cost face exposes this primitive.
(defun fn2-checkpoint-owned-release-clear (e fn2-checkpoint-construction)
 (declare (xargs :stobjs fn2-checkpoint-construction
  :guard (and (fn2-checkpoint-construction-wfp fn2-checkpoint-construction)
              (natp e) (< e (fn2-checkpoint-construction-rows fn2-checkpoint-construction)))))
 (fn2-checkpoint-construction-set-live e 0 fn2-checkpoint-construction))
(defun fn2-checkpoint-owned-release-code (e epoch allocation fn2-checkpoint-construction fn2-extents)
 (declare (xargs :stobjs (fn2-checkpoint-construction fn2-extents)
  :guard (and (fn2-checkpoint-construction-wfp fn2-checkpoint-construction) (fn2-extents-wfp fn2-extents))))
 (let ((code (fn2-alloc-release-code e epoch allocation fn2-extents)))
  (if (eq code :ok)
   (fn2-checkpoint-owned-release-ledger-code e epoch allocation fn2-checkpoint-construction)
   code)))
(defun fn2-checkpoint-owned-release (e epoch allocation fn2-checkpoint-construction fn2-extents)
 (declare (xargs :stobjs (fn2-checkpoint-construction fn2-extents)
  :guard (and (fn2-checkpoint-construction-wfp fn2-checkpoint-construction) (fn2-extents-wfp fn2-extents))))
 (let ((code (fn2-checkpoint-owned-release-code e epoch allocation fn2-checkpoint-construction fn2-extents)))
  (if (not (eq code :ok)) (mv code fn2-checkpoint-construction fn2-extents)
   (mv-let (code fn2-extents) (fn2-alloc-release e epoch allocation fn2-extents)
    (if (eq code :ok)
     ; No fallible check after FREE. Preflight established this exact slot and
     ; handle before allocator identity was cleared; no yield intervenes.
     (let ((fn2-checkpoint-construction (fn2-checkpoint-owned-release-clear e fn2-checkpoint-construction)))
      (mv :ok fn2-checkpoint-construction fn2-extents))
     (mv code fn2-checkpoint-construction fn2-extents))))))
; No cost face: this does not activate RELEASE_ALLOCATION admission. Actual
; persisted FREE consumers must call this shared path rather than alloc-release.
