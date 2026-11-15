; Explicit release ownership registration output, not a baseline snapshot.
(defcorechild fn2-core-allocation-release fn2-allocation-release
 :init (fn2-allocation-release-init 1 fn2-allocation-release)
 :profilep t
 :why "One actual staged/pending RELEASE_ALLOCATION owns exact checkpoint evidence and target across yields; no FREE admission is granted by staging.")

(defun fn2-b-alloc-edge-floor (profile)
 (declare (xargs :guard t))
 (fn2-alloc-edge-layout-floor (nfix (fn2-b-capacity :extent-slots 16 profile))
  (nfix (fn2-profile-o profile)) (fn2-b-checkpoint-capacity profile)))

(defcorechild fn2-core-alloc-edges fn2-alloc-edges
 :init (fn2-alloc-edges-init (fn2-b-capacity :alloc-edge-slots (fn2-b-alloc-edge-floor profile) profile) fn2-alloc-edges)
 :profilep (and
  (fn2-alloc-edge-layoutp (nfix (fn2-b-capacity :extent-slots 16 profile)) (nfix (fn2-profile-o profile)) (fn2-b-checkpoint-capacity profile))
  (unsigned-byte-p 32 (fn2-b-capacity :alloc-edge-slots (fn2-b-alloc-edge-floor profile) profile))
  (<= (fn2-b-alloc-edge-floor profile)
      (fn2-b-capacity :alloc-edge-slots (fn2-b-alloc-edge-floor profile) profile)))
 :harvest (fn2-b-read-pin-harvest
           ((fn2-core-extents fn2-extents) (fn2-core-alloc-edges fn2-alloc-edges)))
 :why "Disjoint commit, root, operation-pin and checkpoint-reference edges survive yields.")

(defcorechild fn2-core-release-evidence fn2-release-evidence
 :init (fn2-release-evidence-init (fn2-b-capacity :extent-slots 16 profile) fn2-release-evidence)
 :profilep (unsigned-byte-p 32 (fn2-b-capacity :extent-slots 16 profile))
 :why "One exact journal allocation stamp owns its descriptor, installation and self evidence obligations until authenticated substitution.")

(defcorechild fn2-core-release-evidence-candidates fn2-release-evidence-candidates
 :init (fn2-release-evidence-candidates-init (fn2-b-checkpoint-capacity profile) fn2-release-evidence-candidates)
 :profilep (unsigned-byte-p 32 (fn2-b-checkpoint-capacity profile))
 :why "Paired exact candidate aggregate blocks disposal while release journals retain its descriptor evidence.")
