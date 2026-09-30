; Immutable conditional-unit readout. This is not a bootstrap authority.
(in-package "ACL2")
(include-book "assumptions-selected-runtime-bp-creators")
(include-book "assumptions-selected-runtime-allocation-geometry")
(defconst *fn-runtime-unit-source-coordinate*
 '(:bp-creators "2896cc08a" :declarations
   "2e60f3389fcdcce52d91e90e3b69ef5bb5ee7ac6251336c4d39af82788408501"
   :record12 "facaad842496aedf9de1bcbe1872e7a0b0c91e40190e591f95f0d5db01ff3b33"))
(defconst *fn-runtime-unit-compiler-coordinate*
 '(:saved-core-policy ((inhibit-warnings 3) (speed 3) (space 1)
   (safety 0) (debug 1) (compilation-speed 0))))
(defconst *fn-runtime-unit-missing*
 '(:caller-xep-frames :first-use :fault-construction-and-signaling
   :ordinary-allocator-premise-installation :automatic-collector-space
   :foreign-allocation :borrowed-root-lifetime :cleanup-and-retirement))
; These constants are constructed during book/image loading, not each read.
; Their retained image roots belong in the qualified installation baseline.
(defconst *fn-runtime-unit-record12*
 (list :runtime-unit :record12 :successful-fixed-creator-objects
  *fn-runtime-unit-source-coordinate* *fn-srbc-coordinate*
  *fn-runtime-unit-compiler-coordinate* *fn-srag-coordinate*
  144 2 144
  '(:evidence "planning/evidence/bp-selected-creators-2026-09-30"
    :conditional-assumption :a-selected-runtime-bp-creators)
  *fn-runtime-unit-missing*))
(defconst *fn-runtime-unit-digest16*
 (list :runtime-unit :digest16 :successful-fixed-creator-objects
  *fn-runtime-unit-source-coordinate* *fn-srbc-coordinate*
  *fn-runtime-unit-compiler-coordinate* *fn-srag-coordinate*
  672 2 672
  '(:evidence "planning/evidence/bp-selected-creators-2026-09-30"
    :conditional-assumption :a-selected-runtime-bp-creators)
  *fn-runtime-unit-missing*))
(defconst *fn-runtime-unit-carry6*
 (list :runtime-unit :carry6 :successful-fixed-creator-objects
  *fn-runtime-unit-source-coordinate* *fn-srbc-coordinate*
  *fn-runtime-unit-compiler-coordinate* *fn-srag-coordinate*
  64 1 64
  '(:evidence "planning/evidence/bp-selected-creators-2026-09-30"
    :conditional-assumption :a-selected-runtime-bp-creators)
  *fn-runtime-unit-missing*))
(defconst *fn-runtime-unit-node16*
 (list :runtime-unit :node16 :successful-fixed-creator-objects
  *fn-runtime-unit-source-coordinate* *fn-srbc-coordinate*
  *fn-runtime-unit-compiler-coordinate* *fn-srag-coordinate*
  704 10 608
  '(:evidence "planning/evidence/bp-selected-creators-2026-09-30"
    :conditional-assumption :a-selected-runtime-bp-creators)
  *fn-runtime-unit-missing*))
(defconst *fn-runtime-unit-left16*
 (list :runtime-unit :left16 :successful-fixed-creator-objects
  *fn-runtime-unit-source-coordinate* *fn-srbc-coordinate*
  *fn-runtime-unit-compiler-coordinate* *fn-srag-coordinate*
  704 10 608
  '(:evidence "planning/evidence/bp-selected-creators-2026-09-30"
    :conditional-assumption :a-selected-runtime-bp-creators)
  *fn-runtime-unit-missing*))
(defconst *fn-runtime-unit-right16*
 (list :runtime-unit :right16 :successful-fixed-creator-objects
  *fn-runtime-unit-source-coordinate* *fn-srbc-coordinate*
  *fn-runtime-unit-compiler-coordinate* *fn-srag-coordinate*
  704 10 608
  '(:evidence "planning/evidence/bp-selected-creators-2026-09-30"
    :conditional-assumption :a-selected-runtime-bp-creators)
  *fn-runtime-unit-missing*))
(defun fn-runtime-unit-source (unit source runtime geometry)
 (declare (xargs :guard t))
 (cond
  ((not (fn-srbc-unitp unit)) (mv :runtime-unit-unavailable :unsupported-unit))
  ((not (equal source *fn-runtime-unit-source-coordinate*))
   (mv :runtime-unit-unavailable :source-coordinate-mismatch))
  ((not (equal runtime *fn-srbc-coordinate*))
   (mv :runtime-unit-unavailable :runtime-coordinate-mismatch))
  ((not (equal geometry *fn-srag-coordinate*))
   (mv :runtime-unit-unavailable :geometry-coordinate-mismatch))
  (t (mv :conditional-unit
   (case unit
    (:record12 *fn-runtime-unit-record12*)
    (:digest16 *fn-runtime-unit-digest16*)
    (:carry6 *fn-runtime-unit-carry6*)
    (:node16 *fn-runtime-unit-node16*)
    (:left16 *fn-runtime-unit-left16*)
    (:right16 *fn-runtime-unit-right16*)
    (otherwise nil))))))
; A conditional constructor row cannot satisfy a complete phase selector.
(defun fn-runtime-phase-source (phase)
 (declare (xargs :guard t))
 (mv :runtime-phase-unavailable
  (case phase
   (:owner-control-entry
    '(:missing :owner-control-entry :scheduler-wakeup-and-wait
      :preobserve-io-participant :caller-frames :first-use :fault-suffix))
   (:explicit-collector
    '(:missing :explicit-collector :core-request-and-completion
      :locked-snapshot-ffi :post-gc-participant-ack :caller-frames))
   (:collector-resume
    '(:missing :collector-resume :callback-return-and-native-unwind
      :retained-completion-roots :caller-frames))
   (:rescue '(:missing :rescue :condition-signaling :fail-stop-and-unwind))
   (:automatic-collector-dynamic
    '(:missing :automatic-collector-dynamic :all-generations-copy-space
      :collector-internal-allocation :concurrent-participant-allocation))
   (:collector-physical
    '(:missing :collector-physical :affine-slack :external :stack :tls :ffi))
   (otherwise '(:missing :unsupported-phase)))))
(verify-guards fn-runtime-unit-source)
(verify-guards fn-runtime-phase-source)
(defthm fn-runtime-unit-source-never-installs
 (not (equal (mv-nth 0 (fn-runtime-unit-source unit source runtime geometry))
             :installed))
 :rule-classes nil)
(defthm fn-runtime-phase-source-refuses-complete-phase
 (equal (mv-nth 0 (fn-runtime-phase-source phase)) :runtime-phase-unavailable)
 :rule-classes nil)
(defthm fn-runtime-unit-object-projection-by-definition
 (implies (equal (mv-nth 0 (fn-runtime-unit-source unit source runtime geometry))
                 :conditional-unit)
  (let ((record (mv-nth 1 (fn-runtime-unit-source unit source runtime geometry))))
   (and (equal (nth 7 record) (fn-srbc-allocated-octets unit))
        (equal (nth 8 record) (fn-srbc-request-count unit))
        (equal (nth 9 record) (fn-srbc-retained-owned-octets unit)))))
 :hints (("Goal" :in-theory (enable fn-runtime-unit-source fn-srbc-unitp
  fn-srbc-allocated-octets fn-srbc-request-count fn-srbc-retained-owned-octets)))
 :rule-classes nil)
