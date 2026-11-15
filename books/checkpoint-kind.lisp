; C-aware checkpoint construction is registered above its B-only children.
(in-package "ACL2")
(include-book "checkpoint-kind-b")
(include-book "checkpoint-teardown-state")
(include-book "checkpoint-page-kind")
(include-book "checkpoint-build")
(include-book "checkpoint-plan")
(include-book "checkpoint-map-build")
(include-book "checkpoint-metadata-driver")
(include-book "checkpoint-metadata-release")
(include-book "checkpoint-live-adoption")
(fn2-book-layer :c)

(defcorechild fn2-core-checkpoint-build fn2-checkpoint-build
 :init (fn2-checkpoint-build-init 1 fn2-checkpoint-build)
 :profilep (or (zp (fn2-b-checkpoint-capacity profile))
               (fn2-checkpoint-minimum-capacityp (fn2-b-capacity :extent-slots 16 profile)))
 :why "One frozen-cut descriptor construction job retains exact reservation and physical completion identity.")

(defcorechild fn2-core-checkpoint-plan fn2-checkpoint-plan
 :init (fn2-checkpoint-plan-init 1 fn2-checkpoint-plan) :profilep t
 :why "One held construction set counted and closed before the physical map copy.")
(defcorechild fn2-core-checkpoint-plan-marks fn2-checkpoint-plan-marks
 :init (fn2-checkpoint-plan-marks-init (fn2-b-capacity :extent-slots 16 profile) fn2-checkpoint-plan-marks)
 :profilep (unsigned-byte-p 32 (fn2-b-capacity :extent-slots 16 profile))
 :why "Per-ordinal duplicate detection for exactly planned map, arena and journal ticket reservations.")

(defcorechild fn2-core-checkpoint-map-build fn2-checkpoint-map-build
 :init (fn2-checkpoint-map-build-init 1 fn2-checkpoint-map-build) :profilep t
 :why "One frozen map/arena page chain owns bounded source traversal and completion-gated root construction.")

(defcorechild fn2-core-checkpoint-teardown-debt fn2-checkpoint-teardown-debt
 :init (fn2-checkpoint-teardown-debt-init (fn2-b-checkpoint-capacity profile) fn2-checkpoint-teardown-debt)
 :profilep (unsigned-byte-p 32 (fn2-b-checkpoint-capacity profile))
 :why "One immutable displaced-evidence and exact retirement continuation per configured candidate; no overwrite, timer or FREE authority.")
