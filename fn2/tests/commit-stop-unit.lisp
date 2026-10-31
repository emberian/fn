; Named stops (REVIEW-20261030 ruling 3): every state the commit kind's helpers
; and the allocator's list operations rule out stops the core with its own
; reason. One control per reason plants that state on an admitted core; the
; unplanted control shows the same call leaves the core running.
(in-package "ACL2")
(include-book "../sim/commit-history")
(defun fn2-csu-plant (kind fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (case kind
  ((:resource :edge)
   (stobj-let ((fn2-commit-io (fn2-core-commit-io fn2-core))) (fn2-commit-io)
    (fn2-commit-io-init 3 fn2-commit-io) fn2-core))
  (:root
   (stobj-let ((fn2-commit-root (fn2-core-commit-root fn2-core))) (fn2-commit-root)
    (fn2-commit-root-init 0 fn2-commit-root) fn2-core))
  (:links
   (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (fn2-extents)
    (update-fn2-alloc-free-head 17 fn2-extents) fn2-core))
  (otherwise fn2-core)))
; Row 0 is admitted (one keyed member); row 1 stays free. The resource and
; edge plants cut the I/O table to row 0's three entries, so row 1's
; resources read the not-u32 extent.
(defun fn2-csu-execute (kind fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((profile (fn2-b-test-profile *fn2-profile-tiny* 0))
      (fn2-core (fn2-core-init profile fn2-core))
      ((mv & fn2-core)
       (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code fn2-extents)
        (fn2-alloc-begin-epoch 1 fn2-extents) (mv code fn2-core)))
      (a (fn2-machine-global-id *fn2-commit-kind* 0 profile))
      (b (fn2-machine-global-id *fn2-commit-kind* 1 profile))
      ((mv admitted & & & fn2-core)
       (if (eq kind :root) (mv :ok 0 0 0 fn2-core) (fn2-commit-admit-keyed 1 0 0 0 0 fn2-core)))
      (fn2-core (fn2-csu-plant kind fn2-core))
      ((mv code fn2-core)
       (case kind
        (:pool (let ((fn2-core (fn2-commit-save-pool a 3 0 0 fn2-core))) (mv :none fn2-core)))
        (:format (let ((fn2-core (fn2-commit-context a 3 fn2-core))) (mv :none fn2-core)))
        (:io (fn2-commit-io-edge a 0 t (expt 2 32) 0 fn2-core))
        (:resource (fn2-commit-reserve-extent b fn2-core))
        (:edge (fn2-commit-root-edge b nil fn2-core))
        (:root (b* (((mv code & & & fn2-core) (fn2-commit-admit-keyed 1 0 0 0 0 fn2-core))) (mv code fn2-core)))
        (otherwise (fn2-commit-reserve-extent b fn2-core)))))
  (mv (list admitted code (fn2-stop-reason-code->keyword (fn2-core-stop-reason fn2-core))) fn2-core)))
(defun fn2-csu-case (kind)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (result fn2-core) (fn2-csu-execute kind fn2-core) result)))
(make-event
 `(defconst *fn2-csu-results*
   ',(list (fn2-csu-case :pool) (fn2-csu-case :format) (fn2-csu-case :io) (fn2-csu-case :resource)
           (fn2-csu-case :edge) (fn2-csu-case :root) (fn2-csu-case :links) (fn2-csu-case :none))))
(assert-event (equal *fn2-csu-results*
 '((:ok :none :commit-pool) (:ok :none :commit-format) (:ok :shape :commit-io)
   (:ok :shape :commit-resource) (:ok :shape :commit-edge) (:ok :admission :commit-root)
   (:ok :links :alloc-links) (:ok :ok :none))))
