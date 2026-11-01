; Death is a fresh process. fn2-sim-crash re-initializes the core in place, so
; after a death every core child's rows must equal a newly created core's init
; values (pool data, which no read observes before it is written, and the
; environment children excepted, as in the reference model's comparison).
; Lists and local stobjs are test adapters, never served operations.
(in-package "ACL2")
(include-book "commit-history")
(fn2-book-layer :b)

; The first child that differs from a newly created core, or nil.
(defun fn2-b-death-difference (profile fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (with-local-stobj fn2-ref-core
  (mv-let (difference fn2-ref-core)
   (let ((fn2-ref-core (fn2-core-init profile fn2-ref-core)))
    (mv (fn2-ref-core-difference fn2-core fn2-ref-core) fn2-ref-core))
   difference)))

; A planted survivor: one live allocator edge row left from before the death.
(defun fn2-b-plant-survivor (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-alloc-edges (fn2-core-alloc-edges fn2-core))) (fn2-alloc-edges)
  (fn2-alloc-edges-set-state 0 *fn2-alloc-edge-state-live* fn2-alloc-edges) fn2-core))

; (fresh-after-init reported): a core dirtied and then re-initialized in place
; equals a new core, and the same comparison reports a planted survivor.
(defun fn2-b-death-control (profile)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core)
   (b* ((fn2-core (fn2-core-init profile fn2-core))
        (fn2-core (fn2-b-plant-survivor fn2-core))
        (fn2-core (fn2-core-init profile fn2-core))
        (clean (fn2-b-death-difference profile fn2-core))
        (fn2-core (fn2-b-plant-survivor fn2-core)))
    (mv (list (null clean) (fn2-b-death-difference profile fn2-core)) fn2-core))
   answer)))
