; Arithmetic shared by profile admission and the actual construction planner.
; This is transient checkpoint workspace, never a ceiling on stored data.
(in-package "ACL2")
(include-book "checkpoint-map-format")
(include-book "commit-format")
(fn2-book-layer :b)

(defun fn2-checkpoint-ticket-demand (base-pages map-pages tickets)
 (declare (xargs :guard (and (natp base-pages) (natp map-pages) (natp tickets))))
 (+ 1 (ceiling (+ (nfix base-pages) (nfix map-pages)
                   (fn2-checkpoint-map-page-count (nfix tickets) *fn2-checkpoint-arena-slots*))
                *fn2-checkpoint-allocation-records-per-ticket*)))

(defun fn2-checkpoint-capacity-demand (base-pages extents tickets fuel)
 (declare (xargs :guard (and (natp base-pages) (natp extents) (natp tickets) (natp fuel))
                 :measure (nfix fuel)))
 (let* ((maps (fn2-checkpoint-map-page-count (nfix extents) *fn2-checkpoint-map-slots*))
        (arena (fn2-checkpoint-map-page-count (nfix tickets) *fn2-checkpoint-arena-slots*))
        (next (fn2-checkpoint-ticket-demand (nfix base-pages) maps (nfix tickets))))
  (cond ((or (zp fuel) (< (nfix extents) next) (< next (nfix tickets))) 0)
        ((equal next (nfix tickets)) (+ (nfix base-pages) maps arena next))
        (t (fn2-checkpoint-capacity-demand (nfix base-pages) (nfix extents) next (- fuel 1))))))

; Exact fixed point, with one unit of fuel per possible ticket identity.
; Zero means the demand cannot fit this arena. Profile admission has no stored
; state to walk. Runtime sizing still counts the actual construction ledger.
(defun fn2-checkpoint-capacity-required (base-pages extents)
 (declare (xargs :guard (and (natp base-pages) (natp extents))))
 (fn2-checkpoint-capacity-demand (nfix base-pages) (nfix extents) 1 (nfix extents)))

; Irreducible protocol workspace: root1, root3, root4 and the descriptor
; each require at least one actual page. In the literal empty held-source case
; metadata-source-step skips empty sources and metadata-manifest-{finish,page}
; opens one real directory page. Fresh genesis can have nonempty sources. This
; lower bound establishes profile eligibility only, never maintenance headroom.
(defconst *fn2-checkpoint-minimum-base-pages* (+ 1 1 1 1))

(defun fn2-checkpoint-minimum-capacityp (extents)
 (declare (xargs :guard t))
 (and (natp extents)
      (let ((need (fn2-checkpoint-capacity-required *fn2-checkpoint-minimum-base-pages* extents)))
       (and (posp need) (<= need extents)))))
