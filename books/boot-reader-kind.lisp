; Sole CORE registration for selected physical map/reach/page reader state.
; Semantic/work state belongs to boot-semantic-kind; catalog to catalog-kind.
(in-package "ACL2")
(include-book "machines-b")
(include-book "checkpoint-restore-map")
(include-book "checkpoint-restore-reach-core")
(fn2-book-layer :b)
(defcorechild fn2-core-checkpoint-restore-reader fn2-checkpoint-restore-reader
 :init (fn2-checkpoint-restore-reader-init 1 fn2-checkpoint-restore-reader) :profilep t
 :why "One exact physical descriptor/map/semantic page reader retains its cursor across bounded turns.")
(defcorechild fn2-core-checkpoint-restore-map fn2-checkpoint-restore-map
 :init (fn2-checkpoint-restore-map-init (fn2-b-capacity :extent-slots 16 profile) fn2-checkpoint-restore-map)
 :profilep (unsigned-byte-p 32 (fn2-b-capacity :extent-slots 16 profile))
 :why "One authenticated selected-map tuple per admitted physical extent.")
(defcorechild fn2-core-checkpoint-restore-map-control fn2-checkpoint-restore-map-control
 :init (fn2-checkpoint-restore-map-control-init 1 fn2-checkpoint-restore-map-control) :profilep t
 :why "One selected map source/control continuation, independent of the page lease.")
(defcorechild fn2-core-checkpoint-restore-reach fn2-checkpoint-restore-reach
 :init (fn2-checkpoint-restore-reach-init (fn2-b-capacity :extent-slots 16 profile) fn2-checkpoint-restore-reach)
 :profilep (unsigned-byte-p 32 (fn2-b-capacity :extent-slots 16 profile))
 :why "One exact typed reachability claim per physical extent, never a stored-data count cap.")
(defcorechild fn2-core-checkpoint-restore-reach-control fn2-checkpoint-restore-reach-control
 :init (fn2-checkpoint-restore-reach-control-init 1 fn2-checkpoint-restore-reach-control) :profilep t
 :why "One exact selected candidate/cut and reachability generation.")
