(fn2-rd-shape fn2-read-observer-release
 (x fn2-reads fn2-c-source-control fn2-c-source-readers)
 ((fn2-reads 1) (fn2-c-source-control 2) (fn2-c-source-readers 3))
 (fn2-reads fn2-c-source-control fn2-c-source-readers)
 (fn2-c-source-reader-release fn2-reads-observer-serial))
(fn2-rd-shape fn2-read-observer-enter
 (x fresh fn2-reads fn2-c-source-control fn2-c-source-readers)
 ((fn2-reads 1) (fn2-c-source-control 2) (fn2-c-source-readers 3))
 (fn2-reads fn2-c-source-control fn2-c-source-readers)
 (fn2-read-observer-release fn2-c-source-reader-acquire fn2-c-source-reader-acquire-under fn2-reads-observer-serial fn2-reads-observer-parent fn2-reads-observer-parent-serial))

(fn2-rd-shape fn2-read-parent-bind-pair
 (x0 x1 parent receipt fn2-reads fn2-c-source-readers)
 ((fn2-reads 1)) (fn2-reads fn2-c-source-readers)
 (fn2-read-parent-pair-p fn2-reads-observer-parent fn2-reads-observer-parent-serial))
(fn2-rd-shape fn2-read-parent-clear-pair
 (x0 x1 parent receipt fn2-reads fn2-c-source-readers)
 ((fn2-reads 1)) (fn2-reads fn2-c-source-readers)
 (fn2-read-parent-pair-p fn2-reads-observer-parent fn2-reads-observer-parent-serial))
(fn2-rd-shape fn2-read-parent-bind-one (x parent receipt fn2-reads fn2-c-source-readers)
 ((fn2-reads 1)) (fn2-reads fn2-c-source-readers)
 (fn2-read-parent-row-p fn2-read-parent-bindable-p fn2-read-parent-bound-p))
(fn2-rd-shape fn2-read-parent-clear-one (x parent receipt fn2-reads fn2-c-source-readers)
 ((fn2-reads 1)) (fn2-reads fn2-c-source-readers)
 (fn2-read-parent-row-p fn2-read-parent-bindable-p fn2-read-parent-bound-p))
