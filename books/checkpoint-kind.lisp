; C-aware checkpoint construction is registered above its B-only children.
(in-package "ACL2")
(include-book "checkpoint-kind-b")
(include-book "checkpoint-build")
(fn2-book-layer :c)

(defcorechild fn2-core-checkpoint-build fn2-checkpoint-build
 :init (fn2-checkpoint-build-init 1 fn2-checkpoint-build) :profilep t
 :harvest (fn2-checkpoint-build-harvest
           ((fn2-core-checkpoint-build fn2-checkpoint-build)
            (fn2-core-checkpoint-refs fn2-checkpoint-refs)
            (fn2-core-csnapshot fn2-csnapshot) (fn2-core-checkpoints fn2-checkpoints)))
 :why "One frozen-cut descriptor construction job retains exact reservation and physical completion identity.")
