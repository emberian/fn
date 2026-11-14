; C source callback declarations for the retained event roots. The composing
; checkpoint owner still owns actor dispatch, abort exclusion and installation.
(in-package "ACL2")
(include-book "checkpoint-kind")
(include-book "event-build")
(fn2-book-layer :c)
(defcorechild fn2-core-event-build fn2-event-build
 :init (fn2-event-build-init 1 fn2-event-build) :profilep t
 :why "One actual retained-event source cursor owns candidate, source claims and completion-gated directory/frontier pages.")
(defcost fn2-event-build-start :child fn2-event-build-begin :answers (:ok :source :bounds)
 :tables (fn2-core-event-build)
 :doc "Start only from an actual builder claim and authenticated held event cut.")
(defcost fn2-event-build-source :child fn2-event-build-source-step :answers t :bytes 4096
 :tables (fn2-core-event-build fn2-core-checkpoint-construction fn2-core-extents fn2-core-alloc-edges
          fn2-core-fields fn2-core-pool fn2-core-control)
 :doc "Advance one bounded real event source/claim/reservation/page step, or return actionable pressure.")
(defcost fn2-event-build-bind :child fn2-event-build-bind-page :answers t
 :tables (fn2-core-event-build fn2-core-checkpoint-page)
 :doc "Bind one prepared source page; source packing closes until exact physical ownership return.")
(defcost fn2-event-build-consume :child fn2-event-build-consume-page :answers t :bytes 32
 :tables (fn2-core-event-build fn2-core-checkpoint-refs fn2-core-checkpoint-bytes)
 :doc "Consume exact verified completion and returned workspace before advancing or capturing a root.")
