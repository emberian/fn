; Opt-in declaration-time resolution; actual registry stays numeric.
(in-package "ACL2")
(include-book "../books/machine-arms")
(include-book "std/testing/must-fail" :dir :system)
(defconst *fn2-budget-unit-bytes* 4096)
(defmachine fn2-budget-literal
 :phases (:free) :fields () :budget (:bytes 4096 :steps 32 :descriptors 0)
 :arms ((:free (:idle))) :observes ())
(defmachine fn2-budget-derived
 :phases (:free) :fields ()
 :budget-cost (:bytes (+ *fn2-budget-unit-bytes* 0) :steps (* 2 16) :descriptors 0)
 :arms ((:free (:idle))) :observes ())
(make-event
 (let ((literal (fn2-machine-property 'fn2-budget-literal :budget (w state)))
       (derived (fn2-machine-property 'fn2-budget-derived :budget (w state))))
  (if (and (equal literal derived) (equal derived '(:bytes 4096 :steps 32 :descriptors 0)))
      (value '(value-triple :numeric-budget))
   (er soft 'machine-budget-cost-unit "Literal and resolved registry budgets differ."))))
(must-fail
 (defmachine fn2-budget-unknown :phases (:free) :fields ()
  :budget-cost (:bytes *fn2-budget-does-not-exist* :steps 32 :descriptors 0)
  :arms ((:free (:idle))) :observes ()))
(must-fail
 (defmachine fn2-budget-runtime :phases (:free) :fields ()
  :budget-cost (:bytes (fn2-pool-rows fn2-pool) :steps 32 :descriptors 0)
  :arms ((:free (:idle))) :observes ()))
(must-fail
 (defmachine fn2-budget-conflict :phases (:free) :fields ()
  :budget (:bytes 4096 :steps 32 :descriptors 0)
  :budget-cost (:bytes 4096 :steps 32 :descriptors 0)
  :arms ((:free (:idle))) :observes ()))
