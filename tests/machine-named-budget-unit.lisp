; Prepared generator controls, unexecuted in the source-only loader lane.
(in-package "ACL2")
(include-book "../books/machine-arms")
(include-book "std/testing/must-fail" :dir :system)
(defconst *fn2-budget-test-bytes* 8192)
(defmachine fn2-budget-literal
 :phases (:free :work) :fields ((budget-count :u32))
 :budget (:bytes 8192 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :arms ((:free (:idle)) (:work (:idle))) :observes ())
(defmachine fn2-budget-named
 :phases (:free :work) :fields ((budget-count :u32))
 :budget (:bytes *fn2-budget-test-bytes* :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :arms ((:free (:idle)) (:work (:idle))) :observes ())
(defmachine fn2-budget-derived
 :phases (:free :work) :fields ((budget-count :u32))
 :budget (:bytes (+ 4096 (* 2 *fn2-budget-test-bytes*)) :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :arms ((:free (:idle)) (:work (:idle))) :observes ())
(make-event
 (if (and (equal (fn2-machine-property 'fn2-budget-literal :budget (w state)) '(:bytes 8192 :steps 32 :descriptors 0))
          (equal (fn2-machine-property 'fn2-budget-named :budget (w state)) '(:bytes 8192 :steps 32 :descriptors 0))
          (equal (fn2-machine-property 'fn2-budget-derived :budget (w state)) '(:bytes 20480 :steps 32 :descriptors 0))
          (equal (fn2-machine-property 'fn2-budget-literal :columns (w state))
                 (fn2-machine-property 'fn2-budget-named :columns (w state)))
          (equal (fn2-machine-property 'fn2-budget-literal :capacity (w state))
                 (fn2-machine-property 'fn2-budget-named :capacity (w state))))
  (value '(value-triple :same-generator-and-layout))
  (er soft 'machine-named-budget-unit "Named budget changed the actual machine declaration.")))
(must-fail
 (defmachine fn2-budget-unknown
  :phases (:free) :fields ((budget-count :u32))
  :budget (:bytes *fn2-budget-not-declared* :steps 32 :descriptors 0)
  :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
  :arms ((:free (:idle))) :observes ()))
(defconst *fn2-budget-not-natural* -1)
(must-fail
 (defmachine fn2-budget-negative
  :phases (:free) :fields ((budget-count :u32))
  :budget (:bytes *fn2-budget-not-natural* :steps 32 :descriptors 0)
  :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
  :arms ((:free (:idle))) :observes ()))
