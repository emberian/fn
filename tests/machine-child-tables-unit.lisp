(in-package "ACL2")
(include-book "../books/machine-arms")
(include-book "std/testing/must-fail" :dir :system)
(defmachine fn2-arms-probe
 :phases (:free :work) :fields ((count :u32))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :arms ((:free (:idle)) (:work (:idle))) :observes ())
;; A child operation can read a registered machine without a :link to it.
;; Its table is a machine registry entry, not a defcorechild entry.
(defun fn2-arms-t-machine-peek (fn2-arms-probe)
  (declare (xargs :stobjs fn2-arms-probe :guard t))
  (declare (ignore fn2-arms-probe))
  :ok)
(defcost fn2-arms-t-machine-peek-core :answers (:ok)
 :child fn2-arms-t-machine-peek :doc "Test: read a sibling machine table without a link.")
(defmachine fn2-arms-machine-reader
 :phases (:free :work)
 :fields ((count :u32))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :arms ((:free (:idle))
        (:work (:do (code) (fn2-arms-t-machine-peek-core) :accept (:ok)) (:idle)))
 :observes ())
(assert-event
 (mv-let (err extras) (fn2-arms-extra-children 'fn2-arms-machine-reader (w state))
   (and (not err) (equal extras '((fn2-arms-probe-table . fn2-arms-probe))))))
(defmachine-arms fn2-arms-machine-reader :children)
(assert-event (member-eq 'fn2-arms-probe
                        (getpropc 'fn2-arms-machine-reader-run-work-children 'stobjs-in nil (w state))))
;; The unregistered fn2-arms-tz control above must still be refused.

;; An operation over a stobj no defcorechild registers is refused.
(defcolumns fn2-arms-tz ((value :u32)))
(defun fn2-arms-t-touch (fn2-arms-tz)
  (declare (xargs :stobjs fn2-arms-tz :guard (fn2-arms-tz-wfp fn2-arms-tz))) (mv :ok fn2-arms-tz))
(defcost fn2-arms-t-touch-core :answers t :child fn2-arms-t-touch :doc "Test: an unregistered child.")
(defmachine fn2-arms-probe5
 :phases (:free :work)
 :fields ((count :u32))
 :budget (:bytes 4096 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :arms ((:free (:idle)) (:work (:do (code) (fn2-arms-t-touch-core) :case ((:otherwise (:idle))))))
 :observes ())
(must-fail (defmachine-arms fn2-arms-probe5 :children))
