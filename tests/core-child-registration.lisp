(in-package "ACL2")
(include-book "../books/core-children")
(include-book "../books/profile")
(include-book "../books/machine-arms")
(defconst *fn2-test-child-profile*
  (put-assoc-equal :test-child-rows 4 *fn2-profile-tiny*))
(defcolumns fn2-test-child ((value :u32)))
(defcorechild fn2-core-test-child fn2-test-child
 :init (fn2-test-child-init (fn2-profile-get :test-child-rows profile) fn2-test-child)
 :profilep (unsigned-byte-p 32 (fn2-profile-get :test-child-rows profile))
 :why "Test-only persistent table registered outside layer A's books.")
(defun fn2-test-child-write-42-of (fn2-test-child)
  (declare (xargs :stobjs fn2-test-child :guard (fn2-test-child-wfp fn2-test-child)))
  (if (< 0 (fn2-test-child-rows fn2-test-child))
      (fn2-test-child-set-value 0 42 fn2-test-child)
    fn2-test-child))
(fn2-test-child-preserves fn2-test-child-write-42-of (fn2-test-child))
(defcost fn2-test-child-write-42 :child fn2-test-child-write-42-of
  :tables (fn2-core-test-child)
  :doc "Write 42 to row 0 of the registered test child table.")
; A late kind also reaches its own registered table through the one core.
(defun fn2-test-machine-initial-generation (slot base n gen)
  (declare (xargs :guard t) (ignore slot base n)) gen)
(defmachine fn2-test-machine
 :phases (:step) :fields ((stopped :bool))
 :budget (:bytes 4096 :steps 32 :descriptors 4) :capacity 1
 :initial ((generation fn2-test-machine-initial-generation))
 :arms ((:step (:do () (fn2-test-child-write-42)) (:charge :steps 1)))
 :observes ((:fence-result (:wake))))
(defmachine-arms fn2-test-machine :children)
(defmacro fn2-test-machine-events ()
 '(progn
    (defmachine-arms fn2-test-machine :wrappers)
    (defmachine-run fn2-test-machine)))
