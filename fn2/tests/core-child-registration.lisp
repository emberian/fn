(in-package "ACL2")
(include-book "../books/core-children")
(include-book "../books/profile")
(defconst *fn2-test-child-profile*
  (put-assoc-equal :test-child-rows 4 *fn2-profile-tiny*))
(defcolumns fn2-test-child ((value :u32)))
(defcorechild fn2-core-test-child fn2-test-child
 :init (fn2-test-child-init (fn2-profile-get :test-child-rows profile) fn2-test-child)
 :profilep (unsigned-byte-p 32 (fn2-profile-get :test-child-rows profile))
 :why "Test-only persistent table registered outside layer A's books.")
; A late kind also reaches its own registered table through the one core.
(defun fn2-test-machine-initial-generation (slot base n gen)
  (declare (xargs :guard t) (ignore slot base n)) gen)
(defmachine fn2-test-machine
 :states (:step) :fields ((stopped :bool)) :accounts (:row)
 :budget (:bytes 4096 :steps 32 :descriptors 4) :capacity 1
 :initial ((generation fn2-test-machine-initial-generation))
 :observes ((:fence-result fn2-test-machine-observe))
 :continuations ((:step fn2-test-machine-step)))
(defmacro fn2-test-machine-events ()
 '(progn
    (defmachine-callback fn2-test-machine-observe fn2-test-machine
      (id event outcome reason count aux0 aux1) 1
      (mv id fn2-core))
    (in-theory (e/d (fn2-core-wfp) (fn2-test-child-rows)))
    (defmachine-callback fn2-test-machine-step fn2-test-machine (id budget) 4
      (let ((fn2-core
             (stobj-let ((fn2-test-child (fn2-core-test-child fn2-core)))
               (fn2-test-child)
               (if (< 0 (fn2-test-child-rows fn2-test-child))
                   (fn2-test-child-set-value 0 42 fn2-test-child) fn2-test-child)
               fn2-core)))
        (fn2-machine-result 0 1 0 nil fn2-core)))
    (in-theory (disable fn2-core-wfp))
    (defmachine-run fn2-test-machine)))
