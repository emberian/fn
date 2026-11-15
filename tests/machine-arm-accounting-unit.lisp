; Real generated children: explicit charges cannot erase :do work or the
; prefix before :goto. Physical read counts require separate refinements.
(in-package "ACL2")
(include-book "../books/machine-arms")
(include-book "std/testing/must-fail" :dir :system)

(defun fn2-accounting-lookup () (declare (xargs :guard t)) :ok)
(defun fn2-accounting-put () (declare (xargs :guard t)) :ok)
(defcost fn2-accounting-lookup :answers (:ok) :child fn2-accounting-lookup
 :bytes 8192 :steps 3 :doc "Accounting fixture: declared lookup charge.")
(defcost fn2-accounting-put :answers (:ok) :child fn2-accounting-put
 :bytes 4096 :steps 2 :doc "Accounting fixture: declared put charge.")
(defmachine fn2-accounting-probe
 :phases (:free :found :end)
 :fields ((count :u32))
 :budget (:bytes 12288 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :subarms ((put (:do (code) (fn2-accounting-put)) (:charge :bytes 17 :steps 1))
           (middle (:goto put))
           (release (:charge)))
 :arms ((:free (:idle))
        (:found (:do (code) (fn2-accounting-lookup)) (:goto middle))
        (:end (:do (code) (fn2-accounting-lookup)) (:goto release)))
 :observes ())
(defmachine-arms fn2-accounting-probe :children)
; Assert the entire returned tuple, including unchanged children. The
; dispatcher-generated formals determine the carriers; no twin arm body.
(make-event
 (let* ((name 'fn2-accounting-probe-run-found-children)
        (formals (getpropc name 'formals nil (w state)))
        (tuple (cadr (fn2-arms-sig name (w state)))))
  `(defthm fn2-accounting-found-whole-result
    (equal (,name ,@formals) (list 12288 5 0 nil ,@tuple))
    :hints (("Goal" :in-theory (enable ,name
      fn2-accounting-probe-sub-middle-children
      fn2-accounting-probe-sub-put-children
      fn2-accounting-lookup fn2-accounting-put))))))
(make-event
 (let* ((name 'fn2-accounting-probe-run-end-children)
        (formals (getpropc name 'formals nil (w state)))
        (tuple (cadr (fn2-arms-sig name (w state)))))
  `(defthm fn2-accounting-end-whole-result
    (equal (,name ,@formals) (list 8192 3 0 nil ,@tuple))
    :hints (("Goal" :in-theory (enable ,name
      fn2-accounting-probe-sub-release-children fn2-accounting-lookup))))))

; Same body, original smaller cap: it must not certify by dropping the
; caller's work. No supported profile limit is enlarged to admit it.
(defmachine fn2-accounting-too-small
 :phases (:free :found)
 :fields ((count :u32))
 :budget (:bytes 8192 :steps 32 :descriptors 0)
 :initial ((generation 1) (ready-prev *fn2-none*) (ready-next *fn2-none*))
 :subarms ((put (:do (code) (fn2-accounting-put)) (:charge :bytes 17 :steps 1)))
 :arms ((:free (:idle))
        (:found (:do (code) (fn2-accounting-lookup)) (:goto put)))
 :observes ())
(must-fail (defmachine-arms fn2-accounting-too-small :children))
