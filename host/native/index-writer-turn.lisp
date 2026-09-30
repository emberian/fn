;;; Installed writer executor transport. INTERNAL, not activated: callbacks
;;; require their actual guarded/declaration cohort and a funded installer.
(in-package "ACL2")

(defstruct (fnn-index-writer-binding
            (:constructor %make-fnn-index-writer-binding) (:copier nil))
  pool slots slot fuel mio arena cat prepare resume step complete finish fault)

(defun fnn-index-writer-binding-make (pool slots slot fuel mio arena cat)
  "Funded installer only; retain the actual shared objects and core endpoint."
  (%make-fnn-index-writer-binding
   :pool pool :slots slots :slot slot :fuel fuel :mio mio :arena arena :cat cat
   :prepare (fnn-fixed-raw-callback 'fn-owner-cat-prepare-indexed)
   :resume (fnn-fixed-raw-callback 'fn-owner-index-writer-begin)
   :step (fnn-fixed-raw-callback 'fn-owner-index-writer-step-owned)
   :complete (fnn-fixed-raw-callback 'fn-owner-index-writer-complete-owned)
   :finish (fnn-fixed-raw-callback 'fn-owner-index-writer-finish)
   :fault (fnn-fixed-raw-callback 'fn-owner-index-writer-fault)))

(defun fnn-index-writer-fault-locked (binding)
  (multiple-value-bind (word slots pool state)
      (fnn-core-mv 'fn-owner-index-writer-fault
        (funcall (fnn-index-writer-binding-fault binding)
                 (fnn-index-writer-binding-slots binding)
                 (fnn-index-writer-binding-pool binding) *the-live-state*))
    (declare (ignore state))
    (setf (fnn-index-writer-binding-slots binding) slots
          (fnn-index-writer-binding-pool binding) pool)
    word))

(defun fnn-index-writer-prepare-locked (binding)
  "Actual sealed prepare and entered BODY remain in one owner/extent span."
  (let ((returned nil))
    (unwind-protect
        (multiple-value-prog1
            (multiple-value-bind (erp word token slots mio pool state)
                (fnn-core-mv 'fn-owner-cat-prepare-indexed
                  (funcall (fnn-index-writer-binding-prepare binding)
                           (fnn-index-writer-binding-slot binding)
                           (fnn-index-writer-binding-fuel binding)
                           (fnn-index-writer-binding-slots binding)
                           (fnn-index-writer-binding-mio binding)
                           (fnn-index-writer-binding-arena binding)
                           (fnn-index-writer-binding-cat binding)
                           (fnn-index-writer-binding-pool binding) *the-live-state*))
              (declare (ignore state))
              (setf (fnn-index-writer-binding-slots binding) slots
                    (fnn-index-writer-binding-pool binding) pool
                    (fnn-index-writer-binding-mio binding) mio)
              (when erp (fnn-fixed-callback-fail 'fn-owner-cat-prepare-indexed :core-error erp))
              (setf (fnn-index-writer-binding-mio binding) mio)
              (values word token))
          (setf returned t))
      (unless returned (fnn-index-writer-fault-locked binding)))))

(defun fnn-index-writer-resume-locked (binding)
  "Resume the actual retained token; do not repeat sealed prepare or issue."
  (let ((returned nil))
    (unwind-protect
        (multiple-value-prog1
            (multiple-value-bind (word token mio pool state)
                (fnn-core-mv 'fn-owner-index-writer-begin
                  (funcall (fnn-index-writer-binding-resume binding)
                           (fnn-index-writer-binding-slots binding)
                           (fnn-index-writer-binding-mio binding)
                           (fnn-index-writer-binding-arena binding)
                           (fnn-index-writer-binding-pool binding) *the-live-state*))
              (declare (ignore state))
              (setf (fnn-index-writer-binding-mio binding) mio
                    (fnn-index-writer-binding-pool binding) pool)
              (values word token))
          (setf returned t))
      (unless returned (fnn-index-writer-fault-locked binding)))))

(defun fnn-index-writer-step-locked (binding)
  "Execute one core quantum under the retained executor and carried guard."
  (let ((returned nil))
    (unwind-protect
        (multiple-value-prog1
            (multiple-value-bind (word left mio state)
                (fnn-core-mv 'fn-owner-index-writer-step-owned
                  (funcall (fnn-index-writer-binding-step binding)
                           (fnn-index-writer-binding-fuel binding)
                           (fnn-index-writer-binding-slots binding)
                           (fnn-index-writer-binding-mio binding)
                           (fnn-index-writer-binding-pool binding) *the-live-state*))
              (declare (ignore state))
              (setf (fnn-index-writer-binding-mio binding) mio)
              (values word left))
          (setf returned t))
      (unless returned (fnn-index-writer-fault-locked binding)))))

(defun fnn-index-writer-complete-locked (binding)
  "Call only at durable owner completion, before clearing the pending PC."
  (let ((returned nil))
    (unwind-protect
        (multiple-value-prog1
            (multiple-value-bind (word left mio state)
                (fnn-core-mv 'fn-owner-index-writer-complete-owned
                  (funcall (fnn-index-writer-binding-complete binding)
                           (fnn-index-writer-binding-fuel binding)
                           (fnn-index-writer-binding-slots binding)
                           (fnn-index-writer-binding-mio binding)
                           (fnn-index-writer-binding-pool binding) *the-live-state*))
              (declare (ignore left state))
              (setf (fnn-index-writer-binding-mio binding) mio)
              word)
          (setf returned t))
      (unless returned (fnn-index-writer-fault-locked binding)))))

(defun fnn-index-writer-finish-locked (binding)
  "Actual outer epilogue only; yields and retained aliases do not finish."
  (let ((returned nil))
    (unwind-protect
        (multiple-value-prog1
            (multiple-value-bind (word slots pool state)
                (fnn-core-mv 'fn-owner-index-writer-finish
                  (funcall (fnn-index-writer-binding-finish binding)
                           (fnn-index-writer-binding-slots binding)
                           (fnn-index-writer-binding-pool binding) *the-live-state*))
              (declare (ignore state))
              (setf (fnn-index-writer-binding-slots binding) slots
                    (fnn-index-writer-binding-pool binding) pool)
              (unless (eq word :left)
                (fnn-fixed-callback-fail 'fn-owner-index-writer-finish :receipt-not-consumed word))
              word)
          (setf returned t))
      (unless returned (fnn-index-writer-fault-locked binding)))))
