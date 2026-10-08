;;; Shared native immutable no-replace publication effect.
;;;
;;; books/journal-publish owns the phase, requested action and outcome.  This
;;; file executes exactly that action and reports the syscall observation.  A
;;; visible final name after an error is never inspected to infer durability.
(in-package "ACL2")

(defun fnn-immutable-test-fault (point path operation-label)
  ; Test injection is reached through the production action loop.  The older
  ; FN_APP spelling remains while the workflow test packet lands.
  (let ((chosen
          (if (eq operation-label :clock-domain)
              (or (fnn-developer-selector "FN_BP_CLOCK_DOMAIN_TEST_FAIL") "")
            (or (fnn-developer-selector "FN_IMMUTABLE_PUBLISH_TEST_FAIL")
                (fnn-developer-selector "FN_APP_JOURNAL_TEST_FAIL") ""))))
    (when (string= chosen point) (fnn-os-fail sb-posix:eio path))))

(defvar *fnn-immutable-cleanups* nil
  "Post-authority stage cleanup receipts, guarded by the close-debt mutex.")
(fnn-guarded-by *fnn-immutable-cleanups* *fnn-close-debts-lock*)

(defun fnn-immutable-queue-cleanup (stage directory operation)
  "Stage cleanup only; no publication outcome depends on its observation."
  (sb-thread:with-mutex (*fnn-close-debts-lock*)
    (push (list :pending stage directory operation) *fnn-immutable-cleanups*))
  nil)

(defun fnn-immutable-drain-cleanups (&optional stage)
  "Take cleanup once and settle its receipt. Without STAGE, run off all locks;
with STAGE, retain only that legacy caller's immediate cleanup timing.
A calling record remains discoverable until settlement. An interrupted drain
leaves it for cold recovery; another drainer never reissues that unlink."
  (loop
    (let ((entry
            (sb-thread:with-mutex (*fnn-close-debts-lock*)
              (let ((entry (find-if (lambda (receipt)
                                      (and (eq (first receipt) :pending)
                                           (or (null stage) (eq (second receipt) stage))))
                                    *fnn-immutable-cleanups*)))
                (when entry (setf (first entry) :calling))
                entry))))
      (unless entry (return))
      ;; Best effort, exactly as the old inline cleanup. A leftover name
      ;; never revokes the final name's authority barrier.
      (handler-case
       (progn
        (fnn-unlink (second entry))
        (when (third entry)
          (fnn-immutable-test-fault "cleanup" (third entry) (fourth entry))
          (fnn-fsync-dir (third entry))))
       (fnn-os-error () nil))
      (sb-thread:with-mutex (*fnn-close-debts-lock*)
        (unless (and (member entry *fnn-immutable-cleanups* :test #'eq)
                     (eq (first entry) :calling))
          (fnn-fault "immutable cleanup lost its receipt"))
        (setf *fnn-immutable-cleanups*
              (delete entry *fnn-immutable-cleanups* :test #'eq))))))

(defun fnn-immutable-publish-effect
    (publication stage final final-directory octets
                 &key cleanup-directory observer operation-label fault-observer registered-step)
  "Publish with the existing immediate stage-cleanup timing.
Off-lock cleanup consumers use fnn-immutable-publish-deferred and drain after release."
  (unwind-protect
      (fnn-immutable-publish-deferred
       publication stage final final-directory octets
       :cleanup-directory cleanup-directory :observer observer
       :operation-label operation-label :fault-observer fault-observer
       :registered-step registered-step)
    (fnn-immutable-drain-cleanups stage)))

(defun fnn-immutable-publish-deferred
  (publication stage final final-directory octets
               &key cleanup-directory observer operation-label fault-observer registered-step)
  "Execute an ACL2-authorized immutable publication state.  PUBLICATION must
come from the caller's ACL2 allocation/admission machine after it establishes
exclusive authority and absence of that machine's exact final name.  Those are
trusted caller observations rather than protection from hostile raw Lisp.  The
executor does not assert the premise itself and returns fn-jpub's classification.
Stage cleanup is queued; the caller must drain it after releasing its locks."
  (unless (eq (fnn-immutable-close-observation) :closed)
    (fnn-indeterminate "prior immutable staging descriptor return remains unobserved"))
  (unless (and (eq (fnn-core 'fn-jpub-host-authorized-initialp publication) t)
               (eq (fnn-core 'fn-jpub-host-action publication) :stage))
    (fnn-fault "immutable publication lacks ACL2 authorization"))
  (let ((publication publication)
        (fd nil) (close-debt nil))
    (labels ((close-handle (handle)
               (handler-case
                   (fnn-immutable-close-handle handle stage final operation-label publication)
                 (serious-condition (condition)
                   (setq close-debt t) (error condition))))
             (advance (event)
               (setq publication
                     (if registered-step
                         (funcall registered-step publication event)
                       (fnn-core 'fn-jpub-host-step publication event))))
             (observed (point)
               ; Consumers use this for process-death tests at modelled cuts.
               ; The callback observes the already-reported ACL2 state and
               ; cannot alter the publication classification.
               (when observer (funcall observer point publication)))
             (fault-observed (point path)
               ; A test observer runs before the same syscall and inside the
               ; same fnn-os-error handler as a real failure.  OPERATION-LABEL
               ; is issued by the caller's ACL2 authorization operation.
               (when fault-observer
                 (funcall fault-observer operation-label point publication
                          path))
               ;; Clock-domain initialization has its own developer cut; an
               ;; older record-publication selector must still reach its
               ;; original operation after this startup prerequisite.
               (fnn-immutable-test-fault
                (case point
                  (:file-barrier "file-barrier")
                  (:begin-link "link")
                  (:directory-barrier "namespace")
                  (otherwise "stage"))
                path operation-label))
             (observe (ok-event error-event point thunk)
               (let ((ok
                       (handler-case (progn (funcall thunk) t)
                         (fnn-os-error () nil))))
                 (advance (if ok ok-event error-event))
                 (when (and ok point) (observed point)))))
      (fnn-unwind-cleanups
           ((loop until (eq (fnn-core 'fn-jpub-host-terminalp publication) t) do
             (case (fnn-core 'fn-jpub-host-action publication)
               (:stage
                (observe '(:stage-result :ok) '(:stage-result :error) nil
                         (lambda ()
                           (fault-observed :stage stage)
                           (setq fd (fnn-open stage
                                              (logior sb-posix:o-wronly
                                                      sb-posix:o-creat
                                                      sb-posix:o-excl)
                                              #o600))
                           (fnn-write-all fd octets))))
               (:file-barrier
                (observe '(:file-barrier-result :ok)
                         '(:file-barrier-result :error)
                         :file-barrier
                         (lambda ()
                           (fault-observed :file-barrier stage)
                           (fnn-fsync-file fd)
                           ; Retire the descriptor number before close: a
                           ; failing close may already have released it.
                           (let ((handle fd))
                             (setq fd nil)
                             (close-handle handle)))))
               (:begin-link (advance '(:link-begin)))
               (:link
                (let ((event
                        (handler-case
                            (progn (fault-observed :begin-link final)
                                   (fnn-link stage final)
                                   '(:link-result :ok))
                          (fnn-os-error (e)
                            (if (= (fnn-os-errno e) sb-posix:eexist)
                                '(:link-result :exists)
                              '(:link-result :error))))))
                  (advance event)
                  (observed :link-result)))
               (:directory-barrier
                (observe '(:directory-barrier-result :ok)
                         '(:directory-barrier-result :error)
                         :directory-barrier
                         (lambda ()
                           (fault-observed :directory-barrier final)
                           (fnn-fsync-dir final-directory))))
               (otherwise
                (fnn-fault "ACL2 returned no immutable publication action")))))
        (when fd
          (let ((handle fd))
            (setq fd nil)
            (handler-case (close-handle handle)
              (serious-condition (condition)
                (fnn-indeterminate "immutable staging descriptor return unobserved: ~a" condition)))))
        ; Cleanup is after the authority barrier and cannot change its result.
        ; Reopen sweeps a surviving stage; this best-effort barrier merely
        ; prevents clean runs from accumulating names after a process death.
        (fnn-immutable-queue-cleanup stage cleanup-directory operation-label)))
    (when close-debt
      (fnn-indeterminate "immutable staging descriptor return unobserved; custody held"))
    (fnn-core 'fn-jpub-host-outcome publication)))
