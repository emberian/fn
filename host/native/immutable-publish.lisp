;;; Shared native immutable no-replace publication effect.
;;;
;;; books/journal-publish owns the phase, requested action and outcome.  This
;;; file executes exactly that action and reports the syscall observation.  A
;;; visible final name after an error is never inspected to infer durability.
(in-package "ACL2")

(defun fnn-immutable-test-fault (point path)
  ; Test injection is reached through the production action loop.  The older
  ; FN_APP spelling remains while the workflow test packet lands.
  (let ((chosen (or (sb-ext:posix-getenv
                     "FN_IMMUTABLE_PUBLISH_TEST_FAIL")
                    (sb-ext:posix-getenv "FN_APP_JOURNAL_TEST_FAIL") "")))
    (when (string= chosen point) (fnn-os-fail sb-posix:eio path))))

(defun fnn-immutable-publish-effect
  (publication stage final final-directory octets
               &key cleanup-directory observer operation-label fault-observer)
  "Execute an ACL2-authorized immutable publication state.  PUBLICATION must
come from the caller's ACL2 allocation/admission machine after it establishes
exclusive authority and absence of that machine's exact final name.  Those are
trusted caller observations rather than protection from hostile raw Lisp.  The
executor does not assert the premise itself and returns fn-jpub's classification."
  (unless (and (eq (fnn-core 'fn-jpub-host-authorized-initialp publication) t)
               (eq (fnn-core 'fn-jpub-host-action publication) :stage))
    (fnn-fault "immutable publication lacks ACL2 authorization"))
  (let ((publication publication)
        (fd nil))
    (labels ((advance (event)
               (setq publication
                     (fnn-core 'fn-jpub-host-step publication event)))
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
               (fnn-immutable-test-fault
                (case point
                  (:file-barrier "file-barrier")
                  (:begin-link "link")
                  (:directory-barrier "namespace")
                  (otherwise "stage"))
                path))
             (observe (ok-event error-event point thunk)
               (let ((ok
                       (handler-case (progn (funcall thunk) t)
                         (fnn-os-error () nil))))
                 (advance (if ok ok-event error-event))
                 (when (and ok point) (observed point)))))
      (unwind-protect
           (loop until (eq (fnn-core 'fn-jpub-host-terminalp publication) t) do
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
                             (fnn-close handle)))))
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
                (fnn-fault "ACL2 returned no immutable publication action"))))
        (when fd (ignore-errors (fnn-close fd)))
        ; Cleanup is after the authority barrier and cannot change its result.
        ; Reopen sweeps a surviving stage; this best-effort barrier merely
        ; prevents clean runs from accumulating names after a process death.
        (ignore-errors
          (fnn-unlink stage)
          (when cleanup-directory
            ; Cleanup is explicitly post-authority.  Its fault hook proves
            ; consumers do not turn a durable final-name barrier into an
            ; uncertain publication merely because stage removal was not
            ; durably observed.
            (fnn-immutable-test-fault "cleanup" cleanup-directory)
            (fnn-fsync-dir cleanup-directory)))))
    (fnn-core 'fn-jpub-host-outcome publication)))
