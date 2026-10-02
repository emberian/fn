(defmacro fnn-core-mv (name call)
  "Preserve fixed CALL's scalar MVs without an argument or result container.
NAME names the actual ACL2 subject. CALL uses its startup-selected callback;
its own scalar refusals remain results, while execution escapes are faults."
  (let ((outcome (gensym "OUTCOME")) (condition (gensym "CONDITION")))
    `(let ((,outcome :thrown))
       (multiple-value-prog1
           (catch 'raw-ev-fncall
             (handler-case
                 (multiple-value-prog1 ,call (setq ,outcome :ok))
               (serious-condition (,condition)
                 (setq ,outcome ,condition)
                 nil)))
         (case ,outcome
           (:ok nil)
           (:thrown (fnn-fixed-callback-fail ,name :raw-callback-escaped nil))
           (otherwise (fnn-fixed-callback-fail ,name :raw-callback-failed ,outcome)))))))

(defun fnn-owner-shared-action-locked (service cid thunk)
  "Run THUNK while the caller holds the owner mutex.

Only a known semantic refusal may leave this boundary without first fencing.
An indeterminate observation is exit 3.  A core/store fault, an unclassified
OS failure, or any other serious condition is exit 4.  The fence is installed
before the mutex can be released, so no queued client can mutate afterward."
  (handler-case
      (if (fnn-developer-selector "FN_NATIVE_FAULT_BACKTRACE")
          ;; Developer image only: the stack of a memory fault or any other
          ;; serious condition, printed where it was signalled (the handler
          ;; below has unwound it).
          (handler-bind ((serious-condition
                           (lambda (c)
                             (unless (typep c 'fnn-store-error)
                               (ignore-errors
                                (fnn-err "fault backtrace: ~a" c)
                                (sb-debug:print-backtrace :count 80 :stream *error-output*))))))
            (funcall thunk))
        (funcall thunk))
    (fnn-store-indeterminate (condition)
      (fnn-owner-stop-service-locked service +fnn-exit-uncertain+)
      (error condition))
    (fnn-store-fault (condition)
      (when (and cid (not (fnn-owner-connection-selected-p service)))
        (ignore-errors (fnn-owner-action 'fn-owner-fault cid)))
      (fnn-owner-stop-service-locked service +fnn-exit-fault+)
      (error condition))
    ;; FNN-STORE-ERROR is the existing known semantic-refusal class.  It has
    ;; made no ambiguous persistence observation and remains connection scoped.
    (fnn-store-error (condition) (error condition))
    ;; An OS or arbitrary failure inside a semantic/persistence action has no
    ;; safe connection-only attribution.  Preserve the shared state by stopping.
    ((or fnn-os-error serious-condition) (condition)
      (when (and cid (not (fnn-owner-connection-selected-p service)))
        (ignore-errors (fnn-owner-action 'fn-owner-fault cid)))
      (fnn-owner-stop-service-locked service +fnn-exit-fault+)
      (error condition))))
