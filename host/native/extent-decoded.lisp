;;; Actual stored-DEFLATE window dispatcher. Loaded after extent.lisp by
;;; the physical integration, which admits and owns every supplied buffer.
;;; This driver does not admit jobs or allocate a whole compressed payload.
(in-package "ACL2")

(defun fnn-extent-decoded-window-realize-octet (file eoff elen poff compressed trailer decoded dict i)
  "The actual scalar getter either borrows a returned decoded byte or throws
its full core-selected cold descriptor while the captured owner is held."
  (let* ((descriptor (fnn-core 'fn-pwz-cold-descriptor
                       file eoff elen poff compressed trailer decoded dict i))
         (dict-id (fnn-core 'fn-pwz-nth 8 descriptor)))
    (multiple-value-bind (word byte)
        (if *fnn-extent-window-worker*
            (fnn-extent-decoded-window-byte-at
              *fnn-extent-window-worker* *fnn-extent-window-token*
              file eoff elen poff compressed trailer decoded dict-id i)
          (values :unavailable nil))
      (cond ((eq word :byte) byte)
            ((member word '(:cancelled :stale-job))
             (throw 'fnn-extent-window-refused (values word nil nil nil)))
            ((eq word :unavailable) (throw 'fnn-extent-cold descriptor))
            (t (error 'fnn-extent-fault
                      :message "arena-extent-read: decoded window was not an authenticated returned result"))))))

;;; The native envelope is published on the existing worker before the
;;; sanctioned private creator runs. It preserves partial construction and
;;; torn semantic calls; it is never a second file/token directory.
(defstruct fnn-decoded-activation job (stage :constructing))

(defmacro fnn-decoded-semantic ((activation) &body body)
  (let ((saved (gensym "DECODED-ACTIVATION-"))
        (answer (gensym "DECODED-ANSWER-")))
    `(let ((,saved ,activation))
       (unless (member (fnn-decoded-activation-stage ,saved) '(:constructing :idle))
         (fnn-fault "decoded private semantic step was already entered"))
       (setf (fnn-decoded-activation-stage ,saved) :calling)
       (let ((,answer (progn ,@body)))
         (setf (fnn-decoded-activation-stage ,saved) :idle)
         ,answer))))

(defun fnn-extent-decoded-window-run (worker token)
  "Same worker/token/pool; actual retained ACL2 controller selects each step.
The issuer draws its declared fixed-storage projection before this entry;
allocator/GC and pointed-to controller graphs remain outside that partial scope."
  (let* ((activation (make-fnn-decoded-activation))
         (fd nil) (incarnation nil))
    (setf (fnn-cold-worker-decoded worker) activation)
    (sb-thread:with-mutex (*fnn-extent-lock*)
      (unless (first (fnn-core-cold-pool 'fn-owner-page-window-work-permittedp
                       (fnn-cold-worker-row worker) token))
        (fnn-fault "decoded constructor lacks its exact running pool draw"))
      (setq fd (gethash (fnn-core 'fn-pwz-nth 2 token) *fnn-extent-fds*)
            incarnation (gethash (fnn-core 'fn-pwz-nth 2 token) *fnn-extent-incarnations*)))
    (unless (and fd incarnation) (fnn-fault "decoded issued file closed"))
    ;; This exact registered zero-input creator uses the validated allocation
    ;; ABI. All decisions below follow normal semantic dispatch.
    (setf (fnn-decoded-activation-job activation)
          (fnn-decoded-semantic (activation)
            (fnn-core 'create-fn-decoded-job)))
    (sb-thread:with-mutex (*fnn-extent-lock*)
      (destructuring-bind (word job &rest ignored)
          (fnn-decoded-semantic (activation)
            (fnn-call 'fn-owner-page-decoded-job-assign
              (fnn-cold-worker-row worker) token token incarnation
              (fnn-decoded-activation-job activation) (fnn-live-page-read-pool)))
        (declare (ignore ignored))
        (setf (fnn-decoded-activation-job activation) job)
        (unless (eq word :decoded-assigned) (fnn-fault "decoded assignment refused"))))
    (destructuring-bind (word job)
        (fnn-decoded-semantic (activation)
          (fnn-call 'fn-dwj-begin token (fnn-decoded-activation-job activation)))
      (setf (fnn-decoded-activation-job activation) job)
      (unless (eq word :decoded-started) (fnn-fault "decoded initialization refused")))
    (loop
      (unless (sb-thread:with-mutex (*fnn-extent-lock*)
                (first (fnn-core-cold-pool 'fn-owner-page-window-work-permittedp
                         (fnn-cold-worker-row worker) token)))
        (return nil))
      (destructuring-bind (word effect job)
          (fnn-decoded-semantic (activation)
            (fnn-call 'fn-dwj-one token (fnn-decoded-activation-job activation)))
        (setf (fnn-decoded-activation-job activation) job)
        (case word
          (:read
           ;; Only this core-selected effect authorizes the physical write
           ;; into the fixed private child. That alias dies with this call.
           (let* ((read-effect (fourth effect))
                  (status (fnn-extent-window-pread
                            fd (svref job 1) (fifth read-effect) (sixth read-effect))))
             (destructuring-bind (answer next)
                 (fnn-decoded-semantic (activation)
                   (fnn-call 'fn-dwj-read-observation token (third effect) status job))
               (declare (ignore answer))
               (setf (fnn-decoded-activation-job activation) next))))
          ((:ready :refused) (return activation))
          ((:stale-decoded-worker :stale-decoded-read)
           (fnn-fault "decoded retained controller refused its current activation"))
          (otherwise nil))))))

(defun fnn-extent-decoded-window-outcome (worker token)
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (unless (fnn-extent-executor-observe-returned worker)
      (return-from fnn-extent-decoded-window-outcome :pending))
    (when (fnn-core-cold-single 'fn-pwx-boundp
              (fnn-core-cold-single 'fn-owner-page-read-ledger (fnn-live-page-read-pool))
              (fnn-cold-worker-row worker) token :cancelled-returned)
      (return-from fnn-extent-decoded-window-outcome :cancelled))
    (let ((result (fnn-cold-worker-result worker)))
      (when (typep result 'condition) (error result))
      (unless (and (fnn-decoded-activation-p result)
                   (eq (fnn-decoded-activation-stage result) :idle))
        (fnn-fault "decoded result lacks a completed private activation"))
      (first (fnn-call 'fn-owner-page-decoded-job-outcome
               (fnn-cold-worker-row worker) token
               (fnn-decoded-activation-job result) (fnn-live-page-read-pool))))))

(defun fnn-extent-decoded-window-byte-at
    (worker token file eoff elen poff compressed trailer decoded dict-id i)
  "Core checks exact returned worker, complete codec identity and coordinates."
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (unless (fnn-extent-executor-observe-returned worker)
      (return-from fnn-extent-decoded-window-byte-at (values :pending nil)))
    (let ((result (fnn-cold-worker-result worker)))
      (when (typep result 'condition) (error result))
      (unless (and (fnn-decoded-activation-p result)
                   (eq (fnn-decoded-activation-stage result) :idle))
        (fnn-fault "decoded borrow lacks a completed private activation"))
      (destructuring-bind (word byte)
          (fnn-call 'fn-owner-page-decoded-job-byte-at
            (fnn-cold-worker-row worker) token file eoff elen poff compressed
            trailer decoded dict-id i (fnn-decoded-activation-job result)
            (fnn-live-page-read-pool))
        (values word byte)))))
