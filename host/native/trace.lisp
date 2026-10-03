;;; Non-semantic, opt-in native span observations. Never log protocol data.
;;; Allocation counters are SBCL PROCESS totals, inclusive and approximate:
;;; simultaneous threads and nested spans overlap. They are not retained heap.
(in-package "ACL2")

(defstruct (fnn-trace-row (:constructor %make-fnn-trace-row))
  id parent cid operation connection-generation phase start duration bytes allocation-scope (outcome :active))
(defstruct (fnn-trace-state (:constructor %make-fnn-trace-state))
  rows (next 0) (attempts 0) (dropped 0) (sample-every 1) allocation
  (lock (sb-thread:make-mutex :name "native-trace")))
(defvar *fnn-trace-state* nil)
(defvar *fnn-trace-parent* nil)
(defvar *fnn-trace-operation* nil)
(defvar *fnn-trace-connection-generation* nil)

(defun fnn-trace-now ()
  "Monotonic runtime ticks, converted to integer microseconds; resolution
is INTERNAL-TIME-UNITS-PER-SECOND, not a promised microsecond clock."
  (floor (* (get-internal-real-time) 1000000) internal-time-units-per-second))

(defun fnn-trace-start (&key (capacity 4096) (sample-every 1) allocation)
  "A bounded diagnostic buffer. ALLOCATION is NIL, :PROCESS or
:ISOLATED-PROCESS. Isolation is a caller assertion, never inferred from CID."
  (unless (and (integerp capacity) (plusp capacity)
               (integerp sample-every) (plusp sample-every)
               (member allocation '(nil :process :isolated-process)))
    (error "invalid native trace configuration"))
  (setf *fnn-trace-state*
        (%make-fnn-trace-state :rows (make-array capacity :initial-element nil)
                              :sample-every sample-every :allocation allocation)))

(defun fnn-trace-configure ()
  "Explicit process diagnostic options; no saved build-host trace state."
  (setf *fnn-trace-state* nil *fnn-trace-parent* nil)
  (when (equal (sb-ext:posix-getenv "FN_TRACE") "1")
    (let ((mode (sb-ext:posix-getenv "FN_TRACE_ALLOC")))
      (fnn-trace-start
       :capacity (parse-integer (or (sb-ext:posix-getenv "FN_TRACE_CAPACITY") "4096"))
       :sample-every (parse-integer (or (sb-ext:posix-getenv "FN_TRACE_SAMPLE_EVERY") "1"))
       :allocation (cond ((or (null mode) (equal mode "0")) nil)
                         ((equal mode "process") :process)
                         ((equal mode "isolated-process") :isolated-process)
                         (t (error "FN_TRACE_ALLOC expects 0, process or isolated-process")))))))

(defun fnn-trace-begin (state phase cid operation connection-generation)
  "Reserve one bounded row. Identity is diagnostic, not durable acceptance."
  (unless (and (keywordp phase)
               (every (lambda (c) (or (find c "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-_") nil))
                      (symbol-name phase))
               ;; Sampling can skip almost every span. Do not allocate a
               ;; temporary identity list on each skipped attempt.
               (typep cid '(or null (integer 0 *)))
               (typep operation '(or null (integer 0 *)))
               (typep connection-generation '(or null (integer 0 *))))
    (error "trace phase must be a keyword; CID must be a nonnegative integer"))
  (sb-thread:with-mutex ((fnn-trace-state-lock state))
    (let ((id (incf (fnn-trace-state-attempts state))))
      (when (zerop (mod (1- id) (fnn-trace-state-sample-every state)))
        (if (< (fnn-trace-state-next state) (length (fnn-trace-state-rows state)))
            (let ((row (%make-fnn-trace-row
                        :id id :parent *fnn-trace-parent* :cid cid :operation operation
                        :connection-generation connection-generation :phase phase
                        :allocation-scope (fnn-trace-state-allocation state))))
              (setf (aref (fnn-trace-state-rows state) (fnn-trace-state-next state)) row)
              (incf (fnn-trace-state-next state))
              row)
          (progn (incf (fnn-trace-state-dropped state)) nil))))))

(defun fnn-trace-finish (state row start bytes outcome)
  ;; Sample before observer locking/formatting; this still includes runtime
  ;; counter overhead and allocations by other threads in the same process.
  (let ((duration (- (fnn-trace-now) start))
        (allocated (and bytes (- (sb-ext:get-bytes-consed) bytes))))
    (sb-thread:with-mutex ((fnn-trace-state-lock state))
      (setf (fnn-trace-row-start row) start
            (fnn-trace-row-duration row) duration
            (fnn-trace-row-bytes row) allocated
            (fnn-trace-row-outcome row) outcome))))

(defmacro fnn-trace-span ((phase &key cid (operation '*fnn-trace-operation*)
                                      (connection-generation '*fnn-trace-connection-generation*)) &body body)
  "Preserve all values and exits; measure one shared span lifetime. Off:
one special-variable test, no identity evaluation, clock read or thunk."
  (let ((state (gensym "STATE")) (row (gensym "ROW"))
        (start (gensym "START")) (bytes (gensym "BYTES")) (ready (gensym "READY"))
        (outcome (gensym "OUTCOME")))
    `(if *fnn-trace-state*
         (let* ((,state *fnn-trace-state*)
                (,row (ignore-errors (fnn-trace-begin ,state ,phase ,cid ,operation ,connection-generation))))
           (if ,row
               (multiple-value-bind (,start ,bytes ,ready)
                   (ignore-errors
                     (values (fnn-trace-now)
                             (and (fnn-trace-state-allocation ,state) (sb-ext:get-bytes-consed)) t))
                 (if ,ready
                     (let* ((*fnn-trace-parent* (fnn-trace-row-id ,row))
                            (*fnn-trace-operation* (fnn-trace-row-operation ,row))
                            (*fnn-trace-connection-generation* (fnn-trace-row-connection-generation ,row))
                            (,outcome :nonlocal-exit))
                       (unwind-protect
                            (handler-bind ((serious-condition (lambda (condition)
                                                                (declare (ignore condition))
                                                                (setf ,outcome :condition))))
                              (multiple-value-prog1 (progn ,@body) (setf ,outcome :returned)))
                         ;; A diagnostic failure must not replace a primary exit.
                         (ignore-errors (fnn-trace-finish ,state ,row ,start ,bytes ,outcome))))
                   (progn ,@body)))
             (progn ,@body)))
       (progn ,@body))))

(defun fnn-trace-report (&optional (stream *error-output*))
  "JSON lines from the bounded sink. Intended after workers have joined.
No condition strings, objects, thread names, peer addresses or payloads."
  (when *fnn-trace-state*
    (let ((state *fnn-trace-state*))
      (sb-thread:with-mutex ((fnn-trace-state-lock state))
        (dotimes (i (fnn-trace-state-next state))
          (let ((row (aref (fnn-trace-state-rows state) i)))
            (unless (eq (fnn-trace-row-outcome row) :active)
              (format stream
                      "~&FN_TRACE {\"type\":\"span\",\"span_id\":~d,\"parent_id\":~a,\"connection_id\":~a,\"operation_id\":~a,\"connection_generation\":~a,\"phase\":\"~(~a~)\",\"start_us\":~d,\"duration_us\":~d,\"allocated_bytes\":~a,\"allocation_scope\":\"~(~a~)\",\"outcome\":\"~(~a~)\"}~%"
                      (fnn-trace-row-id row) (or (fnn-trace-row-parent row) "null")
                      (or (fnn-trace-row-cid row) "null")
                      (or (fnn-trace-row-operation row) "null")
                      (or (fnn-trace-row-connection-generation row) "null") (fnn-trace-row-phase row)
                      (fnn-trace-row-start row) (fnn-trace-row-duration row)
                      (or (fnn-trace-row-bytes row) "null")
                      (or (fnn-trace-row-allocation-scope row) :disabled)
                      (fnn-trace-row-outcome row)))))
        (format stream "~&FN_TRACE {\"type\":\"summary\",\"attempts\":~d,\"recorded\":~d,\"dropped\":~d,\"incomplete\":~d,\"sample_every\":~d,\"clock_ticks_per_second\":~d}~%"
                (fnn-trace-state-attempts state) (fnn-trace-state-next state)
                (fnn-trace-state-dropped state)
                (count :active (fnn-trace-state-rows state) :key
                       (lambda (row) (and row (fnn-trace-row-outcome row))))
                (fnn-trace-state-sample-every state)
                internal-time-units-per-second))
      (finish-output stream))))

(defun fnn-trace-hotspots (&optional (stream *error-output*) (limit 10))
  "Rank the existing bounded sink without dumping every chronological row.
Totals are inclusive process/nested observations, never unique allocation or
retained heap. Snapshot aggregation holds only the private trace leaf mutex;
sorting and output happen after release. The sink remains available."
  (unless (and (integerp limit) (plusp limit))
    (error "trace hotspot limit must be a positive integer"))
  (let ((state *fnn-trace-state*) (groups (make-hash-table :test 'equal))
        (attempts 0) (recorded 0) (dropped 0) (incomplete 0) (sample-every 1))
    (when state
      (sb-thread:with-mutex ((fnn-trace-state-lock state))
        (setf attempts (fnn-trace-state-attempts state)
              recorded (fnn-trace-state-next state)
              dropped (fnn-trace-state-dropped state)
              sample-every (fnn-trace-state-sample-every state))
        (dotimes (i recorded)
          (let ((row (aref (fnn-trace-state-rows state) i)))
            (if (eq (fnn-trace-row-outcome row) :active)
                (incf incomplete)
              (let* ((key (list (fnn-trace-row-phase row) (fnn-trace-row-allocation-scope row)))
                     ;; samples, duration, allocation samples, bytes, max bytes.
                     (stats (or (gethash key groups)
                                (setf (gethash key groups) (vector 0 0 0 0 0)))))
                (incf (aref stats 0))
                (incf (aref stats 1) (fnn-trace-row-duration row))
                (when (fnn-trace-row-bytes row)
                  (incf (aref stats 2))
                  (incf (aref stats 3) (fnn-trace-row-bytes row))
                  (setf (aref stats 4) (max (aref stats 4) (fnn-trace-row-bytes row)))))))))
      (let ((rows (loop for key being the hash-keys of groups using (hash-value stats)
                        collect (cons key stats))))
        ;; Allocation-enabled groups rank by mean allocated bytes. Clock-only
        ;; groups rank separately by mean duration; units never share a score.
        (setf rows
              (stable-sort rows
               (lambda (a b)
                 (let ((x (cdr a)) (y (cdr b)))
                   (cond ((and (plusp (aref x 2)) (zerop (aref y 2))) t)
                         ((and (zerop (aref x 2)) (plusp (aref y 2))) nil)
                         ((plusp (aref x 2))
                          (> (/ (aref x 3) (aref x 2)) (/ (aref y 3) (aref y 2))))
                         (t (> (/ (aref x 1) (aref x 0)) (/ (aref y 1) (aref y 0)))))))))
        (format stream "~&FN_TRACE_HOTSPOTS groups=~d showing=~d attempts=~d recorded=~d dropped=~d incomplete=~d every=~d~%"
                (length rows) (min limit (length rows)) attempts recorded dropped incomplete sample-every)
        (format stream "Inclusive samples; process/nested deltas are not unique allocation, retained heap or GC volume.~%")
        (format stream "phase scope samples mean-us mean-allocated max-allocated~%")
        (loop for (key . stats) in rows for i below limit do
          (format stream "~(~a~) ~(~a~) ~d ~,1f ~a ~d~%"
                  (first key) (or (second key) :disabled) (aref stats 0)
                  (/ (aref stats 1) (aref stats 0))
                  (if (plusp (aref stats 2))
                      (format nil "~,1f" (/ (aref stats 3) (aref stats 2))) "disabled")
                  (aref stats 4)))
        (finish-output stream)))))
