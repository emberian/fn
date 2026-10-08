;;; Non-semantic, opt-in native span observations. Never log protocol data.
;;; Allocation counters are SBCL PROCESS totals, inclusive and approximate:
;;; simultaneous threads and nested spans overlap. They are not retained heap.
;;;
;;; Per-request cost columns (program section 2b), each labelled with its scope:
;;; cpu_us the serving THREAD's user+system CPU (clock_gettime
;;; CLOCK_THREAD_CPUTIME_ID on Linux and Darwin; the PROCESS run time elsewhere,
;;; cpu_scope says which); gc_us and gc_count PROCESS-wide; read_octets,
;;; write_octets and syscalls THREAD-local (io.lisp's fnn-io-counters, bound by
;;; the span); rss_kib the PROCESS resident size, Linux only, every Nth top-level
;;; span.  gc_count is a lower bound: SBCL runs *after-gc-hooks* in its finalizer
;;; thread, so a GC at the very end of a span can be counted by the next one; a
;;; changed GC epoch inside the span makes the count at least 1.
;;;
;;; Tracing is switched by the operator, never by the environment: `fn operator
;;; CONFIG trace on|off|drain' (books/decision-trace.lisp fn-dtrace-verb
;;; decides; host/native/control.lisp carries the frame).  `trace on' starts
;;; the span state below and the DECISION RING at the end of this file, both
;;; from the one plan ACL2 admitted from the profile's [trace] table
;;; (fn-dtrace-admit).
(in-package "ACL2")

(defstruct (fnn-trace-row (:constructor %make-fnn-trace-row))
  id parent cid operation connection-generation phase start duration bytes allocation-scope (outcome :active)
  ;; Start marks while :active, then the span's deltas (cost columns).
  (cpu 0) (gc-us 0) (gc-count 0) (read 0) (write 0) (syscalls 0) gc-epoch rss-kib)
(defstruct (fnn-trace-state (:constructor %make-fnn-trace-state))
  rows (next 0) (attempts 0) (dropped 0) (sample-every 1) allocation
  ;; rss-every 0: never sampled.  rss-ticket counts top-level span ends (car).
  (rss-every 0) (rss-ticket (list 0)) rss-fd
  (lock (sb-thread:make-mutex :name "native-trace")))
(defvar *fnn-trace-gc-cell* (list 0)
  "The car counts completed collections seen by FNN-TRACE-AFTER-GC (atomic).")
(defparameter *fnn-trace-cpu-scope* #+(or linux darwin) :thread #-(or linux darwin) :process)
(declaim (special *fnn-io-counters*)) ; io.lisp owns it (fnn-io-counters)
(defvar *fnn-trace-state* nil)
(defvar *fnn-dtrace* nil
  "NIL when decision tracing is off (the default); else the live ring
(host/native/trace.lisp, the end of this file).")
(defvar *fnn-trace-parent* nil)
(defvar *fnn-trace-parent-state* nil)
(defvar *fnn-trace-operation* nil)
(defvar *fnn-trace-connection-generation* nil)
;; The owner quantum's span label: :control inside a control request (an
;; operator post), :over-cursor for the cursor quanta, :commit for the
;; committer's, otherwise the gate class the hold was admitted as.
(defvar *fnn-trace-label* :other)

(defun fnn-trace-reset ()
  "Start a run with no tracing, whatever an earlier run in this image left."
  (fnn-trace-release)
  (setf *fnn-trace-state* nil *fnn-trace-parent* nil *fnn-trace-parent-state* nil
        *fnn-dtrace* nil))

(defun fnn-trace-now ()
  "Monotonic runtime ticks, converted to integer microseconds; resolution
is INTERNAL-TIME-UNITS-PER-SECOND, not a promised microsecond clock."
  (floor (* (get-internal-real-time) 1000000) internal-time-units-per-second))

(defun fnn-trace-after-gc ()
  (sb-ext:atomic-incf (car *fnn-trace-gc-cell*)))

(defun fnn-trace-release ()
  "Remove what tracing installed in the runtime: the after-GC hook and the
resident-size descriptor."
  (setf sb-ext:*after-gc-hooks* (remove 'fnn-trace-after-gc sb-ext:*after-gc-hooks*))
  (let ((state *fnn-trace-state*))
    (when (and state (fnn-trace-state-rss-fd state))
      (ignore-errors (sb-unix:unix-close (fnn-trace-state-rss-fd state)))
      (setf (fnn-trace-state-rss-fd state) nil))))

(defun fnn-trace-thread-cpu-us ()
  "CPU microseconds of the calling thread (cpu_scope :thread), else of the process."
  #+(or linux darwin)
  (sb-alien:with-alien ((ts (array sb-alien:long 2)))
    ;; CLOCK_THREAD_CPUTIME_ID: 3 on Linux, 16 on Darwin.
    (if (zerop (sb-alien:alien-funcall
                (sb-alien:extern-alien "clock_gettime"
                                       (function sb-alien:int sb-alien:int (* (array sb-alien:long 2))))
                #+linux 3 #+darwin 16 (sb-alien:addr ts)))
        (+ (* (sb-alien:deref ts 0) 1000000) (floor (sb-alien:deref ts 1) 1000))
      0))
  #-(or linux darwin)
  (floor (* (get-internal-run-time) 1000000) internal-time-units-per-second))

(defun fnn-trace-rss-kib (state)
  "Resident KiB from the preopened /proc/self/statm descriptor, else NIL."
  #+linux
  (let ((fd (fnn-trace-state-rss-fd state)))
    (when fd
      (sb-alien:with-alien ((buffer (array (sb-alien:unsigned 8) 96)))
        (let ((n (sb-alien:alien-funcall
                  (sb-alien:extern-alien "pread" (function sb-alien:long sb-alien:int
                                                           (* (array (sb-alien:unsigned 8) 96))
                                                           sb-alien:unsigned-long sb-alien:long))
                  fd (sb-alien:addr buffer) 96 0))
              (i 0) (field 0) (value 0))
          ;; "size resident shared ...": the second field, in pages.
          (when (plusp n)
            (loop while (< i n) do
              (let ((c (sb-alien:deref buffer i)))
                (cond ((= c 32) (incf field) (when (= field 2) (return)))
                      ((and (= field 1) (<= 48 c 57)) (setf value (+ (* value 10) (- c 48))))))
              (incf i))
            (floor (* value (sb-alien:alien-funcall
                             (sb-alien:extern-alien "getpagesize" (function sb-alien:int))))
                   1024))))))
  #-linux (progn state nil))

(defun fnn-trace-mark (row)
  "Take ROW's start marks (the span's thread, now)."
  (let ((c *fnn-io-counters*))
    (setf (fnn-trace-row-cpu row) (fnn-trace-thread-cpu-us)
          (fnn-trace-row-gc-us row) sb-ext:*gc-run-time*
          (fnn-trace-row-gc-count row) (car *fnn-trace-gc-cell*)
          (fnn-trace-row-gc-epoch row) sb-kernel::*gc-epoch*
          (fnn-trace-row-read row) (fnn-io-counters-read c)
          (fnn-trace-row-write row) (fnn-io-counters-write c)
          (fnn-trace-row-syscalls row) (fnn-io-counters-syscalls c))))

(defun fnn-trace-start (&key (capacity 4096) (sample-every 1) allocation (rss-every 0))
  "A bounded diagnostic buffer. ALLOCATION is NIL, :PROCESS or
:ISOLATED-PROCESS. Isolation is a caller assertion, never inferred from CID.
RSS-EVERY is the plan's resident-size sampling interval in requests (0: never)."
  (unless (and (integerp capacity) (plusp capacity)
               (integerp sample-every) (plusp sample-every)
               (member allocation '(nil :process :isolated-process))
               (typep rss-every '(integer 0 1000000)))
    (error "invalid native trace configuration"))
  (fnn-trace-release)
  (pushnew 'fnn-trace-after-gc sb-ext:*after-gc-hooks*)
  (setf *fnn-trace-state*
        (%make-fnn-trace-state :rows (make-array capacity :initial-element nil)
                              :sample-every sample-every :allocation allocation
                              :rss-every rss-every
                              :rss-fd #+linux (and (plusp rss-every)
                                                   (ignore-errors (values (sb-unix:unix-open "/proc/self/statm" sb-unix:o_rdonly 0))))
                                      #-linux nil)))

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
                        :id id :parent (and (eq state *fnn-trace-parent-state*)
                                            *fnn-trace-parent*)
                        :cid cid :operation operation
                        :connection-generation connection-generation :phase phase
                        :allocation-scope (fnn-trace-state-allocation state))))
              (setf (aref (fnn-trace-state-rows state) (fnn-trace-state-next state)) row)
              (incf (fnn-trace-state-next state))
              row)
          (progn (incf (fnn-trace-state-dropped state)) nil))))))

(defun fnn-trace-finish (state row start bytes outcome)
  ;; Sample before observer locking/formatting; this still includes runtime
  ;; counter overhead and allocations by other threads in the same process.
  (let* ((allocated (and bytes (- (sb-ext:get-bytes-consed) bytes)))
         (duration (- (fnn-trace-now) start))
         (c *fnn-io-counters*)
         (cpu (- (fnn-trace-thread-cpu-us) (fnn-trace-row-cpu row)))
         (gc-us (floor (* (- sb-ext:*gc-run-time* (fnn-trace-row-gc-us row)) 1000000)
                       internal-time-units-per-second))
         (gc-count (max (- (car *fnn-trace-gc-cell*) (fnn-trace-row-gc-count row))
                        (if (eq sb-kernel::*gc-epoch* (fnn-trace-row-gc-epoch row)) 0 1)))
         (read (- (fnn-io-counters-read c) (fnn-trace-row-read row)))
         (write (- (fnn-io-counters-write c) (fnn-trace-row-write row)))
         (syscalls (- (fnn-io-counters-syscalls c) (fnn-trace-row-syscalls row)))
         (every (fnn-trace-state-rss-every state))
         (rss (and (plusp every) (null (fnn-trace-row-parent row))
                   (zerop (mod (sb-ext:atomic-incf (car (fnn-trace-state-rss-ticket state))) every))
                   (fnn-trace-rss-kib state))))
    (sb-thread:with-mutex ((fnn-trace-state-lock state))
      (setf (fnn-trace-row-start row) start
            (fnn-trace-row-duration row) duration
            (fnn-trace-row-bytes row) allocated
            (fnn-trace-row-cpu row) cpu (fnn-trace-row-gc-us row) gc-us
            (fnn-trace-row-gc-count row) gc-count (fnn-trace-row-read row) read
            (fnn-trace-row-write row) write (fnn-trace-row-syscalls row) syscalls
            (fnn-trace-row-gc-epoch row) nil (fnn-trace-row-rss-kib row) rss
            (fnn-trace-row-outcome row) outcome))))

(defmacro fnn-trace-span ((phase &key cid (operation '*fnn-trace-operation*)
                                      (connection-generation '*fnn-trace-connection-generation*)) &body body)
  "Preserve all values and exits; measure one shared span lifetime. Off:
one special-variable test, no identity evaluation, clock read or thunk."
  (let ((state (gensym "STATE")) (row (gensym "ROW"))
        (start (gensym "START")) (bytes (gensym "BYTES")) (ready (gensym "READY"))
        (outcome (gensym "OUTCOME")) (counters (gensym "COUNTERS")))
    `(if *fnn-trace-state*
         (let* ((,state *fnn-trace-state*)
                (,row (ignore-errors (fnn-trace-begin ,state ,phase ,cid ,operation ,connection-generation))))
           (if ,row
               (let* ((,counters (or *fnn-io-counters* (%make-fnn-io-counters)))
                      (*fnn-io-counters* ,counters))
               (multiple-value-bind (,start ,bytes ,ready)
                   (ignore-errors
                     (fnn-trace-mark ,row)
                     (values (fnn-trace-now)
                             (and (fnn-trace-state-allocation ,state) (sb-ext:get-bytes-consed)) t))
                 (if ,ready
                     (let* ((*fnn-trace-parent* (fnn-trace-row-id ,row))
                            (*fnn-trace-parent-state* ,state)
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
                   (progn ,@body))))
             (progn ,@body)))
       (progn ,@body))))

(defun fnn-trace-snapshot (state)
  "Snapshot completed immutable rows and counters under the collector lock.
A row is published once by FINISH; no writer changes a completed interval.
Formatting, sorting and destination I/O must occur after this lock is free."
  (sb-thread:with-mutex ((fnn-trace-state-lock state))
    (let* ((recorded (fnn-trace-state-next state))
           (rows (make-array recorded :initial-element nil)) (incomplete 0))
      (dotimes (i recorded)
        (let ((row (aref (fnn-trace-state-rows state) i)))
          (if (eq (fnn-trace-row-outcome row) :active)
              (incf incomplete)
            (setf (aref rows i) row))))
      (values rows (fnn-trace-state-attempts state) recorded
              (fnn-trace-state-dropped state) incomplete
              (fnn-trace-state-sample-every state)))))

(defun fnn-trace-report (&optional (stream *error-output*))
  "JSON lines from a bounded snapshot. Destination I/O never holds the sink
mutex; no conditions, thread names, addresses or payloads are serialized."
  (let ((state *fnn-trace-state*))
    (when state
      (multiple-value-bind (rows attempts recorded dropped incomplete sample-every)
          (fnn-trace-snapshot state)
        (dotimes (i recorded)
          (let ((row (aref rows i)))
            (when row
              (format stream
                      "~&FN_TRACE {\"v\":2,\"type\":\"span\",\"span_id\":~d,\"parent_id\":~a,\"connection_id\":~a,\"operation_id\":~a,\"connection_generation\":~a,\"phase\":\"~(~a~)\",\"start_us\":~d,\"duration_us\":~d,\"allocated_bytes\":~a,\"allocation_scope\":\"~(~a~)\",\"outcome\":\"~(~a~)\",\"cpu_us\":~d,\"cpu_scope\":\"~(~a~)\",\"gc_us\":~d,\"gc_count\":~d,\"gc_scope\":\"process\",\"read_octets\":~d,\"write_octets\":~d,\"syscalls\":~d,\"io_scope\":\"thread\",\"rss_kib\":~a,\"rss_scope\":\"process\"}~%"
                      (fnn-trace-row-id row) (or (fnn-trace-row-parent row) "null")
                      (or (fnn-trace-row-cid row) "null")
                      (or (fnn-trace-row-operation row) "null")
                      (or (fnn-trace-row-connection-generation row) "null") (fnn-trace-row-phase row)
                      (fnn-trace-row-start row) (fnn-trace-row-duration row)
                      (or (fnn-trace-row-bytes row) "null")
                      (or (fnn-trace-row-allocation-scope row) :disabled)
                      (fnn-trace-row-outcome row)
                      (fnn-trace-row-cpu row) *fnn-trace-cpu-scope*
                      (fnn-trace-row-gc-us row) (fnn-trace-row-gc-count row)
                      (fnn-trace-row-read row) (fnn-trace-row-write row)
                      (fnn-trace-row-syscalls row) (or (fnn-trace-row-rss-kib row) "null")))))
        (format stream "~&FN_TRACE {\"type\":\"summary\",\"attempts\":~d,\"recorded\":~d,\"dropped\":~d,\"incomplete\":~d,\"sample_every\":~d,\"clock_ticks_per_second\":~d}~%"
                attempts recorded dropped incomplete sample-every internal-time-units-per-second)
        (finish-output stream)))))

(defun fnn-trace-hotspots (&optional (stream *error-output*) (limit 10))
  "Rank the existing bounded sink without dumping every chronological row.
Totals are inclusive process/nested observations, never unique allocation or
retained heap. Completed-row snapshot holds only the private trace leaf mutex;
aggregation, sorting and output happen after release. The sink remains available."
  (unless (and (integerp limit) (plusp limit))
    (error "trace hotspot limit must be a positive integer"))
  (let ((state *fnn-trace-state*) (groups (make-hash-table :test 'equal)) (snapshot nil)
        (attempts 0) (recorded 0) (dropped 0) (incomplete 0) (sample-every 1))
    (when state
      (multiple-value-setq (snapshot attempts recorded dropped incomplete sample-every)
        (fnn-trace-snapshot state))
      (dotimes (i recorded)
        (let ((row (aref snapshot i)))
          (when row
            (let* ((key (list (fnn-trace-row-phase row) (fnn-trace-row-allocation-scope row)))
                   ;; samples, duration, allocation samples, bytes, max bytes.
                   (stats (or (gethash key groups)
                              (setf (gethash key groups) (vector 0 0 0 0 0)))))
              (incf (aref stats 0))
              (incf (aref stats 1) (fnn-trace-row-duration row))
              (when (fnn-trace-row-bytes row)
                (incf (aref stats 2))
                (incf (aref stats 3) (fnn-trace-row-bytes row))
                (setf (aref stats 4) (max (aref stats 4) (fnn-trace-row-bytes row))))))))
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

;;; ---------------------------------------------------------------------------
;;; Decision tracing (lane obs-decision-trace; books/decision-trace.lisp).
;;;
;;; A trace is a VIEW over a decision already made.  `fnn-call' (and
;;; `fnn-core-mv') tests the special variable *fnn-dtrace*, NIL unless the
;;; operator turned tracing on; for a name in the traced set it takes a start
;;; time, runs the call, and offers the values it returned to
;;; `fnn-dtrace-note'.  Nothing here is read by a caller: the note's result is
;;; discarded, a failure in it is counted and swallowed, and no decision
;;; branches on whether tracing is on (tools/host_check.py, DT-4).
;;;
;;; The ROW is ACL2's: `fn-dtrace-project' (books/definterface.lisp, generated
;;; from the declarations) turns the traced entry's non-redacted arguments and
;;; its returned values (stobj positions masked to NIL) into (POINT INPUTS
;;; OUTCOME), a bounded record (DT-2).  This file keeps that record in a
;;; preallocated ring row beside the sequence number, the start time, the
;;; duration and the operation identities, and renders it as JSON after the
;;; ring lock is released.  The ring is a leaf mutex held for counter updates
;;; and one row store; no call out, no I/O, no allocation of the row's lists
;;; happens under it.
;;;
;;; Counters: every call the traced set matches ends as exactly one of
;;; RECORDED (a row kept), DROPPED (the ring was full, or the projection
;;; failed) or SAMPLED-OUT (not this call's turn), and is counted an ATTEMPT in
;;; the same lock hold as its end: attempts = recorded + dropped + sampled-out
;;; in every snapshot (DT-5).  A call between its admission and its end is in
;;; none of the four; the sampling cursor (TICKET) is its own counter.
;;;
;;; DRAIN is an acknowledged cursor: `drain SINCE' frees the rows whose
;;; sequence is at most SINCE and returns the live rows after it, so a lost
;;; reply is repeated, not lost.  A full ring drops (counted) and never waits.

(defstruct (fnn-dtrace-point (:constructor %make-fnn-dtrace-point))
  name class positions stobjs-out masked)

(defstruct (fnn-dtrace-row (:constructor %make-fnn-dtrace-row))
  (seq 0) point class (start 0) (duration 0) operation generation inputs outcome)

(defstruct (fnn-dtrace-ring (:constructor %make-fnn-dtrace-ring))
  rows (capacity 0) (tail 0) (count 0) (next-seq 1)
  (ticket 0) (attempts 0) (recorded 0) (dropped 0) (sampled-out 0)
  (sample-every 1) points skew previous
  (lock (sb-thread:make-mutex :name "native-decision-ring")))

(defun fnn-dtrace-enabled-p ()
  "Whether decision tracing is on.  For this file and tools/host_check.py's
DT-4 rule only: no other host code may call it, let alone branch on it."
  (and *fnn-dtrace* t))

(defun fnn-dtrace-make-point (name entry)
  "The traced-set element for NAME from its fn-dtrace-points table ENTRY (a
plist: :class :positions :stobjs-out ...), as ACL2 wrote it."
  (let ((mask (getf entry :stobjs-out)))
    (%make-fnn-dtrace-point :name name :class (getf entry :class)
                            :positions (getf entry :positions)
                            :stobjs-out mask :masked (and (some #'identity mask) t))))

(defun fnn-dtrace-point-set (entries classes)
  "ENTRIES is the table-alist ((NAME . PLIST) ...); the set holds the entries
whose class is in CLASSES."
  (let ((set (make-hash-table :test 'eq)))
    (dolist (entry entries set)
      (when (member (getf (cdr entry) :class) classes)
        (setf (gethash (car entry) set) (fnn-dtrace-make-point (car entry) (cdr entry)))))))

(defun fnn-dtrace-start (entries &key (classes '(:verdict :refusal :tariff :schedule :plan))
                                      (capacity 1024) (sample-every 1) skew)
  "Allocate the ring and turn decision tracing on.  The caller has an
ACL2-admitted plan (fn-dtrace-admit); a malformed one is a defect."
  (unless (and (integerp capacity) (plusp capacity) (integerp sample-every) (plusp sample-every))
    (error "invalid decision trace configuration"))
  (let ((rows (make-array capacity)))
    (dotimes (i capacity) (setf (svref rows i) (%make-fnn-dtrace-row)))
    (setf *fnn-dtrace*
          (%make-fnn-dtrace-ring :rows rows :capacity capacity :sample-every sample-every
                                 :points (fnn-dtrace-point-set entries classes) :skew skew))))

(defun fnn-dtrace-stop ()
  "Turn decision tracing off and release the ring."
  (setf *fnn-dtrace* nil))

(declaim (inline fnn-dtrace-lookup))
(defun fnn-dtrace-lookup (name)
  "The traced-set element for NAME, or NIL.  Called only after *fnn-dtrace*
tested non-NIL."
  (let ((ring *fnn-dtrace*))
    (and ring (values (gethash name (fnn-dtrace-ring-points ring))))))

(defun fnn-dtrace-count-dropped (ring)
  (sb-thread:with-mutex ((fnn-dtrace-ring-lock ring))
    (incf (fnn-dtrace-ring-attempts ring))
    (incf (fnn-dtrace-ring-dropped ring))))

(defun fnn-dtrace-admit-attempt (ring)
  "Say what becomes of one matching call: :record (the caller settles it),
or :sampled-out or :dropped (full ring), which settle here."
  (sb-thread:with-mutex ((fnn-dtrace-ring-lock ring))
    (let ((n (incf (fnn-dtrace-ring-ticket ring))))
      (cond ((not (zerop (mod (1- n) (fnn-dtrace-ring-sample-every ring))))
             (incf (fnn-dtrace-ring-attempts ring))
             (incf (fnn-dtrace-ring-sampled-out ring))
             :sampled-out)
            ((<= (fnn-dtrace-ring-capacity ring) (fnn-dtrace-ring-count ring))
             (incf (fnn-dtrace-ring-attempts ring))
             (incf (fnn-dtrace-ring-dropped ring))
             :dropped)
            (t :record)))))

(defun fnn-dtrace-store (ring point start duration operation generation record)
  "Keep RECORD, ACL2's (POINT INPUTS OUTCOME), in the next ring row; counted
dropped when the ring filled while the record was made."
  (sb-thread:with-mutex ((fnn-dtrace-ring-lock ring))
    (incf (fnn-dtrace-ring-attempts ring))
    (if (<= (fnn-dtrace-ring-capacity ring) (fnn-dtrace-ring-count ring))
        (incf (fnn-dtrace-ring-dropped ring))
      (let ((row (svref (fnn-dtrace-ring-rows ring)
                        (mod (+ (fnn-dtrace-ring-tail ring) (fnn-dtrace-ring-count ring))
                             (fnn-dtrace-ring-capacity ring)))))
        (setf (fnn-dtrace-row-seq row) (fnn-dtrace-ring-next-seq ring)
              (fnn-dtrace-row-point row) (first record)
              (fnn-dtrace-row-class row) (fnn-dtrace-point-class point)
              (fnn-dtrace-row-start row) start
              (fnn-dtrace-row-duration row) duration
              (fnn-dtrace-row-operation row) operation
              (fnn-dtrace-row-generation row) generation
              (fnn-dtrace-row-inputs row) (second record)
              (fnn-dtrace-row-outcome row) (third record))
        (incf (fnn-dtrace-ring-next-seq ring))
        (incf (fnn-dtrace-ring-count ring))
        (incf (fnn-dtrace-ring-recorded ring))))))

(defun fnn-dtrace-masked-values (point values)
  "VALUES with every stobj position NIL (the table's :stobjs-out)."
  (if (fnn-dtrace-point-masked point)
      (loop for v in values
            for m in (append (fnn-dtrace-point-stobjs-out point) (make-list (length values)))
            collect (if m nil v))
    values))

(defun fnn-dtrace-note (point name args values start)
  "Offer one traced call's return to the ring.  Never signals, never blocks
on anything but the leaf lock, and its result is meaningless to the caller."
  (declare (ignore name))
  (let ((ring *fnn-dtrace*))
    (when ring
      (handler-case
          (let ((verdict (fnn-dtrace-admit-attempt ring)))
            (when (eq verdict :record)
              (let* ((seen (fnn-dtrace-masked-values point values))
                     ;; the mutation witness FN_NATIVE_TEST_TRACE_SKEW: the
                     ;; row takes the previous call's outcome
                     (seen (if (fnn-dtrace-ring-skew ring)
                               (prog1 (or (fnn-dtrace-ring-previous ring) seen)
                                 (setf (fnn-dtrace-ring-previous ring) seen))
                             seen))
                     (picked (loop for p in (fnn-dtrace-point-positions point) collect (nth p args)))
                     (record (first (fnn-call 'fn-dtrace-project (fnn-dtrace-point-name point)
                                              picked seen)))
                     (duration (max 0 (- (fnn-trace-now) start))))
                (fnn-dtrace-store ring point start duration
                                  *fnn-trace-operation* *fnn-trace-connection-generation*
                                  record))))
        (serious-condition () (ignore-errors (fnn-dtrace-count-dropped ring)))))))

;;; The call sites (macros, so host/native/io.lisp holds no trace branch).  Off:
;;; one special-variable test.  On: a hash lookup of NAME; only a traced name
;;; reads the clock.
(defmacro fnn-dtrace-around ((name args) &body body)
  "Run BODY (which returns the list of the call's values) and offer it to the
ring when NAME is traced.  The values are returned unchanged."
  (let ((point (gensym "POINT")) (start (gensym "START")) (values (gensym "VALUES")))
    `(let* ((,point (and *fnn-dtrace* (fnn-dtrace-lookup ,name)))
            (,start (if ,point (fnn-trace-now) 0))
            (,values (progn ,@body)))
       (when ,point (fnn-dtrace-note ,point ,name ,args ,values ,start))
       ,values)))

(defun fnn-dtrace-around-mv-traced (name thunk)
  "Run THUNK (a fixed callback, returning its scalar MVs) and offer the values
it returned to the ring.  A fixed callback has no argument list here, so it can
record its outcome only: its declared inputs are all :redact.  The values are
returned unchanged."
  (let ((point (fnn-dtrace-lookup name)))
    (if point
        (let* ((start (fnn-trace-now))
               (vals (multiple-value-list (funcall thunk))))
          (fnn-dtrace-note point name nil vals start)
          (values-list vals))
      (funcall thunk))))

(defmacro fnn-dtrace-around-mv (name body)
  "BODY (a fixed callback's scalar-MV form) with its values offered to the ring
when NAME is traced.  Off: BODY inline after one special-variable test -- no
closure and no funcall.  On: the same BODY in a closure."
  `(if *fnn-dtrace*
       (fnn-dtrace-around-mv-traced ,name (lambda () ,body))
     ,body))

(defun fnn-dtrace-snapshot (ring since limit)
  "Under the ring lock: free the rows at most SINCE, copy the next LIMIT live
rows and the counters.  Everything that formats runs after this returns."
  (sb-thread:with-mutex ((fnn-dtrace-ring-lock ring))
    (loop while (and (plusp (fnn-dtrace-ring-count ring))
                     (<= (fnn-dtrace-row-seq (svref (fnn-dtrace-ring-rows ring)
                                                    (fnn-dtrace-ring-tail ring)))
                         since))
          do (let ((row (svref (fnn-dtrace-ring-rows ring) (fnn-dtrace-ring-tail ring))))
               (setf (fnn-dtrace-row-inputs row) nil (fnn-dtrace-row-outcome row) nil))
             (setf (fnn-dtrace-ring-tail ring)
                   (mod (1+ (fnn-dtrace-ring-tail ring)) (fnn-dtrace-ring-capacity ring)))
             (decf (fnn-dtrace-ring-count ring)))
    (let* ((n (min limit (fnn-dtrace-ring-count ring)))
           (rows (make-array n)))
      (dotimes (i n)
        (setf (svref rows i)
              (copy-fnn-dtrace-row
               (svref (fnn-dtrace-ring-rows ring)
                      (mod (+ (fnn-dtrace-ring-tail ring) i) (fnn-dtrace-ring-capacity ring))))))
      (values rows
              (fnn-dtrace-ring-attempts ring) (fnn-dtrace-ring-recorded ring)
              (fnn-dtrace-ring-dropped ring) (fnn-dtrace-ring-sampled-out ring)
              (fnn-dtrace-ring-count ring) (fnn-dtrace-ring-next-seq ring)))))

(defun fnn-dtrace-json-string (text stream)
  (write-char #\" stream)
  (loop for c across text
        do (cond ((char= c #\") (write-string "\\\"" stream))
                 ((char= c #\\) (write-string "\\\\" stream))
                 ((< (char-code c) 32) (format stream "\\u~4,'0x" (char-code c)))
                 (t (write-char c stream))))
  (write-char #\" stream))

(defun fnn-dtrace-render-record (x stream)
  "ACL2's record as JSON: a natural, a symbol's lowercase name as a string,
NIL and a list as an array.  A rendering of a value ACL2 produced."
  (cond ((null x) (write-string "[]" stream))
        ((integerp x) (format stream "~d" x))
        ((symbolp x) (fnn-dtrace-json-string (string-downcase (symbol-name x)) stream))
        ((consp x)
         (write-char #\[ stream)
         (loop for tail = x then (cdr tail) for first = t then nil
               while (consp tail)
               do (unless first (write-char #\, stream))
                  (fnn-dtrace-render-record (car tail) stream))
         (write-char #\] stream))
        (t (write-string "null" stream))))

(defun fnn-dtrace-render-row (row stream)
  (format stream "FN_TRACE {\"v\":2,\"type\":\"decision\",\"seq\":~d,\"class\":" (fnn-dtrace-row-seq row))
  (fnn-dtrace-json-string (string-downcase (symbol-name (fnn-dtrace-row-class row))) stream)
  (write-string ",\"point\":" stream)
  (fnn-dtrace-json-string (string-downcase (symbol-name (fnn-dtrace-row-point row))) stream)
  (format stream ",\"operation\":~a,\"connection_generation\":~a,\"start_us\":~d,\"duration_us\":~d,\"inputs\":"
          (or (fnn-dtrace-row-operation row) "null") (or (fnn-dtrace-row-generation row) "null")
          (fnn-dtrace-row-start row) (fnn-dtrace-row-duration row))
  (fnn-dtrace-render-record (fnn-dtrace-row-inputs row) stream)
  (write-string ",\"outcome\":" stream)
  (fnn-dtrace-render-record (fnn-dtrace-row-outcome row) stream)
  (format stream "}~%"))

(defun fnn-dtrace-render (rows attempts recorded dropped sampled-out live next stream)
  "The FN_TRACE lines of a snapshot: one decision line per row, then the
counters.  The identity attempts = recorded + dropped + sampled-out holds of
the numbers a snapshot returns together."
  (loop for row across rows do (fnn-dtrace-render-row row stream))
  (format stream "FN_TRACE {\"v\":2,\"type\":\"decision-summary\",\"attempts\":~d,\"recorded\":~d,\"dropped\":~d,\"sampled_out\":~d,\"live\":~d,\"next\":~d}~%"
          attempts recorded dropped sampled-out live next))

(defun fnn-dtrace-drain (since limit)
  "The decision lines after SINCE as a string (NIL when tracing is off)."
  (let ((ring *fnn-dtrace*))
    (when ring
      (multiple-value-bind (rows attempts recorded dropped sampled-out live next)
          (fnn-dtrace-snapshot ring since limit)
        (with-output-to-string (out)
          (fnn-dtrace-render rows attempts recorded dropped sampled-out live next out))))))

(defun fnn-dtrace-report (&optional (stream *error-output*))
  "At stop, the decision rows still in the ring, in the drain's format (the
span report's companion: tools/native_trace.py reads both)."
  (let ((text (fnn-dtrace-drain 0 (let ((ring *fnn-dtrace*))
                                    (if ring (fnn-dtrace-ring-capacity ring) 0)))))
    (when text
      (write-string text stream)
      (finish-output stream))))

;;; ---------------------------------------------------------------------------
;;; The operator's switch: `fn operator CONFIG trace on|off|drain'.
;;;
;;; ACL2 decides everything that is a decision (books/decision-trace.lisp):
;;; the PLAN from the profile's [trace] table at start (fn-dtrace-config-plan;
;;; a refused table stops the start by name), and what a verb does given the
;;; plan and whether tracing is on now (fn-dtrace-verb).  The host reads the
;;; plan's fields, applies the action, and renders rows.  The request is
;;; FNCT kind 26, the reply kind 27, sealed by ACL2; the kind is :read.

(defvar *fnn-trace-plan* nil
  "ACL2's admitted plan for this run: (:off) without a [trace] table, else
(:plan ...).  NIL before `run' decides it.")

(defun fnn-trace-turn-on (plan)
  "Start the span state and the decision ring from PLAN's fields (read through
ACL2's accessors); both are freed together by `fnn-trace-reset'."
  (let ((classes (fnn-core 'fn-dtrace-plan-classes plan))
        (capacity (fnn-core 'fn-dtrace-plan-capacity plan))
        (every (fnn-core 'fn-dtrace-plan-sample-every plan))
        (allocation (fnn-core 'fn-dtrace-plan-allocation plan))
        (rss-every (fnn-core 'fn-dtrace-plan-rss-every plan)))
    ;; Labelled developer mutation witness (DT-3): an enabled trace that
    ;; consumes an entropy draw changes every octet that follows the draw.
    (when (fnn-developer-selector "FN_NATIVE_TEST_TRACE_PERTURB")
      (fnn-csprng-octets 1 "trace perturbation"))
    (fnn-trace-start :capacity capacity :sample-every every :allocation allocation
                     :rss-every rss-every)
    (fnn-dtrace-start (fnn-core 'fn-dtrace-point-table)
                      :classes classes :capacity capacity :sample-every every
                      ;; Labelled developer mutation witness (DT-1h): each row
                      ;; takes the previous traced call's outcome.
                      :skew (and (fnn-developer-selector "FN_NATIVE_TEST_TRACE_SKEW") t))))

(defun fnn-heap-config-trace-ring-octets (config-octets)
  "The ring octets ACL2's plan of CONFIG-OCTETS' [trace] table commits (0 for
none, and for a table the start will refuse by name)."
  (if config-octets
      (fnn-core 'fn-dtrace-config-ring-octets (fnn-octet-list config-octets)
                (if (fnn-developer-image-p) :developer :production))
    0))

(defvar *fnn-heap-trace-ring-octets* 0
  "The decision trace ring's octets, ACL2's (fn-dtrace-ring-octets of the
admitted [trace] plan): 0 without a [trace] table, which is the default.  Set by
the launcher probe from the configuration it reads (fnn-heap-operator-profile),
by `run' when it decides the plan (host/native/trace.lisp), and read by the
reservation extension below.")


(defun fnn-trace-decide-plan (config-octets)
  "At `run': ACL2's plan of the profile's [trace] table.  A refusal stops the
start by name; a plan that starts on starts the ring before anything listens."
  (let* ((plan (fnn-core 'fn-dtrace-config-plan
                         (and config-octets (fnn-octet-list config-octets))
                         (if (fnn-developer-image-p) :developer :production)))
         (kind (fnn-core 'fn-dtrace-plan-kind plan)))
    (when (eq kind :refused)
      (fnn-refuse "the [trace] table is refused: ~(~a~)" (fnn-core 'fn-dtrace-plan-refusal plan)))
    (setq *fnn-trace-plan* plan
          *fnn-heap-trace-ring-octets* (fnn-core 'fn-dtrace-ring-octets plan))
    (when (and (eq kind :plan) (fnn-core 'fn-dtrace-plan-start-p plan))
      (fnn-trace-turn-on plan))
    plan))

(defun fnn-trace-control-answer (verb since)
  "The sealed kind-27 reply to one trace request: ACL2's decision, applied."
  (let* ((decision (fnn-core 'fn-dtrace-verb verb *fnn-trace-plan* (fnn-dtrace-enabled-p)))
         (action (first decision)))
    (flet ((reply (status reason lines)
             (let ((octets (fnn-core 'fn-dtrace-reply-encode status reason lines)))
               (unless (fnn-octet-list-p octets)
                 (fnn-fault "ACL2 refused a trace reply"))
               octets)))
      (case action
        (:enable (fnn-trace-turn-on *fnn-trace-plan*)
         (reply :accepted nil (fnn-core 'fn-dtrace-status-line :on)))
        (:disable (fnn-trace-reset)
         (reply :accepted nil (fnn-core 'fn-dtrace-status-line :off)))
        (:drain
         ;; Rendering happens here, after the ring lock is released; the rows
         ;; pass through one octet list of at most (drain-limit) rows, an
         ;; operator action, not the served path.
         (let ((text (fnn-dtrace-drain since (fnn-core 'fn-dtrace-drain-limit))))
           (reply :accepted nil
                  (if text
                      (fnn-octet-list (fnn-string-octets text))
                    (fnn-core 'fn-dtrace-status-line :off)))))
        (t (multiple-value-bind (status reason)
               (values-list (fnn-core 'fn-dtrace-verb-status decision))
             (reply status reason (fnn-core 'fn-dtrace-status-line :refused))))))))

(defun fnn-trace-execute (result)
  "Execute an accepted `trace' plan over the control socket and print the
owner's lines."
  (let* ((control (fnn-core 'fn-native-operator-host-result-trace-control-path-octets result))
         (plan (fnn-core 'fn-native-operator-host-result-trace-plan result))
         (path (and (fnn-octet-list-p control) (consp control)
                    (fnn-octets-string (fnn-octets control)))))
    (handler-case
        (if (or (null path) (null plan))
            (progn (fnn-operator-emit-status :refused "trace"
                                             "the configuration names no control socket")
                   +fnn-exit-refused+)
          (multiple-value-bind (frame stage)
              (fnn-control-exchange path (fnn-core 'fn-dtrace-request-encode
                                                   (first plan) (second plan)))
            (let ((read (and frame (fnn-core 'fn-dtrace-reply-read (fnn-octet-list frame)))))
              (if (not (consp read))
                  (let* ((status (fnn-control-transport-outcome stage))
                         (code (fnn-core 'fn-native-control-host-status-exit-code status)))
                    (fnn-operator-emit-status (fnn-operator-status-of-exit-code code) "trace")
                    code)
                (destructuring-bind (status word lines) read
                  (when (and (fnn-octet-list-p lines) (consp lines))
                    (let ((text (fnn-octets-string (fnn-octets lines))))
                      (fnn-out "~a" text)
                      (unless (and (plusp (length text))
                                   (char= (char text (1- (length text))) #\Newline))
                        (fnn-out "~%"))))
                  (let ((code (fnn-core 'fn-native-control-host-status-exit-code status)))
                    (fnn-operator-emit-status
                     (fnn-operator-status-of-exit-code code) "trace"
                     (let ((detail (and (fnn-octet-list-p word)
                                        (fnn-core 'fn-native-control-host-reply-detail
                                                  status word))))
                       (and (fnn-octet-list-p detail) (consp detail)
                            (fnn-octets-string (fnn-octets detail)))))
                    code))))))
      (error (condition)
        (let ((code (fnn-exit-code-for condition)))
          (fnn-operator-emit-status (fnn-operator-status-of-exit-code code) "trace" condition)
          code)))))
