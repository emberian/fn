;;; Measurement only, loaded into each PUBPROF process, never saved in an image.
;;; FN_LOAD_EXITPROF=<prefix>; MODE=cpu|alloc; INTERVAL decimal seconds (default .005).
;;; STOP names a trigger file. A single report contains flat (:max 60) and graph
;;; (:max 40) sections; .consed.txt snapshots counters BEFORE report allocation.
;;; .done is written after both reports; .error.txt records a reporting failure.
(in-package "ACL2")
(let ((prefix (sb-ext:posix-getenv "FN_LOAD_EXITPROF")))
  (when (and prefix (plusp (length prefix)))
    (let* ((bytes0 (sb-ext:get-bytes-consed))
           (gc0 sb-ext:*gc-run-time*)
           (cpu0 (get-internal-run-time))
           (stop (sb-ext:posix-getenv "FN_LOAD_EXITPROF_STOP"))
           (interval (or (sb-ext:posix-getenv "FN_LOAD_EXITPROF_INTERVAL") "0.005"))
           (mode (if (equal (sb-ext:posix-getenv "FN_LOAD_EXITPROF_MODE") "alloc") :alloc :cpu))
           (lock (sb-thread:make-mutex :name "fn-load-exitprof"))
           (reported nil))
      (labels ((write-bytes ()
                 (handler-case
                     (with-open-file (s "/proc/self/io")
                       (loop for line = (read-line s nil nil) while line
                             when (and (>= (length line) 12)
                                       (string= "write_bytes:" line :end2 12))
                               return (parse-integer line :start 12)))
                   (error () nil)))
               (report-once ()
                 ;; Exit on the main thread waits if the STOP observer is still
                 ;; writing. Claiming the report and all writes share this mutex.
                 (sb-thread:with-mutex (lock)
                   (unless reported
                     (setf reported t)
                     (handler-case
                         (let ((bytes (- (sb-ext:get-bytes-consed) bytes0))
                               (gc-ms (* 1000.0 (/ (- sb-ext:*gc-run-time* gc0)
                                                   internal-time-units-per-second)))
                               (cpu-ms (* 1000.0 (/ (- (get-internal-run-time) cpu0)
                                                    internal-time-units-per-second)))
                               (written (write-bytes)))
                           (funcall (intern "STOP-PROFILING" "SB-SPROF"))
                           (with-open-file (s (concatenate 'string prefix ".consed.txt")
                                              :direction :output :if-exists :supersede)
                             (format s "consed_bytes ~d gc_ms ~,6f cpu_ms ~,6f write_bytes ~a~%"
                                     bytes gc-ms cpu-ms (or written "unavailable")))
                           (with-open-file (s (concatenate 'string prefix ".txt")
                                              :direction :output :if-exists :supersede)
                             (let ((*standard-output* s))
                               (write-line "=== flat ===" s)
                               (funcall (intern "REPORT" "SB-SPROF") :type :flat :max 60)
                               (write-line "=== graph ===" s)
                               (funcall (intern "REPORT" "SB-SPROF") :type :graph :max 40))))
                       (error (e)
                         (with-open-file (s (concatenate 'string prefix ".error.txt")
                                            :direction :output :if-exists :supersede)
                           (format s "~a~%" e))))
                     (with-open-file (s (concatenate 'string prefix ".done")
                                        :direction :output :if-exists :supersede)
                       (write-line "done" s))))))
        (require :sb-sprof)
        (let* ((dot (position #\. interval))
               (digits (remove #\. interval))
               (seconds (float (/ (parse-integer digits)
                                  (expt 10 (if dot (- (length interval) dot 1) 0))) 1.0)))
          (unless (plusp seconds) (error "exit-prof sample interval must be positive"))
          (funcall (intern "START-PROFILING" "SB-SPROF")
                   :mode mode :threads :all :sample-interval seconds :max-samples 1000000))
        (push #'report-once sb-ext:*exit-hooks*)
        ;; fnn-exit uses sb-ext:exit :abort t, which bypasses *exit-hooks*.
        ;; This workload-only wrapper reports before forwarding the SAME exit.
        (when (fboundp 'fnn-exit)
          (sb-int:encapsulate 'fnn-exit 'fn-load-exitprof
                             (lambda (fn &rest args)
                               (report-once)
                               (apply fn args))))
        (when stop
          (sb-thread:make-thread
           (lambda ()
             (loop until (probe-file stop) do (sleep 0.05))
             (report-once))
           :name "fn-load-exitprof-stop"))))))
