;;; Measurement-only PUBPROF hook. Initialize paths, mutex, profiler, exit shim
;;; and observer before the final baselines. Reporting never prevents fnn-exit.
(in-package "ACL2")
(load (merge-pathnames "profile-support.lisp" *load-truename*))
(let ((prefix (sb-ext:posix-getenv "FN_LOAD_EXITPROF")))
  (when (and prefix (plusp (length prefix)))
    (let* ((stop-name (sb-ext:posix-getenv "FN_LOAD_EXITPROF_STOP"))
           (stop (and stop-name (fn-load-trigger-name stop-name)))
           (report-path (concatenate 'string prefix ".txt"))
           (consed-path (concatenate 'string prefix ".consed.txt"))
           (error-path (concatenate 'string prefix ".error.txt"))
           (done-path (concatenate 'string prefix ".done"))
           (interval (or (sb-ext:posix-getenv "FN_LOAD_EXITPROF_INTERVAL") "0.005"))
           (mode (if (equal (sb-ext:posix-getenv "FN_LOAD_EXITPROF_MODE") "alloc") :alloc :cpu))
           (lock (sb-thread:make-mutex :name "fn-load-exitprof"))
           (observer-ready (sb-thread:make-semaphore))
           (reported nil) (initialized nil) (bytes0 0) (gc0 0) (cpu0 0))
      (labels ((write-bytes ()
                 (ignore-errors
                   (with-open-file (s "/proc/self/io")
                     (loop for line = (read-line s nil nil) while line
                           when (and (>= (length line) 12)
                                     (string= "write_bytes:" line :end2 12))
                             return (parse-integer line :start 12)))))
               (report-once ()
                 ;; Guard the ENTIRE path, including mutex/error/done handling.
                 ;; A full disk, reporting error, or failure to create any marker
                 ;; can only lose measurements, never alter the native exit.
                 (ignore-errors
                   (sb-thread:with-mutex (lock)
                     (when (and initialized (not reported))
                       (setf reported t)
                       (handler-case
                           (progn
                             (funcall (intern "STOP-PROFILING" "SB-SPROF"))
                             ;; Sampling is stopped before /proc, formatting, or
                             ;; report I/O. Counters also exclude that report work.
                             (let ((bytes (- (sb-ext:get-bytes-consed) bytes0))
                                   (gc-ms (* 1000.0 (/ (- sb-ext:*gc-run-time* gc0)
                                                       internal-time-units-per-second)))
                                   (cpu-ms (* 1000.0 (/ (- (get-internal-run-time) cpu0)
                                                        internal-time-units-per-second)))
                                   (written (write-bytes)))
                               (with-open-file (s consed-path :direction :output :if-exists :supersede)
                                 (format s "consed_bytes ~d gc_ms ~,6f cpu_ms ~,6f write_bytes ~a~%"
                                         bytes gc-ms cpu-ms (or written "unavailable")))
                               (with-open-file (s report-path :direction :output :if-exists :supersede)
                                 (let ((*standard-output* s))
                                   (write-line "=== flat ===" s)
                                   (funcall (intern "REPORT" "SB-SPROF") :type :flat :max 60)
                                   (write-line "=== graph ===" s)
                                   (funcall (intern "REPORT" "SB-SPROF") :type :graph :max 40)))))
                         (error (e)
                           (ignore-errors
                             (with-open-file (s error-path :direction :output :if-exists :supersede)
                               (format s "~a~%" e)))))
                       (ignore-errors
                         (with-open-file (s done-path :direction :output :if-exists :supersede)
                           (write-line "done" s))))))))
        (require :sb-sprof)
        (push #'report-once sb-ext:*exit-hooks*)
        ;; :abort t bypasses *exit-hooks*. Forward all ORIGINAL exit arguments
        ;; even if reporting unexpectedly unwinds outside its own error handler.
        (when (fboundp 'fnn-exit)
          (sb-int:encapsulate 'fnn-exit 'fn-load-exitprof
                             (lambda (fn &rest args)
                               (unwind-protect (report-once) (apply fn args)))))
        (when stop
          (sb-thread:make-thread
           (lambda ()
             (sb-thread:signal-semaphore observer-ready)
             (loop until initialized do (sleep 0.02))
             (loop until (fn-load-trigger-present-p stop) do (sleep 0.05))
             (report-once))
           :name "fn-load-exitprof-stop")
          (sb-thread:wait-on-semaphore observer-ready))
        (let* ((dot (position #\. interval)) (digits (remove #\. interval))
               (seconds (float (/ (parse-integer digits)
                                  (expt 10 (if dot (- (length interval) dot 1) 0))) 1.0)))
          (unless (plusp seconds) (error "exit-prof sample interval must be positive"))
          (funcall (intern "START-PROFILING" "SB-SPROF")
                   :mode mode :threads :all :sample-interval seconds :max-samples 1000000))
        ;; Last initialization: none of require/setup/encapsulation/thread birth
        ;; is charged to the operation's allocation or GC totals.
        (sb-thread:with-mutex (lock)
          (setf cpu0 (get-internal-run-time) gc0 sb-ext:*gc-run-time*
                bytes0 (sb-ext:get-bytes-consed) initialized t))))))
