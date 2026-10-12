;;; Process-wide counters only: no encapsulation or GC policy change.
;;; Prepare paths/encodings/ready stream before the baseline. Publish its byte
;;; with a nonallocating write afterwards, so readiness cannot race the baseline.
(in-package "ACL2")
(load (merge-pathnames "profile-support.lisp" *load-truename*))
(let ((dir (sb-ext:posix-getenv "FN_LOAD_CONSED_DIR")))
  (when dir
    (let* ((start (fn-load-trigger-name (format nil "~a/start" dir)))
           (stop (fn-load-trigger-name (format nil "~a/stop" dir)))
           (ready-path (format nil "~a/ready" dir))
           (out (format nil "~a/consed.txt" dir))
           (done (format nil "~a/done" dir))
           (ready (open ready-path :direction :output :if-exists :supersede))
           (ready-fd (sb-sys:fd-stream-fd ready))
           (ready-byte (make-array 1 :element-type '(unsigned-byte 8) :initial-element 49))
           (gcs 0))
      (push (lambda () (incf gcs)) sb-ext:*after-gc-hooks*)
      (sb-thread:make-thread
       (lambda ()
         (unwind-protect
             (progn
               (loop until (fn-load-trigger-present-p start) do (sleep 0.02))
               ;; All initialization precedes this final baseline. Polling
               ;; creates no Lisp objects; the idle control measures residuals.
               (let ((gc-time sb-ext:*gc-run-time*) (gc-count gcs)
                     (ticks (get-internal-real-time))
                     (bytes (sb-ext:get-bytes-consed)))
                 (sb-sys:with-pinned-objects (ready-byte)
                   (sb-unix:unix-write ready-fd (sb-sys:vector-sap ready-byte) 0 1))
                 (loop until (fn-load-trigger-present-p stop) do (sleep 0.02))
                 ;; Snapshot every raw counter before any arithmetic: even
                 ;; conversion of ticks to milliseconds can allocate a ratio.
                 (let ((end-bytes (sb-ext:get-bytes-consed))
                       (end-gc-time sb-ext:*gc-run-time*)
                       (end-gc-count gcs)
                       (end-ticks (get-internal-real-time)))
                   (let ((delta (- end-bytes bytes))
                         (gc-delta (- end-gc-time gc-time))
                         (count-delta (- end-gc-count gc-count))
                         (window-ms (* 1000.0 (/ (- end-ticks ticks)
                                                internal-time-units-per-second))))
                     (with-open-file (s out :direction :output :if-exists :supersede)
                       (format s "consed_bytes ~d gc_ms ~,6f gcs ~d window_ms ~,6f~%" delta
                               (* 1000.0 (/ gc-delta internal-time-units-per-second)) count-delta window-ms))))
                 (with-open-file (s done :direction :output :if-exists :supersede)
                   (write-line "done" s))))
           (close ready)))
       :name "fn-load-consed"))))
