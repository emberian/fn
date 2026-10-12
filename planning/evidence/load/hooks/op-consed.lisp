;;; Process-wide counters only: no encapsulation or GC policy change.
;;; FN_LOAD_CONSED_DIR contains start/ready/stop/consed.txt/done.
(in-package "ACL2")
(let ((dir (sb-ext:posix-getenv "FN_LOAD_CONSED_DIR")))
  (when dir
    (let ((gcs 0))
      (push (lambda () (incf gcs)) sb-ext:*after-gc-hooks*)
      (sb-thread:make-thread
       (lambda ()
         (flet ((path (name) (format nil "~a/~a" dir name))
                (mark (name)
                  (with-open-file (s (format nil "~a/~a" dir name)
                                     :direction :output :if-exists :supersede)
                    (write-line "ready" s))))
           (loop until (probe-file (path "start")) do (sleep 0.02))
           (let ((bytes (sb-ext:get-bytes-consed))
                 (gc-time sb-ext:*gc-run-time*)
                 (gc-count gcs))
             (mark "ready")
             (loop until (probe-file (path "stop")) do (sleep 0.02))
             ;; Snapshot before formatting/report allocation.
             (let ((delta (- (sb-ext:get-bytes-consed) bytes))
                   (gc-delta (- sb-ext:*gc-run-time* gc-time))
                   (count-delta (- gcs gc-count)))
               (with-open-file (s (path "consed.txt") :direction :output :if-exists :supersede)
                 (format s "consed_bytes ~d gc_ms ~f gcs ~d~%" delta
                         (* 1000.0 (/ gc-delta internal-time-units-per-second)) count-delta)))
             (mark "done"))))
       :name "fn-load-consed"))))
