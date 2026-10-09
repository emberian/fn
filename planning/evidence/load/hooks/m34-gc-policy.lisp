;;; Builder M, memory landing 3+4 (2026-10-09): a candidate collector policy, measured before it is built.
;;; The census found fn-core's resident set far above its live heap at rest (W1 at 4,000 records: 245-302 MB
;;; resident against 74 MB live after a full collection; a full collection returned it to 143 MB).  Promoted
;;; garbage in older generations waits for their own triggers.  The policy: after any collection, when the
;;; dynamic usage exceeds RHO-scaled live usage at the last full collection plus twice the trigger in force, one
;;; full collection runs on this hook's own thread.  FN_LOAD_GC_RHO is RHO in percent (default 25).  The hook
;;; only collects.  It prints one line per full collection it ran to FN_LOAD_CENSUS_DIR/gc-policy.log.
(in-package "ACL2")

(defvar *fnl-gcp-live* nil)
(defvar *fnl-gcp-sem* (sb-thread:make-semaphore))
(defvar *fnl-gcp-busy* nil)

(defun fnl-gcp-rho ()
  (let ((s (sb-ext:posix-getenv "FN_LOAD_GC_RHO")))
    (or (and s (parse-integer s :junk-allowed t)) 25)))

(defun fnl-gcp-after-gc ()
  (let ((live *fnl-gcp-live*))
    (when (and live (not *fnl-gcp-busy*)
               (> (sb-kernel:dynamic-usage)
                  (+ live (floor (* live (fnl-gcp-rho)) 100) (* 2 (sb-ext:bytes-consed-between-gcs)))))
      (setq *fnl-gcp-busy* t)
      (sb-thread:signal-semaphore *fnl-gcp-sem*))))

(let ((dir (sb-ext:posix-getenv "FN_LOAD_CENSUS_DIR")))
  (when (and dir (plusp (length dir)))
    (sb-thread:make-thread
     (lambda ()
       (sb-ext:gc :full t)
       (setq *fnl-gcp-live* (sb-kernel:dynamic-usage))
       (push #'fnl-gcp-after-gc sb-ext:*after-gc-hooks*)
       (loop
         (sb-thread:wait-on-semaphore *fnl-gcp-sem*)
         (let ((before (sb-kernel:dynamic-usage)) (t0 (get-internal-real-time)))
           (sb-ext:gc :full t)
           (setq *fnl-gcp-live* (sb-kernel:dynamic-usage))
           (with-open-file (o (concatenate 'string dir "/gc-policy.log") :direction :output
                              :if-exists :append :if-does-not-exist :create)
             (format o "full before ~d live ~d ms ~d~%" before *fnl-gcp-live*
                     (round (* 1000 (- (get-internal-real-time) t0)) internal-time-units-per-second))))
         (setq *fnl-gcp-busy* nil)))
     :name "fn-load-gc-policy")))
