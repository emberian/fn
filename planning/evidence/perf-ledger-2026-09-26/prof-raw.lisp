; Scratch-only raw profiling entry (rep-wave-c lane): never committed.
; The developer entry plus: FN_PROF_LOAD (a file loaded before fnn-main, the
; call-count wrappers), FN_SPROF_DIR (a thread that waits for DIR/start, then
; either counts calls (FN_PROF_COUNT set: counts.txt at DIR/stop) or samples
; CPU with sb-sprof (flat.txt, graph.txt at DIR/stop)).  Any error in the
; thread is written to DIR/error.txt; DIR/done is written last.
(in-package "ACL2")
(require :sb-sprof)
(defvar *fnp-counts* (make-hash-table :test 'eq))
(defvar *fnp-active* nil)
(defun fnp-write-counts (path)
  (with-open-file (s path :direction :output :if-exists :supersede)
    (let ((rows nil))
      (maphash (lambda (k v) (push (cons k v) rows)) *fnp-counts*)
      (dolist (r (sort rows #'string< :key (lambda (r) (symbol-name (car r)))))
        (format s "~(~a~) ~d~%" (car r) (cdr r))))))
(defun fnp-thread (dir)
  (flet ((f (n) (concatenate 'string dir "/" n)))
    (handler-case
        (progn
          (loop until (probe-file (f "start")) do (sleep 0.05))
          (if (sb-ext:posix-getenv "FN_PROF_COUNT")
              (progn
                (clrhash *fnp-counts*)
                (setq *fnp-active* t)
                (loop until (probe-file (f "stop")) do (sleep 0.05))
                (setq *fnp-active* nil)
                (fnp-write-counts (f "counts.txt")))
              (progn
                (sb-sprof:start-profiling :max-samples 1000000 :mode :cpu
                                          :sample-interval 0.001 :threads :all)
                (loop until (probe-file (f "stop")) do (sleep 0.05))
                (sb-sprof:stop-profiling)
                (with-open-file (s (f "flat.txt") :direction :output :if-exists :supersede)
                  (sb-sprof:report :type :flat :max 80 :stream s))
                (with-open-file (s (f "graph.txt") :direction :output :if-exists :supersede)
                  (sb-sprof:report :type :graph :max 60 :stream s)))))
      (serious-condition (c)
        (with-open-file (s (f "error.txt") :direction :output :if-exists :supersede)
          (format s "~a~%" c))))
    (with-open-file (s (f "done") :direction :output :if-exists :supersede)
      (print :done s))))
(defun fn-native-entry (st)
  (declare (ignore st))
  (fnn-native-startup (lambda ()
                        (fnn-crypto-startup)
                        (fnn-tls-reset)
                        (fnn-hsig-reset)
                        (fnn-hsig-initialize)))
  (let ((extra (sb-ext:posix-getenv "FN_PROF_LOAD")))
    (when extra (load extra)))
  (let ((dir (sb-ext:posix-getenv "FN_SPROF_DIR")))
    (when dir
      (sb-thread:make-thread (lambda () (fnp-thread dir)) :name "fn-prof")))
  (fnn-main)
  (values nil :exited *the-live-state*))
