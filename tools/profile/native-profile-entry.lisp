;;; A PROFILING variant of the developer image's entry (never a release image).
;;; tools/profile/build_native_profile.sh loads this after host/native/build.lisp's
;;; world is set and before its save-exec.  With FN_PROF_OUT=P set, the process
;;; starts a watcher thread: creating P.start (its first line an optional mode,
;;; cpu or alloc) starts SBCL's statistical profiler over every thread; creating
;;; P.stop stops it and writes P.N.txt: wall seconds, bytes consed (whole process)
;;; and sb-sprof's flat and graph reports.  Without FN_PROF_OUT it is the
;;; ordinary entry.  FN_PROF_HOOK=FILE loads FILE first (phase timers).
;;; Exists to find which work a served quantum does
;;; (lane control-quanta, 2026-09-27).
(require :sb-sprof)

(defvar *fnn-prof-n* 0)

(defun fnn-prof-read-mode (path)
  (let ((line (ignore-errors
               (with-open-file (s path) (read-line s nil "")))))
    (if (and line (search "alloc" line)) :alloc :cpu)))

(defun fnn-prof-watch (out)
  (let ((start (concatenate 'string out ".start"))
        (stop (concatenate 'string out ".stop"))
        (t0 0) (b0 0) (mode :cpu))
    (loop
      (sleep 0.05)
      (when (probe-file start)
        (setq mode (fnn-prof-read-mode start))
        (ignore-errors (delete-file start))
        (sb-sprof:reset)
        (setq b0 (sb-ext:get-bytes-consed)
              t0 (get-internal-real-time))
        (sb-sprof:start-profiling :mode mode :threads :all
                                  :sample-interval 0.002
                                  :alloc-interval 4
                                  :max-samples 2000000))
      (when (probe-file stop)
        (ignore-errors (delete-file stop))
        (sb-sprof:stop-profiling)
        (let ((wall (/ (- (get-internal-real-time) t0)
                       (float internal-time-units-per-second)))
              (consed (- (sb-ext:get-bytes-consed) b0))
              (file (format nil "~a.~d.txt" out (incf *fnn-prof-n*))))
          (with-open-file (s (concatenate 'string file ".tmp")
                             :direction :output :if-exists :supersede)
            (format s "mode ~a wall-s ~,3f bytes-consed ~d~%" mode wall consed)
            (let ((*standard-output* s))
              (sb-sprof:report :type :flat :stream s :max 80)
              (sb-sprof:report :type :graph :stream s :max 60)))
          (rename-file (concatenate 'string file ".tmp") file))))))

(defun fn-native-entry (st)
  (declare (ignore st))
  ;; FN_PROF_HOOK=FILE: a Lisp file loaded before the entry runs (phase
  ;; timers by sb-int:encapsulate; lane snapshot-open).
  (let ((hook (sb-ext:posix-getenv "FN_PROF_HOOK")))
    (when (and hook (plusp (length hook)))
      (load hook)))
  (let ((out (sb-ext:posix-getenv "FN_PROF_OUT")))
    (when (and out (plusp (length out)))
      (sb-thread:make-thread (lambda () (fnn-prof-watch out))
                             :name "fn-prof-watch")))
  (fnn-main)
  (values nil :exited *the-live-state*))
