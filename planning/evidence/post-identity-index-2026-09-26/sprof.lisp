; post-identity-index: a CPU window for a developer core (no profiling twin).
; Loaded before acl2::sbcl-restart by the wrapper launcher postmeasure.py
; writes.  When FN_SPROF_DIR is set, a thread waits for DIR/start, samples
; every thread with sb-sprof :cpu at 1 ms until DIR/stop, writes DIR/flat.txt
; and DIR/graph.txt, then DIR/done; errors go to DIR/error.txt.
(require :sb-sprof)
(defvar cl-user::*pim-dir* (sb-ext:posix-getenv "FN_SPROF_DIR"))
(defun cl-user::pim-thread (dir)
  (flet ((f (n) (concatenate 'string dir "/" n)))
    (handler-case
        (progn
          (loop until (probe-file (f "start")) do (sleep 0.05))
          (sb-sprof:start-profiling :max-samples 1000000 :mode :cpu
                                    :sample-interval 0.001 :threads :all)
          (loop until (probe-file (f "stop")) do (sleep 0.05))
          (sb-sprof:stop-profiling)
          (with-open-file (s (f "flat.txt") :direction :output :if-exists :supersede)
            (sb-sprof:report :type :flat :stream s :max 200))
          (with-open-file (s (f "graph.txt") :direction :output :if-exists :supersede)
            (sb-sprof:report :type :graph :stream s)))
      (serious-condition (c)
        (with-open-file (s (f "error.txt") :direction :output :if-exists :supersede)
          (format s "~a~%" c))))
    (with-open-file (s (f "done") :direction :output :if-exists :supersede)
      (print :done s))))
(when cl-user::*pim-dir*
  (sb-thread:make-thread (lambda () (cl-user::pim-thread cl-user::*pim-dir*))
                         :name "fn-prof"))
