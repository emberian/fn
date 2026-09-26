; scratch: alloc-mode statistical profile between FN_ALLOC_DIR/start and /stop
(in-package "ACL2")
(require :sb-sprof)
(defvar *fna-dir* (sb-ext:posix-getenv "FN_ALLOC_DIR"))
(when *fna-dir*
  (sb-thread:make-thread
   (lambda ()
     (flet ((f (n) (concatenate 'string *fna-dir* "/" n)))
       (handler-case
           (progn
             (loop until (probe-file (f "start")) do (sleep 0.05))
             (sb-sprof:start-profiling :max-samples 2000000 :mode :alloc :threads :all)
             (loop until (probe-file (f "stop")) do (sleep 0.05))
             (sb-sprof:stop-profiling)
             (with-open-file (s (f "flat.txt") :direction :output :if-exists :supersede)
               (sb-sprof:report :type :flat :max 60 :stream s))
             (with-open-file (s (f "graph.txt") :direction :output :if-exists :supersede)
               (sb-sprof:report :type :graph :max 80 :stream s)))
         (serious-condition (c)
           (with-open-file (s (f "error.txt") :direction :output :if-exists :supersede)
             (format s "~a~%" c))))
       (with-open-file (s (f "done") :direction :output :if-exists :supersede)
         (print :done s))))
   :name "fn-alloc"))
