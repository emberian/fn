;;; Measurement hook for tools/load peers.py (W6 mechanism runs): the W13 GC log hook, then
;;; sb-sprof CPU sampling of every thread, one flat report per window.  No image change.
;;;   FN_LOAD_PROF=<path-prefix>   reports go to <prefix>.NNN.txt, NNN = window index from process start
;;;   FN_LOAD_PROF_WINDOW=<s>      window length in seconds (default 120)
;;;   FN_LOAD_PROF_MODE=cpu|alloc  sb-sprof mode (default cpu)
;;;   FN_LOAD_PROF_START=<path>    optional trigger file: wait for it, then sample ONE
;;;                              window (W2P creates it after the R16 warmup).
;;;   FN_LOAD_PROF_GRAPH=1        also emit .NNN.graph.txt (:max 40)
;;;   FN_LOAD_PROF_INTERVAL=0.001 optional sample interval; with a trigger,
;;;                              acknowledge ready, stop on sibling stop, emit done.
;;;                              Without it the existing timed windows are unchanged.
(in-package "ACL2")
(load (merge-pathnames "profile-support.lisp" *load-truename*))
(load (merge-pathnames "w13-idle-gc.lisp" (or *load-truename* *default-pathname-defaults*)))
(let ((out (sb-ext:posix-getenv "FN_LOAD_PROF")))
  (when (and out (plusp (length out)))
    (require :sb-sprof)
    (let ((win (parse-integer (or (sb-ext:posix-getenv "FN_LOAD_PROF_WINDOW") "120")))
          (trigger (sb-ext:posix-getenv "FN_LOAD_PROF_START"))
          (interval (sb-ext:posix-getenv "FN_LOAD_PROF_INTERVAL"))
          (graph (equal (sb-ext:posix-getenv "FN_LOAD_PROF_GRAPH") "1"))
          (mode (if (equal (sb-ext:posix-getenv "FN_LOAD_PROF_MODE") "alloc") :alloc :cpu)))
      (sb-thread:make-thread
       (lambda ()
         (when trigger (loop until (probe-file trigger) do (sleep 0.05)))
         (loop for k from 0
               do (funcall (intern "START-PROFILING" "SB-SPROF")
                           :max-samples 400000 :mode mode
                           :sample-interval (if interval
                                                ;; Parse a decimal without invoking the Lisp reader.
                                                (let* ((dot (position #\. interval))
                                                       (digits (remove #\. interval)))
                                                  (float (/ (parse-integer digits)
                                                            (expt 10 (if dot (- (length interval) dot 1) 0)))
                                                         1.0))
                                                0.01)
                           ;; A snapshot thread list excluding this controller
                           ;; would omit threads born later, notably per-batch
                           ;; syncers. Keep :all and export self samples by thread
                           ;; for parser subtraction when INTERVAL is supplied.
                           ;; Unset new keys preserve existing reports/behaviour.
                           :threads :all)
                  (if (and trigger interval)
                      (progn
                        (with-open-file (s (merge-pathnames "ready" trigger)
                                           :direction :output :if-exists :supersede)
                          (write-line "ready" s))
                        (loop with deadline = (+ (get-internal-real-time)
                                                 (* win internal-time-units-per-second))
                              until (or (probe-file (merge-pathnames "stop" trigger))
                                        (>= (get-internal-real-time) deadline))
                              do (sleep 0.001)))
                      (sleep win))
                  (funcall (intern "STOP-PROFILING" "SB-SPROF"))
                  (with-open-file (s (format nil "~a.~3,'0d.txt" out k)
                                     :direction :output :if-exists :supersede)
                    (let ((*standard-output* s))
                      (funcall (intern "REPORT" "SB-SPROF") :type :flat :max 60)))
                  (when interval
                    (handler-case
                        (fn-load-thread-samples (format nil "~a.~3,'0d.threads.jsonl" out k))
                      (error (e)
                        (with-open-file (s (format nil "~a.~3,'0d.threads.error.txt" out k)
                                           :direction :output :if-exists :supersede)
                          (format s "~a~%" e)))))
                  (when graph
                    (with-open-file (s (format nil "~a.~3,'0d.graph.txt" out k)
                                       :direction :output :if-exists :supersede)
                      (let ((*standard-output* s))
                        (funcall (intern "REPORT" "SB-SPROF") :type :graph :max 40))))
                  (funcall (intern "RESET" "SB-SPROF"))
                  (when (and trigger interval)
                    (with-open-file (s (merge-pathnames "done" trigger)
                                       :direction :output :if-exists :supersede)
                      (write-line "done" s)))
                  (when trigger (return))))
       :name "fn-load-prof"))))
