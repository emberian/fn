;;; Measurement hook for tools/load peers.py (W6 mechanism runs): the W13 GC log hook, then
;;; sb-sprof CPU sampling of every thread, one flat report per window.  No image change.
;;;   FN_LOAD_PROF=<path-prefix>   reports go to <prefix>.NNN.txt, NNN = window index from process start
;;;   FN_LOAD_PROF_WINDOW=<s>      window length in seconds (default 120)
;;;   FN_LOAD_PROF_MODE=cpu|alloc  sb-sprof mode (default cpu)
;;;   FN_LOAD_PROF_START=<path>    optional trigger file: wait for it, then sample ONE
;;;                              window (W2P creates it after the R16 warmup).
(in-package "ACL2")
(load (merge-pathnames "w13-idle-gc.lisp" (or *load-truename* *default-pathname-defaults*)))
(let ((out (sb-ext:posix-getenv "FN_LOAD_PROF")))
  (when (and out (plusp (length out)))
    (require :sb-sprof)
    (let ((win (parse-integer (or (sb-ext:posix-getenv "FN_LOAD_PROF_WINDOW") "120")))
          (trigger (sb-ext:posix-getenv "FN_LOAD_PROF_START"))
          (mode (if (equal (sb-ext:posix-getenv "FN_LOAD_PROF_MODE") "alloc") :alloc :cpu)))
      (sb-thread:make-thread
       (lambda ()
         (when trigger (loop until (probe-file trigger) do (sleep 0.05)))
         (loop for k from 0
               do (funcall (intern "START-PROFILING" "SB-SPROF")
                           :max-samples 400000 :mode mode :sample-interval 0.01 :threads :all)
                  (sleep win)
                  (funcall (intern "STOP-PROFILING" "SB-SPROF"))
                  (with-open-file (s (format nil "~a.~3,'0d.txt" out k)
                                     :direction :output :if-exists :supersede)
                    (let ((*standard-output* s))
                      (funcall (intern "REPORT" "SB-SPROF") :type :flat :max 60)))
                  (funcall (intern "RESET" "SB-SPROF"))
                  (when trigger (return))))
       :name "fn-load-prof"))))
