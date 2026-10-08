;;; Measurement hook for tools/load peers.py (W6 mechanism runs): the W13 GC log hook, then
;;; sb-sprof CPU sampling of every thread, one flat report per window.  No image change.
;;;   FN_LOAD_PROF=<path-prefix>   reports go to <prefix>.NNN.txt, NNN = window index from process start
;;;   FN_LOAD_PROF_WINDOW=<s>      window length in seconds (default 120)
(in-package "ACL2")
(load (merge-pathnames "w13-idle-gc.lisp" (or *load-truename* *default-pathname-defaults*)))
(let ((out (sb-ext:posix-getenv "FN_LOAD_PROF")))
  (when (and out (plusp (length out)))
    (require :sb-sprof)
    (let ((win (parse-integer (or (sb-ext:posix-getenv "FN_LOAD_PROF_WINDOW") "120"))))
      (funcall (intern "START-PROFILING" "SB-SPROF")
               :max-samples 400000 :mode :cpu :sample-interval 0.01 :threads :all)
      (sb-thread:make-thread
       (lambda ()
         (loop for k from 0
               do (sleep win)
                  (with-open-file (s (format nil "~a.~3,'0d.txt" out k)
                                     :direction :output :if-exists :supersede)
                    (let ((*standard-output* s))
                      (funcall (intern "REPORT" "SB-SPROF") :type :flat :max 40)))
                  (funcall (intern "STOP-PROFILING" "SB-SPROF"))
                  (funcall (intern "RESET" "SB-SPROF"))
                  (funcall (intern "START-PROFILING" "SB-SPROF")
                           :max-samples 400000 :mode :cpu :sample-interval 0.01 :threads :all)))
       :name "fn-load-prof"))))
