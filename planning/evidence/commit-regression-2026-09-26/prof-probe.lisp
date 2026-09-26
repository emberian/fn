;; Profile `store ROOT probe N` in-process (the commit loop and the reopen),
;; with SBCL's statistical profiler.  PROF_ROOT names an initialised store,
;; PROF_N the commit count, PROF_MODE cpu or alloc.
(require :sb-sprof)
(in-package "ACL2")
(fnn-crypto-startup) (fnn-tls-reset) (fnn-hsig-reset) (fnn-hsig-initialize)
(defvar *root* (sb-ext:posix-getenv "PROF_ROOT"))
(defvar *n* (parse-integer (sb-ext:posix-getenv "PROF_N")))
(defvar *mode* (if (equal (sb-ext:posix-getenv "PROF_MODE") "alloc") :alloc :cpu))
(let ((b0 (sb-ext:get-bytes-consed)) (t0 (get-internal-real-time)))
  (sb-sprof:with-profiling (:max-samples 400000 :mode *mode* :sample-interval 0.005 :report nil)
    (handler-case (fnn-command-probe *root* *n*) (type-error (e) (format t "~&(json output stream unbound: ~a)~%" (type-of e)))))
  (format t "~&PROF n=~d bytes-consed=~d elapsed=~,3f~%" *n* (- (sb-ext:get-bytes-consed) b0)
          (/ (- (get-internal-real-time) t0) (float internal-time-units-per-second))))
(sb-sprof:report :type :flat :max 80 :sort-by :cumulative-samples)
(sb-sprof:report :type :flat :max 30)
(sb-ext:exit :code 0 :abort t)
