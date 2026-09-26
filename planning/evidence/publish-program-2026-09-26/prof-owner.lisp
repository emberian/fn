;; In-process CPU profile of the served owner (`operator CONFIG run`) with
;; SBCL's statistical profiler and NO polling thread: rep-wave-c's profiler
;; (planning/evidence/rep-wave-c-2026-09-25/prof-raw.lisp) looped over
;; probe-file every 50 ms and its own samples were the 79 % in
;; SB-IMPL::QUERY-FILE-SYSTEM that PKT-186 reported.
;;
;; Loaded by the launcher's own sbcl command line before ACL2's restart hands
;; control to fn-native-entry (`--eval '(load "prof-owner.lisp")'` in front
;; of `--eval '(acl2::sbcl-restart)'`).  The report is written when SIGUSR1
;; arrives (the driver sends it at the end of its load, or when it detects a
;; stall) or after PROF_SECONDS, whichever comes first; the process then
;; exits.  The waiting thread blocks on a semaphore: nothing here reads the
;; filesystem until the report is written.
(require :sb-sprof)
(defvar cl-user::*fnp-out* (sb-ext:posix-getenv "PROF_OUT"))
(defvar cl-user::*fnp-seconds*
  (parse-integer (or (sb-ext:posix-getenv "PROF_SECONDS") "900")))
(defvar cl-user::*fnp-sem* (sb-thread:make-semaphore :name "fn-prof-report"))
(defun cl-user::fnp-report ()
  (sb-sprof:stop-profiling)
  (with-open-file (s cl-user::*fnp-out* :direction :output :if-exists :supersede)
    (format s "PROF mode=cpu interval=0.002 seconds-cap=~d~%" cl-user::*fnp-seconds*)
    (sb-sprof:report :type :flat :max 80 :stream s)
    (sb-sprof:report :type :graph :max 60 :stream s))
  (sb-ext:exit :code 0 :abort t))
(sb-sys:enable-interrupt sb-unix:sigusr1
                         (lambda (signal info context)
                           (declare (ignore signal info context))
                           (sb-thread:signal-semaphore cl-user::*fnp-sem*)))
(sb-thread:make-thread
 (lambda ()
   (sb-thread:wait-on-semaphore cl-user::*fnp-sem* :timeout cl-user::*fnp-seconds*)
   (cl-user::fnp-report))
 :name "fn-prof-report")
(sb-sprof:start-profiling :max-samples 4000000 :mode :cpu
                          :sample-interval 0.002 :threads :all)
