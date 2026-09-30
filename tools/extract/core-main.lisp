;;; tools/extract/core-main.lisp -- build the Common Lisp product in a BARE
;;; SBCL (no ACL2): the image's packages, the hand runtime, the extracted
;;; definitions (cl.py), the image's state and world values the code reads
;;; (core-world.lisp), then host/native exactly as host/native/build.lisp
;;; loads it (core_build.py), saved as one executable.  Run from the tree's
;;; root; XL_OUT names build/core/.  tools/extract/core.sh runs it.
(setq *compile-verbose* nil *compile-print* nil)
;; ACL2's external formats (acl2.lisp): Latin-1 for streams, file names and
;; the command line, so argv's octets are the characters the image reads
(setq sb-impl::*default-external-format* :iso-8859-1)
(setq sb-alien::*default-c-string-external-format* :iso-8859-1)
(defvar cl-user::*xl-out* (sb-ext:posix-getenv "XL_OUT"))
(defun cl-user::xl-path (name) (concatenate 'string cl-user::*xl-out* name))
(load (cl-user::xl-path "packages.lisp") :external-format :latin-1)
(with-compilation-unit ()
  (load (compile-file (concatenate 'string (sb-ext:posix-getenv "XL_X") "clruntime.lisp")
                      :output-file (cl-user::xl-path "clruntime.fasl")))
  (load (compile-file (cl-user::xl-path "defs.lisp") :output-file (cl-user::xl-path "defs.fasl")
                      :external-format :latin-1)))
(load (cl-user::xl-path "core-world.lisp") :external-format :utf-8)
(acl2::xl-make-live-stobjs)
;; ACL2's global compilation policy: the image compiles host/native under it
(proclaim '(optimize (compilation-speed 0) (speed 3) (space 1) (safety 0)))
(load (cl-user::xl-path "host-block.lisp"))
(setq acl2::*xl-user-stobj-alist* nil)
(when (sb-ext:posix-getenv "XL_PROF") (require :sb-sprof))
(defun cl-user::xl-toplevel ()
  ;; a profiling build (XL_PROF at build and at run): a statistical profile of
  ;; the command, reported to stderr at exit.  A measurement tool only.
  (when (and (find-package "SB-SPROF") (sb-ext:posix-getenv "XL_PROF"))
    (funcall (intern "START-PROFILING" "SB-SPROF") :sample-interval 0.0005 :threads :all)
    (let ((exit (fdefinition 'acl2::fnn-exit)))
      (setf (fdefinition 'acl2::fnn-exit)
            (lambda (code)
              (let ((*standard-output* *error-output*))
                (funcall (intern "REPORT" "SB-SPROF") :type :flat :max 40))
              (funcall exit code))))
    ;; XL_PROF_SECONDS: report and show where the main thread is, then exit
    (let ((secs (sb-ext:posix-getenv "XL_PROF_SECONDS")) (main sb-thread:*current-thread*))
      (when secs
        (sb-ext:schedule-timer
         (sb-ext:make-timer (lambda ()
                              (let ((*standard-output* *error-output*))
                                (funcall (intern "REPORT" "SB-SPROF") :type :flat :max 30)
                                (sb-thread:interrupt-thread main (lambda () (sb-debug:print-backtrace :count 40)
                                                                   (sb-ext:exit :code 99 :abort t)))))
                            :thread t)
         (parse-integer secs)))))
  (acl2::xl-make-live-stobjs)
  ;; A developer core's evaluation hook for the extraction gate's boundary
  ;; probes (tools/extract/probes.py run-core): `fn-core --xl-load FILE'
  ;; loads FILE (forms in package ACL2 calling fnn-call) and exits.  A
  ;; production core refuses it, as it refuses every developer selector.
  (let ((args sb-ext:*posix-argv*))
    (when (and (equal (second args) "--xl-load") (third args))
      (unless (acl2::fnn-developer-image-p)
        (format *error-output* "fn-host: error: --xl-load is a developer-core facility~%")
        (sb-ext:exit :code 5 :abort t))
      (acl2::fnn-open-streams)
      (let ((*package* (find-package "ACL2"))) (load (third args)))
      (finish-output)
      (sb-ext:exit :code 0 :abort t)))
  (acl2::fn-native-entry nil)
  (sb-ext:exit :code 0))
(sb-ext:gc :full t)
(format t "~&XL built; dynamic usage ~,1f MiB~%" (/ (sb-kernel:dynamic-usage) 1048576.0))
;; Keep the existing native launcher/core packaging contract. SBCL handles
;; command-line options, then the generated launcher calls XL-TOPLEVEL. A
;; runtime identity probe can consequently exit without starting fn.
(sb-ext:save-lisp-and-die (cl-user::xl-path "fn-core.core")
                        :toplevel #'sb-impl::toplevel-init :executable nil)
