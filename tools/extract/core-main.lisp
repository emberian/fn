;;; tools/extract/core-main.lisp -- build the Common Lisp product in a BARE
;;; SBCL (no ACL2): the image's packages, the hand runtime, the extracted
;;; definitions (defs.lisp, forms-export.lisp), the image's state and world values the code reads
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
;; defs.lisp's forms are read and evaluated one at a time, each compiled as it is read (as ACL2
;; compiles its own installs), so a defglobal/defparameter initializer can call a function defined above
;; it.  Not `load': loading a source file gives every compiled form a debug source holding its own copy of
;; the file's form-position table so far, which for defs.lisp's ~25,000 forms was 1.29 GB of
;; (unsigned-byte 32) vectors in the saved core (EXTRACTION-PROGRAM-20261007.md section 6).
;; Every form evaluated here is compiled with STORE-SOURCE-FORM 0.  Otherwise SBCL keeps each function's
;; whole macroexpanded source form in its debug source (a CORE-DEBUG-SOURCE's FORM): at dev f2629613e the
;; build's dynamic usage is 66.3 MiB with this policy and 98.4 MiB without it, and the core is 100.2 MB.
;; Those cold conses sat between the objects the server reads, so a long-resident core's 64 KiB
;; fault-around windows mapped them in (CONVERGE-3 row 23).
(proclaim '(optimize (sb-c:store-source-form 0)))
(defun cl-user::xl-eval-forms (path external-format)
  (with-open-file (in path :external-format external-format)
    (let ((*package* *package*) (*readtable* *readtable*) (eof (list nil)))
      (loop for form = (read in nil eof)
            until (eq form eof)
            do (eval form)))))
;; ONE compilation unit from the runtime to the end of host/native: SBCL's undefined-function summary is then
;; judged after the host has defined what the books only constrain (X2); tools/extract/core.sh fails the build
;; on any name in it.
(with-compilation-unit ()
(load (concatenate 'string (sb-ext:posix-getenv "XL_X") "clruntime.lisp"))
;; The whole product is compiled at DEBUG 0: SBCL then keeps each code object's name and entry point but drops its
;; block (code-location) maps.  The prologue's declaim in defs.lisp (O1: ACL2's own form) sets only
;; compilation-speed, speed, space and safety, so it leaves this quality alone.  Exceptions, from ONE data file
;; (tools/extract/debug-keep.txt, read again by debug_keep.py): the host's fault boundaries and its two
;; backtrace readers are recompiled at DEBUG 1 below, after host-block.lisp has loaded.
(proclaim '(optimize (debug 0)))
(cl-user::xl-eval-forms (cl-user::xl-path "defs.lisp") :latin-1)
(load (cl-user::xl-path "core-world.lisp") :external-format :utf-8)
;; named through its symbol: this form is compiled before defs.lisp defines it
(funcall 'acl2::xl-make-live-stobjs)
;; ACL2's standard channels get their streams at load (axioms.lisp:19005 setup-standard-io and the
;; eval-when after it); an ACL2 warning the served code prints goes to them, as the image's does
(unless (fboundp 'acl2::setup-standard-io) (error "core: setup-standard-io is not in the closure"))
(funcall 'acl2::setup-standard-io)
;; ACL2's global compilation policy: the image compiles host/native under it
(proclaim '(optimize (compilation-speed 0) (speed 3) (space 1) (safety 0)))
(when (sb-ext:posix-getenv "XL_PROF") (require :sb-sprof))
;; Inventory build-selected profiling hooks before participant registration.
;; The actual image-hook checker refuses other restore callbacks; loading a
;; module after that check would evade the saved-image exclusion contract.
(load (cl-user::xl-path "host-block.lisp"))
;; The debug-keep set (tools/extract/debug-keep.txt): each defun is read from its host file and compiled again at
;; DEBUG 1 (its callers reach it through the global function cell, so they need not be recompiled).
(let ((keep (concatenate 'string (sb-ext:posix-getenv "XL_X") "debug-keep.txt")) (seen nil))
  (with-open-file (in keep)
    (loop for line = (read-line in nil) while line
          do (let ((line (string-trim " " line)))
               (unless (or (zerop (length line)) (char= (char line 0) #\#))
                 (let* ((sp (position #\Space line))
                        (name (let ((*package* (find-package "ACL2"))) (read-from-string (subseq line 0 sp))))
                        (file (string-trim " " (subseq line sp)))
                        (found nil))
                   (with-open-file (src file :external-format :latin-1)
                     (let ((*package* (find-package "ACL2")) (eof (list nil)))
                       (loop for form = (read src nil eof) until (eq form eof)
                             do (when (and (consp form) (eq (car form) 'defun) (eq (cadr form) name))
                                  (proclaim '(optimize (debug 1)))
                                  (handler-bind ((warning #'muffle-warning)) (eval form))
                                  (proclaim '(optimize (debug 0)))
                                  (setq found t) (return)))))
                   (unless found (error "debug-keep: no top-level defun ~a in ~a" name file))
                   (push name seen))))))
  (format t "~&debug-keep: ~d functions recompiled at debug 1~%" (length seen)))
) ; the compilation unit
(defun cl-user::xl-toplevel ()
  ;; Stage 0 (planning/design-store-representation-2026-10-01.md section 4):
  ;; no (acl2::fnn-runtime-bootstrap-startup) gate before argv; its
  ;; producer (the compiled operation table) does not exist, so it exited
  ;; every verb (host/native/build.lisp fn-native-entry says the same).
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
  ;; This is an idempotent lookup after image construction. The saved native
  ;; bootstrap and the live registry must keep the same stobj identities.
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
  ;; A developer core's measurement hook (the load/scale harness's in-process arms, as the image's
  ;; hooks are loaded with --eval before acl2::sbcl-restart): XL_HOOK=FILE loads FILE (package ACL2)
  ;; and then starts fn as usual.  A production core refuses it, as above.
  (let ((hook (sb-ext:posix-getenv "XL_HOOK")))
    (when (and hook (plusp (length hook)))
      (unless (acl2::fnn-developer-image-p)
        (format *error-output* "fn-host: error: XL_HOOK is a developer-core facility~%")
        (sb-ext:exit :code 5 :abort t))
      (let ((*package* (find-package "ACL2"))) (load hook))))
  (acl2::fn-native-entry nil)
  (sb-ext:exit :code 0))
(sb-ext:gc :full t)
(format t "~&XL built; dynamic usage ~,1f MiB~%" (/ (sb-kernel:dynamic-usage) 1048576.0))
;; Keep the existing native launcher/core packaging contract. SBCL handles
;; command-line options, then the generated launcher calls XL-TOPLEVEL. A
;; runtime identity probe can consequently exit without starting fn.
(sb-ext:save-lisp-and-die (cl-user::xl-path "fn-core.core")
                        :toplevel #'sb-impl::toplevel-init :executable nil)
