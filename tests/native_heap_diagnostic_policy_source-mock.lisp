; SCN-1136 continuation: actual STATUS/HEALTH consumers retain normalized
; configuration policies; the actual ACL2 output extension contributes MB.
(load "tests/native_heap_default_source-mock.lisp")
(require :sb-bsd-sockets)
(in-package "ACL2")

;;; ---- derived stubs: BEGIN (python3 tools/harness_check.py --write-stubs; do not edit) ----
(define-condition harness-stub-reached (serious-condition)
  ((name :initarg :name :reader harness-stub-reached-name)
   (source :initarg :source :reader harness-stub-reached-source))
  (:report (lambda (c s)
             (format s "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it"
                     (harness-stub-reached-name c) (harness-stub-reached-source c)))))
(defun harness-stub-reached (name source)
  (format *error-output* "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it~%"
          name source)
  (finish-output *error-output*)
  (error 'harness-stub-reached :name name :source source))
(defun fnn-bp-session-profile (root)
  (declare (ignorable root))
  (harness-stub-reached 'fnn-bp-session-profile "host/native/bp-session.lisp"))
(defun fnn-bps-read-profile (root)
  (declare (ignorable root))
  (harness-stub-reached 'fnn-bps-read-profile "host/native/bp-service.lisp"))
;;; ---- derived stubs: END ----
(selected-source "books/native-config.lisp"
 '(fn-native-config-store fn-native-config-cold-resources fn-native-config-output-resources))
(selected-source "books/native-operator.lisp" '(fn-native-operator-result-config))
(selected-source "host/native-operator-host.lisp"
 '(fn-native-operator-host-result-config fn-native-operator-host-result-store-root))
(source-forms "host/native/operator.lisp" '(fnn-operator-print-next-run-heap))
(source-forms (or (sixth sb-ext:*posix-argv*) "host/native/operator.lisp")
 '(fnn-operator-execute-status fnn-operator-execute-health))
(defparameter *before-diagnostic-core* (symbol-function 'fnn-core))
(defun fnn-core (entry &rest args)
 (case entry
  ((fn-native-operator-host-result-config fn-native-operator-host-result-store-root
    fn-native-config-cold-resources fn-native-config-output-resources)
   (apply (symbol-function entry) args))
  (fn-native-operator-host-result-command (third (first args)))
  ((fn-native-operator-host-result-status-watch
    fn-native-operator-host-result-status-control-path-octets) nil)
  (fn-native-operator-host-result-status-kind :fixture)
  (fn-native-operator-host-result-health-min-percent 10)
  (fn-native-health-host-exit 0)
  ;; tariff2 (075343bea): the accounting line follows the heap line; its text
  ;; is books/output-admission-line.lisp's, so the fixture only checks that
  ;; the configured output policy reaches it.
  (fn-oadl-accounting-line (push (list :accounting (first args)) *calls*) "|accounting")
  (otherwise (apply *before-diagnostic-core* entry args))))
(defun fnn-filesystem-durability-warn (&rest args) (declare (ignore args)) nil)
; PRF-1327: no running owner, so no key-exchange line after the report.
(defvar *fnn-operator-live-owner* nil)
(defun fnn-operator-status-once (&rest args) (declare (ignore args)) 0)
(defun fnn-operator-emit-status (&rest args) (declare (ignore args)) nil)
(defun fnn-operator-status-of-exit-code (code) (assert (= code 0)) :accepted)
(defun fnn-operator-health-report (&rest args) (declare (ignore args)) :health-report)
(defun fnn-write-report (report) (assert (eq report :health-report)))
(defparameter +fnn-exit-refused+ 1)
(defun policy-case (command cold output expected)
 (let* ((config (make-list 31))
        (result (list :accepted nil command config nil))
        (*fnn-stdout* (make-string-output-stream))
        (*calls* nil) (*captured-core* 0) (*captured-machine* 0))
  (setf (first config) "/fixture" (nth 29 config) cold (nth 30 config) output)
  (assert (= (if (equal command "status")
                (fnn-operator-execute-status result)
              (fnn-operator-execute-health result)) 0))
  (assert (equal (get-output-stream-string *fnn-stdout*) expected))
  (let ((cold-call (assoc :cold *calls*)) (output-call (assoc :output *calls*)))
   (assert (equal (third cold-call) cold))
   (assert (equal (third output-call) output))
   (assert (equal (assoc :accounting *calls*) (list :accounting output))))
  (assert (= *captured-core* *captured-machine* 1))))
; The DEFAULT run (259 MiB before output: tests/native_heap_default_source-mock.lisp)
; and the explicit-cold one (256) each add the 16 MiB output backing: 275 and
; 272.  At the 8 MiB collection-trigger cap (books/profile-limits.lisp
; :gc-nursery-mib, MEM-007) the output backing no longer enlarges the
; collector's nursery protection, which at the former 64 MiB cap added 3 MiB
; (the former 276/275).
(dolist (command '("status" "health"))
 (policy-case command nil '(16777216 1048576) "(:HEAP 275 :SMALL 8192 1024 16)|accounting")
 (policy-case command '(67108864 4 256 256 256) '(16777216 1048576)
              "(:HEAP 272 :SMALL 8192 1024 16)|accounting"))
(format t "SOURCE NEXT-RUN POLICY DIAGNOSTICS PASSED~%")
