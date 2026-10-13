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
 '(fn-ncfg-nth *fn-ncfg-max-u64* fn-native-config-output-resources-wfp))
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
(defun policy-case (command cold output)
 (let* ((config (make-list 31))
        (result (list :accepted nil command config nil))
        (*fnn-stdout* (make-string-output-stream))
        (*calls* nil) (*observed* nil))
  (setf (first config) "/fixture" (nth 29 config) cold (nth 30 config) output)
  (assert (= (if (equal command "status")
                (fnn-operator-execute-status result)
              (fnn-operator-execute-health result)) 0))
  ;; the next run's launch line (fnn-heap-print-store-line: the probe's own
  ;; decision), then the accounting line
  (assert (equal (get-output-stream-string *fnn-stdout*)
                 (format nil "~s|accounting" *serve*)))
  ;; the configured policies reach the launch's pools and threads
  (let ((launch (call-of *calls* :serve)))
   (assert (equal (nth 4 launch) cold))
   (assert (equal (nth 11 launch) output))
   (assert (equal (nth 12 launch) *peer*)))
  (assert (equal (assoc :accounting *calls*) (list :accounting output)))
  (assert (= 1 (count :core *observed*)))
  (assert (not (member :machine *observed*)))))
; The DEFAULT run and an explicit-cold one, each with an output pool: the
; next-run line is the served run's launch over the pools those policies fund.
(dolist (command '("status" "health"))
 (policy-case command nil '(16777216 1048576))
 (policy-case command '(67108864 4 256 256 256) '(16777216 1048576)))
(format t "SOURCE NEXT-RUN POLICY DIAGNOSTICS PASSED~%")
