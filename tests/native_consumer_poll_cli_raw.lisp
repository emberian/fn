;;; Exercise the shipped CLI adapter, including its request/output split.
(defpackage "ACL2" (:use "CL"))
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
(defun fnn-octet-list (octets)
  (declare (ignorable octets))
  (harness-stub-reached 'fnn-octet-list "host/native/io.lisp"))
(defun fnn-read-regular-bounded (path maximum)
  (declare (ignorable path maximum))
  (harness-stub-reached 'fnn-read-regular-bounded "host/native/io.lisp"))
;;; ---- derived stubs: END ----

(defvar *calls* nil)
(defparameter +fnn-exit-usage+ 2)
(defparameter +fnn-exit-ok+ 0)
(defun fnn-ascii-octet-list (s) (map 'list #'char-code s))
(defun fnn-octets (x) x)
(defun fnn-octets-string (x) (map 'string #'code-char x))
(defun fnn-octet-list-p (x)
  (and (listp x) (every (lambda (b) (and (integerp b) (<= 0 b 255))) x)))
(defun fnn-core (name &rest args)
  (declare (ignore args))
  (case name
    (fn-native-control-host-consumer-cli-plan
     (list :run :poll '(99) '(119) '(99 117 114 115 111 114)
           '(114 101 112 111 114 116)))
    (fn-native-control-host-status-exit-code 0)
    ;; PKT-709: no register retry for a poll; the report's summary for the
    ;; line (text mode prints only the status).
    (fn-native-control-host-consumer-cli-after nil)
    (fn-native-control-host-consumer-report-summary '(:empty))
    (otherwise (error "unexpected ACL2 entry ~s" name))))
(defun fnn-control-consumer-local (control operation first second)
  (push (list :request control operation first second) *calls*)
  (values (list :consumer-poll-reply :accepted '(1 2 3) '(4 5 6)) nil))
(defun fnn-write-staged (path bytes)
  (push (list :write path bytes) *calls*))
(defun fnn-out (&rest args) (declare (ignore args)))
(defun fnn-err (&rest args) (error "unexpected CLI refusal ~s" args))
(defun fnn-fault (&rest args) (error "native fault ~s" args))
(defun fnn-register-verb (&rest args) (declare (ignore args)))

(let ((found nil))
  (with-open-file (stream "host/native/consumer-local.lisp")
    (loop for form = (read stream nil :eof)
          until (eq form :eof)
          when (and (consp form) (eq (car form) 'defun)
                    (member (cadr form) '(fnn-command-consumer-local
                                          fnn-consumer-say)))
            do (eval form)
               (when (eq (cadr form) 'fnn-command-consumer-local)
                 (setf found t))))
  (unless found (error "deployed consumer CLI adapter missing")))

(unless (eql (fnn-command-consumer-local "poll"
                                         '("control" "worker" "cursor" "report"))
             0)
  (error "poll did not return ACL2 accepted status"))
(unless (equal (reverse *calls*)
               '((:request (99) :poll (119) nil)
                 (:write "report" (4 5 6))
                 (:write "cursor" (1 2 3))))
  (error "poll request included output path or lost report-before-cursor writes: ~s"
         (reverse *calls*)))
(format t "native consumer poll CLI boundary passed~%")
