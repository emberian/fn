;;; The developer evaluator's own semantics in a bare SBCL: one form, no reader
;;; evaluation, bounded output, errors as an :error status, the evaluation inside
;;; the owner's serialization (a mutex here: the real owner is not loaded, so this
;;; claims nothing about its admission or fencing; tests/dev_repl_native.py does).
;;; __TRACE__ is host/native/trace.lisp; __EVAL__ the evaluation half of
;;; host/native/developer-eval.lisp (everything before its server side).
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defvar *the-live-state* nil)
(defvar *standard-co* nil)
(defvar *owner-lock* (sb-thread:make-mutex))
(defvar *serialized-class* nil)
(defun fnn-owner-serialized (service cid thunk class)
 (declare (ignore service cid))
 (setq *serialized-class* class)
 (sb-thread:with-recursive-lock (*owner-lock*) (funcall thunk)))
(defun fnn-core (name &rest args)
 (declare (ignore args))
 (if (eq name 'fn-deval-max-output-characters) 65536 (error "unexpected core call ~s" name)))
(load "__TRACE__")
(load "__EVAL__")
(defun run (text) (multiple-value-list (fnn-dev-evaluate nil text)))
(defmacro check (form) `(unless ,form (format t "FAILED ~s~%" ',form) (finish-output) (sb-ext:exit :code 1 :abort t)))
(check (equal (run "(+ 20 22)") '(:ok "42
")))
(check (eq *serialized-class* :inspect))
(check (eq (first (run "(defparameter *dev-test-value* 17)")) :ok))
(check (equal (run "*dev-test-value*") '(:ok "17
")))
(check (equal (run "(values 1 2 3)") '(:ok "1
2
3
")))
(check (eq (first (run "#.(error \"reader eval\")")) :error))
(check (eq (first (run "(+ 1 2) (+ 3 4)")) :error))
(check (eq (first (run "")) :error))
(check (eq (first (run "(+ 1 2")) :error))
(check (equal (run "(+ 1 2)") '(:ok "3
")))
(let ((long (run "(dotimes (i 70000) (write-char #\\x))")))
 (check (eq (first long) :ok))
 (check (search "[output truncated]" (second long)))
 (check (< (length (second long)) 65700)))
(let ((failed (run "(error \"evaluation failure\")")))
 (check (eq (first failed) :error))
 (check (search "evaluation failure" (second failed))))
(check (eq (first (run "(progn (fnn-trace-start :allocation :process) :tracing)")) :ok))
(check (eq (first (run "(+ 41 1)")) :ok))
(let ((report (run "(fnn-trace-report *standard-output*)")))
 (check (eq (first report) :ok))
 (check (search "\"phase\":\"developer-eval\"" (second report)))
 (check (search "\"allocation_scope\":\"process\"" (second report))))
(format t "DEV-EVAL-FIXTURE-PASS~%")
