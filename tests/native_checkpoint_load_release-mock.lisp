;;; A refused state checkpoint gives the served octet buffer back
;;; (host/native/io.lisp fnn-state-checkpoint-load, sweep S071).  The plan
;;; (fnn-state-checkpoint-plan) reserves a file-sized array in the buffer and
;;; fills it; only the :ok arena path hands the buffer on.  Every refusal
;;; (the plan's, ACL2's :arena refusal of a tables-only file, a read error
;;; after the reserve) must leave the buffer empty, or the served process
;;; keeps an array the size of the checkpoint file for its whole life.
;;;
;;; The seams are the plan's file read, ACL2's decode of the buffer, and the
;;; buffer stobj's reserve; fnn-state-checkpoint-load and fnn-octets-release
;;; are the deployed io.lisp.  The stubs make this a -mock fixture: it is
;;; cited by no claim.

(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defvar *the-live-state* nil)
(defun f-get-global (name state) (declare (ignore name state)) nil)
(load "tests/native_io_prelude.lisp")
(load "host/native/io.lisp")

(defvar *stobj* (vector (make-array 0 :element-type '(unsigned-byte 8)) 0))
(setq *fnn-octets* *stobj*)
(defun fn-octets$c-reserve (n st)
  (setf (svref st 0) (make-array n :element-type '(unsigned-byte 8) :initial-element 7)
        (svref st 1) n)
  st)
(defun fnn-core-state (name &rest args)
  (declare (ignore args))
  (case name
    (fn-store-sco-clear nil)
    (otherwise (error "unexpected ACL2 state call ~s" name))))

(defun check (test what)
  (unless test
    (format t "native_checkpoint_load_release: FAIL ~a~%" what)
    (finish-output)
    (sb-ext:exit :code 1 :abort t)))

(defun held () (length (svref *stobj* 0)))
(defun reset-buffer ()
  (setf (svref *stobj* 0) (make-array 0 :element-type '(unsigned-byte 8)) (svref *stobj* 1) 0))
(defun load-outcome (plan decode)
  (reset-buffer)
  (setf (fdefinition 'fnn-state-checkpoint-plan) plan
        (fdefinition 'fnn-core-buffer-state) decode)
  (multiple-value-list (fnn-state-checkpoint-load (make-fnn-store "/store" :writable nil))))

(defun reserving (then)
  (lambda (store) (declare (ignore store))
    (fn-octets$c-reserve 4096 *stobj*)
    (funcall then)))
(defun no-decode (name &rest args) (declare (ignore name args)) (error "decode must not run"))

;; 1. The plan reserved the file's array and then refused it.
(let ((o (load-outcome (reserving (lambda () (values :refused :header))) #'no-decode)))
  (check (eq (first o) :refused) (format nil "a refused plan is :refused, got ~s" o))
  (check (zerop (held))
         "a refused state checkpoint left a file-sized array in the served octet buffer (plan refused)"))

;; 2. The plan read the file; ACL2 refuses a file without the arena run.
(let ((o (load-outcome (reserving (lambda () (values :ok '(frames))))
                       (lambda (name &rest args) (declare (ignore name args)) '(:refused :arena)))))
  (check (eq (first o) :arena) (format nil "a tables-only file is :arena, got ~s" o))
  (check (zerop (held))
         "a refused state checkpoint left a file-sized array in the served octet buffer (:arena)"))

;; 3. ACL2 refuses the decode some other way.
(let ((o (load-outcome (reserving (lambda () (values :ok '(frames))))
                       (lambda (name &rest args) (declare (ignore name args)) '(:refused :other)))))
  (check (eq (first o) :refused) (format nil "an undecodable file is :refused, got ~s" o))
  (check (zerop (held))
         "a refused state checkpoint left a file-sized array in the served octet buffer (decode refused)"))

;; 4. The read fails after the reserve.
(let ((o (load-outcome (reserving (lambda () (fnn-os-fail 5 "/store/checkpoint"))) #'no-decode)))
  (check (eq (first o) :refused) (format nil "a failed read is :refused, got ~s" o))
  (check (zerop (held))
         "a refused state checkpoint left a file-sized array in the served octet buffer (read error)"))

;; 5. No checkpoint at all reserved nothing.
(let ((o (load-outcome (lambda (store) (declare (ignore store)) (values :absent nil)) #'no-decode)))
  (check (eq (first o) :absent) (format nil "no file is :absent, got ~s" o))
  (check (zerop (held)) "an absent checkpoint reserves nothing"))

(format t "native_checkpoint_load_release passed (5 paths)~%")
