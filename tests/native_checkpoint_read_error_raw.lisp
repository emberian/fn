;;; An unreadable state checkpoint is the read's fault, never a refusal that
;;; calls the checkpoint damaged (host/native/io.lisp fnn-recover-log,
;;; fnn-state-checkpoint-load).  After `store compact' the covered log
;;; segments are gone, so the open's plan without the checkpoint's F row is
;;; (:refused :checkpoint-damaged) (books/store-log-segments.lisp
;;; fn-lgs-open-plan).  When the checkpoint file is intact but read(2)
;;; failed (EIO), that refusal (exit 1, "checkpoint-damaged") is a verdict on
;;; a file nobody read: an uncertain observation reported as a refusal.  The
;;; open must stop as a fault naming the read error; a checkpoint that WAS
;;; read and does not verify keeps its refusal by name.
;;;
;;; The deployed io.lisp drives the open; the plan is the book's
;;; fn-lgs-open-plan, read from books/store-log-segments.lisp.  The seams are
;;; the checkpoint file's read (fnn-state-checkpoint-plan) and journal/'s
;;; listing.

(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defvar *the-live-state* nil)
(defun f-get-global (name state)
  (declare (ignore name state))
  nil)
(load "tests/native_io_prelude.lisp")
(load "host/native/io.lisp")

;; The ACL2 primitives the book bodies below call, as ACL2 defines them.
(defun nfix (x) (if (and (integerp x) (>= x 0)) x 0))
(defun posp (x) (and (integerp x) (> x 0)))
(defun natp (x) (and (integerp x) (>= x 0)))
(defun zp (x) (or (not (integerp x)) (<= x 0)))
(defmacro mbe (&key logic exec) (declare (ignore logic)) exec)
(defconstant *fn-lgs-max-segment* 999999)
(book-defuns "books/store-log-segments.lisp"
             '(fn-lgs-digit-char fn-lgs-digits fn-lgs-segment-name fn-lgs-digits-value
               fn-lgs-segment-index fn-lgs-indices-loop fn-lgs-indices fn-lgs-max-index
               fn-lgs-range-loop fn-lgs-range fn-lgs-all-present fn-lgs-below-loop
               fn-lgs-below fn-lgs-open-plan))
(defun fnn-call (name &rest args)
  (case name
    (fn-lgs-open-plan (list (apply name args)))
    (otherwise (error "unexpected ACL2 call ~s" name))))
(defun fnn-core-state (name &rest args)
  (declare (ignore args))
  (case name
    (fn-store-sco-clear nil)
    (otherwise (error "unexpected ACL2 state call ~s" name))))

;; journal/ after a compaction: segments 1 and 2 dropped, 3 active.
(defun fnn-log-segment-names (store) (declare (ignore store)) (list "000003.log"))

(defun check (test what)
  (unless test
    (format t "native_checkpoint_read_error: FAIL ~a~%" what)
    (finish-output)
    (sb-ext:exit :code 1 :abort t)))

(defun open-outcome ()
  (let ((store (make-fnn-store "/store" :writable t)))
    (handler-case (progn (fnn-recover-log store) :opened)
      (fnn-store-open-refusal (c) (list :refused (fnn-message c)))
      (fnn-store-fault (c) (list :fault (fnn-message c)))
      (serious-condition (c) (list :other (princ-to-string c))))))

;; 1. The checkpoint file cannot be read: a fault naming the read.
(setf (fdefinition 'fnn-state-checkpoint-plan)
      (lambda (store) (declare (ignore store)) (fnn-os-fail 5 "/store/checkpoint")))
(let ((o (open-outcome)))
  (check (not (eq (first o) :refused))
         "an unreadable checkpoint is refused as checkpoint-damaged (an uncertain read reported as a damage refusal)")
  (check (eq (first o) :fault) (format nil "an unreadable checkpoint is a fault, got ~s" o))
  (check (search "Input/output error" (second o)) "the fault names the read error"))

;; 2. The checkpoint was read and does not verify: the refusal by name stays.
(setf (fdefinition 'fnn-state-checkpoint-plan)
      (lambda (store) (declare (ignore store)) (values :refused :truncated)))
(let ((o (open-outcome)))
  (check (eq (first o) :refused) (format nil "a damaged checkpoint is refused, got ~s" o))
  (check (search "reason=checkpoint-damaged" (second o)) "the refusal names checkpoint-damaged"))

;; 3. A read error with the log still whole is no refusal of the plan: the
;; history from segment 1 is scanned (here: the scan is reached).
(setf (fdefinition 'fnn-state-checkpoint-plan)
      (lambda (store) (declare (ignore store)) (fnn-os-fail 5 "/store/checkpoint")))
(defun fnn-log-segment-names (store) (declare (ignore store)) (list "000001.log"))
(defun fnn-genesis-open (store &optional profile)
  (declare (ignore store profile))
  (error "scan reached"))
(let ((o (open-outcome)))
  (check (and (eq (first o) :other) (search "scan reached" (second o)))
         (format nil "a whole log is replayed past an unreadable checkpoint, got ~s" o)))

(format t "native_checkpoint_read_error: PASS~%")
