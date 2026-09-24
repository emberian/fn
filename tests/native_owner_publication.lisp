;;; Raw witness for the shared prepared-publication boundary.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defvar *the-live-state* nil)
(defun f-get-global (name state) (declare (ignore name state)) nil)
(load "host/native/io.lisp")
(load "host/native/owner.lisp")

(defun nop-check (test control &rest args)
  (unless test (error (apply #'format nil control args))))

(defvar *nop-sequence* 7
  "The staged sequence the stubbed owner reports (fn-owner-pending-sequence).")
(defvar *nop-published* nil
  "The sequences fnn-publish was called with, most recent first.")

(defun nop-condition (type thunk)
  (handler-case (progn (funcall thunk) nil)
    (error (e) (if (typep e type) e (error "expected ~a, got ~a" type e)))))

(defun nop-with-stubs (publish owner-action finish thunk)
  (let ((saved (mapcar (lambda (name) (cons name (symbol-function name)))
                       '(fnn-owner-core fnn-publish fnn-owner-action fnn-finish))))
    (unwind-protect
         (progn
           (setf (symbol-function 'fnn-owner-core)
                 (lambda (name &rest ignored)
                   (declare (ignore ignored))
                   (case name
                     (fn-owner-pending-octets '(1 2 3))
                     (fn-owner-pending-sequence *nop-sequence*)
                     (t (error "unexpected owner core call ~s" name)))))
           (setf (symbol-function 'fnn-publish)
                 (lambda (store sequence record)
                   (push sequence *nop-published*)
                   (funcall publish store sequence record))
                 (symbol-function 'fnn-owner-action) owner-action
                 (symbol-function 'fnn-finish) finish)
           (funcall thunk))
      (dolist (entry saved)
        (setf (symbol-function (car entry)) (cdr entry))))))

(defun nop-refusal-then-valid ()
  (setq *nop-published* nil)
  (let* ((store (%make-fnn-store :root "/raw" :writable t :lock-fd nil
                                 :config nil :frontier 0 :fenced nil))
         (service (%make-fnn-owner-service :store store :lock nil
                                          :listener nil :stopping nil))
         (publishes 0) (aborts 0) (finishes 0))
    (nop-with-stubs
     (lambda (&rest ignored)
       (declare (ignore ignored))
       (incf publishes)
       (when (= publishes 1) (fnn-refuse "expected capacity refusal"))
       :durable)
     (lambda (name &rest ignored)
       (declare (ignore ignored))
       (if (eq name 'fn-owner-known-abort)
           (progn (incf aborts) :aborted)
         (error "unexpected owner action ~s" name)))
     (lambda (&rest ignored) (declare (ignore ignored)) (incf finishes) :durable)
     (lambda ()
       (nop-check (nop-condition 'fnn-store-error
                                 (lambda () (fnn-owner-publish-prepared service "test")))
                  "expected refusal was not preserved")
       (nop-check (not (fnn-store-fenced store))
                  "known prepublication refusal left Store fenced")
       (nop-check (= aborts 1) "known refusal did not consume reservation")
       (nop-check (eq (fnn-owner-publish-prepared service "test") :durable)
                  "valid operation after refusal did not commit")
       (nop-check (= finishes 1) "valid operation did not finish once")
       ;; Both attempts named the owner's staged sequence; the host counted
       ;; nothing of its own.
       (nop-check (equal *nop-published* (list *nop-sequence* *nop-sequence*))
                  "publication did not name the owner's staged sequence: ~s"
                  *nop-published*)))))

(defun nop-uncertain-and-fault-stay-fenced ()
  (setq *nop-published* nil)
  (dolist (kind '(fnn-store-indeterminate fnn-store-fault))
    (let* ((store (%make-fnn-store :root "/raw" :writable t :lock-fd nil
                                   :config nil :frontier 0 :fenced nil))
           (service (%make-fnn-owner-service :store store :lock nil
                                            :listener nil :stopping nil))
           (aborts 0))
      (nop-with-stubs
       (lambda (&rest ignored)
         (declare (ignore ignored))
         (when (eq kind 'fnn-store-indeterminate)
           (setf (fnn-store-fenced store) t))
         (error kind))
       (lambda (&rest ignored) (declare (ignore ignored)) (incf aborts) :aborted)
       (lambda (&rest ignored) (declare (ignore ignored))
         (error "finish reached after ~a" kind))
       (lambda ()
         (nop-check (nop-condition kind
                                   (lambda () (fnn-owner-publish-prepared service "test")))
                    "~a was downgraded" kind)
         (nop-check (fnn-store-fenced store) "~a did not preserve fence" kind)
         (nop-check (zerop aborts) "~a incorrectly ran known abort" kind)
         (nop-check (member *nop-sequence* *nop-published*)
                    "~a publication did not name the staged sequence" kind))))))

(nop-refusal-then-valid)
(nop-uncertain-and-fault-stay-fenced)
(format t "FN-NATIVE-OWNER-PUBLICATION-PASS~%")
