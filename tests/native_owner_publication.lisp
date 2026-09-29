;;; Raw witness for the shared prepared-publication boundary (SCN-027 steps
;;; 2 and 4): the deployed host/native/owner.lisp fnn-owner-publish-prepared,
;;; loaded by name, with the ACL2 owner and the Store writes stubbed.
;;;
;;; Step 2 on the record log: the staged record is named by ACL2's
;;; fn-sbud-pending-sequence and a known prepublication refusal appends
;;; nothing, so the next commit names the SAME sequence -- no journal gap
;;; and nothing burned (the retired per-file allocator's transaction IDs are
;;; gone; books/store-identity-sequence-invariants.lisp
;;; fn-sn-known-abort-preserves-identity-sequence is the model's side).
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

;;; ---- derived stubs: BEGIN (python3 tools/harness_check.py --write-stubs; do not edit) ----
;;; ---- derived stubs: END ----

;; The deployed forms, loaded by name so a rename fails here rather than
;; leaving a stale copy in its place.
(defun load-deployed-forms (path wanted)
  (let ((missing (copy-list wanted)))
    (with-open-file (stream path)
      (loop for form = (read stream nil :eof)
            until (eq form :eof)
            when (and (consp form)
                      (member (car form)
                              '(defun defmacro defvar define-condition deftype defstruct))
                      (let ((name (if (consp (cadr form)) (car (cadr form)) (cadr form))))
                        (member (list (car form) name) wanted :test #'equal)))
              do (let ((name (if (consp (cadr form)) (car (cadr form)) (cadr form))))
                   (eval form)
                   (setf missing (remove (list (car form) name) missing
                                         :test #'equal)))))
    (when missing (error "deployed forms missing from ~a: ~s" path missing))))

(load-deployed-forms "host/native/io.lisp"
                     '((define-condition fnn-store-error)
                       (define-condition fnn-store-fault)
                       (define-condition fnn-store-indeterminate)
                       (defun fnn-refuse)
                       (defun fnn-fault)
                       (defun fnn-indeterminate)
                       (deftype fnn-octets)
                       (defun fnn-make-octets)
                       (defun fnn-octets)
                       (defun fnn-octet-list-p)
                       (defun fnn-pending-sequence)
                       (defstruct fnn-store)))

;; fnn-owner-service's exit-code slot defaults to the host's OK code; the
;; slot is never read here.
(defconstant +fnn-exit-ok+ 0)

(load-deployed-forms "host/native/owner.lisp"
                     '((defstruct fnn-owner-service)
                       (defun fnn-owner-signal-commit)
                       (defun fnn-owner-publish-prepared)))

(defun nop-check (test control &rest args)
  (unless test (error (apply #'format nil control args))))

(defvar *nop-sequence* 7
  "The staged sequence the stubbed owner reports (fn-owner-pending-sequence).")
(defvar *nop-published* nil
  "The sequences fnn-publish was called with, most recent first.")

(defun nop-condition (type thunk)
  (handler-case (progn (funcall thunk) nil)
    (error (e) (if (typep e type) e (error "expected ~a, got ~a" type e)))))

;; The stubbed boundary: ACL2's staged record and sequence, the Store's
;; publish and finish, and the owner's known abort.
(defvar *nop-publish* nil)
(defvar *nop-owner-action* nil)
(defvar *nop-finish* nil)

(defun fnn-core-arena-state (name &rest args)
  (declare (ignore args))
  (if (eq name 'fn-owner-pending-octets)
      '(1 2 3)
    (error "unexpected arena entry ~s" name)))
(defun fnn-owner-core (name &rest args)
  (declare (ignore args))
  (if (eq name 'fn-owner-pending-sequence)
      *nop-sequence*
    (error "unexpected owner core call ~s" name)))
(defun fnn-publish (store sequence record)
  (push sequence *nop-published*)
  (funcall *nop-publish* store sequence record))
(defun fnn-owner-action (name &rest args)
  (apply *nop-owner-action* name args))
(defun fnn-finish (store)
  (funcall *nop-finish* store))
(defun fnn-owner-refresh-compression (log)
  (error "the record log is off here (logp nil); refresh reached with ~s" log))

(defun nop-fresh-service ()
  (let ((store (%make-fnn-store :root "/raw" :writable t :lock-fd nil
                                :config nil :frontier 0 :fenced nil)))
    (values store (%make-fnn-owner-service :store store :lock nil
                                           :listener nil :stopping nil))))

(defun nop-refusal-then-valid ()
  (setq *nop-published* nil)
  (multiple-value-bind (store service) (nop-fresh-service)
    (let ((publishes 0) (aborts 0) (finishes 0))
      (setq *nop-publish*
            (lambda (&rest ignored)
              (declare (ignore ignored))
              (incf publishes)
              (when (= publishes 1) (fnn-refuse "expected capacity refusal"))
              :durable)
            *nop-owner-action*
            (lambda (name &rest ignored)
              (declare (ignore ignored))
              (if (eq name 'fn-owner-known-abort)
                  (progn (incf aborts) :aborted)
                (error "unexpected owner action ~s" name)))
            *nop-finish*
            (lambda (&rest ignored) (declare (ignore ignored)) (incf finishes) :durable))
      (let ((refusal (nop-condition 'fnn-store-error
                                    (lambda () (fnn-owner-publish-prepared service "test")))))
        (nop-check refusal "expected refusal was not raised")
        (nop-check (not (typep refusal 'fnn-store-fault)) "refusal became a fault")
        (nop-check (not (typep refusal 'fnn-store-indeterminate)) "refusal became uncertain"))
      (nop-check (not (fnn-store-fenced store))
                 "known prepublication refusal left Store fenced")
      (nop-check (= aborts 1) "known refusal did not consume reservation")
      (nop-check (= (fnn-owner-service-commits service) 0)
                 "a refusal woke the consumer waits")
      (nop-check (eq (fnn-owner-publish-prepared service "test") :durable)
                 "valid operation after refusal did not commit")
      (nop-check (= finishes 1) "valid operation did not finish once")
      (nop-check (= (fnn-owner-service-commits service) 1)
                 "the durable commit did not wake the consumer waits once")
      ;; Step 2: both attempts named the owner's staged sequence; the refusal
      ;; burned nothing, so the commit that follows leaves no gap.
      (nop-check (equal *nop-published* (list *nop-sequence* *nop-sequence*))
                 "publication did not name the owner's staged sequence: ~s"
                 *nop-published*))))

(defun nop-uncertain-and-fault-stay-fenced ()
  (dolist (kind '(fnn-store-indeterminate fnn-store-fault))
    (setq *nop-published* nil)
    (multiple-value-bind (store service) (nop-fresh-service)
      (let ((aborts 0))
        (setq *nop-publish*
              (lambda (&rest ignored)
                (declare (ignore ignored))
                (when (eq kind 'fnn-store-indeterminate)
                  (setf (fnn-store-fenced store) t))
                (error kind :message "injected"))
              *nop-owner-action*
              (lambda (&rest ignored) (declare (ignore ignored)) (incf aborts) :aborted)
              *nop-finish*
              (lambda (&rest ignored) (declare (ignore ignored))
                (error "finish reached after ~a" kind)))
        (nop-check (nop-condition kind
                                  (lambda () (fnn-owner-publish-prepared service "test")))
                   "~a was downgraded" kind)
        (nop-check (fnn-store-fenced store) "~a did not preserve fence" kind)
        (nop-check (zerop aborts) "~a incorrectly ran known abort" kind)
        (nop-check (zerop (fnn-owner-service-commits service))
                   "~a woke the consumer waits" kind)
        (nop-check (equal *nop-published* (list *nop-sequence*))
                   "~a publication did not name the staged sequence" kind)))))

(nop-refusal-then-valid)
(nop-uncertain-and-fault-stay-fenced)
(format t "FN-NATIVE-OWNER-PUBLICATION-PASS~%")
