;;; Actual compressed arena scalar branch and native scalar/window dispatch.
;;; Existing whole decode and physical returned-worker borrow are recording
;;; boundaries. This does not qualify a decoded worker allocator or image.
(load "tests/native_section_envelope_raw.lisp")
(unless (find-package "ACL2_*1*_ACL2")
  (defpackage "ACL2_*1*_ACL2" (:use "CL")))
(in-package "ACL2")
(defun natp (x) (and (integerp x) (<= 0 x)))
(defun zp (x) (not (and (integerp x) (< 0 x))))
(load-deployed-forms "books/octets-stobj.lisp" '((defun fn-oct-nth)))
(load-deployed-forms "host/native/extent.lisp"
 '((defvar *fnn-extent-window-mode*) (defvar *fnn-extent-window-worker*)
   (defvar *fnn-extent-window-token*) (defmacro fnn-core-cold-single)
   (defun fn-durable-realize-lz-octet)))
(defvar *scalar-full-calls* nil)
(defvar *scalar-borrow-calls* nil)
(defvar *scalar-borrow-word* :byte)
(defun fn-durable-realize-lz (&rest args)
  (push args *scalar-full-calls*) '(65 66 67))
(defun fnn-core (subject &rest args)
  (assert (eq subject 'fn-oct-nth)) (apply #'fn-oct-nth args))
(defun fnn-cold-call (subject &rest args)
  (case subject
    (fn-owner-page-window-decoded-refusal (list :decoded-window-unavailable))
    ((fn-pwz-cold-descriptor fn-pwz-nth)
     (list (apply (symbol-function subject) args)))
    (otherwise (error "unexpected cold scalar subject ~s" subject))))
(let ((*fnn-extent-window-mode* nil))
  (assert (= 66 (fn-durable-realize-lz-octet 7 100 320 120 40 99 3 nil 1)))
  (assert (equal *scalar-full-calls* '((7 100 320 120 40 99 3 nil)))))
;; No physical provider installed: the existing named ACL2 refusal survives.
(let ((*fnn-extent-window-mode* t))
  (assert (eq :decoded-window-unavailable
              (catch 'fnn-extent-window-refused
                (fn-durable-realize-lz-octet 7 100 320 120 40 99 3 nil 1)))))
(load-deployed-forms "books/decoded-window-descriptor.lisp"
 '((defun fn-pwz-nth) (defun fn-pwz-cold-descriptor)))
(load-deployed-forms "host/native/extent.lisp" '((define-condition fnn-extent-fault)))
(load-deployed-forms "host/native/extent-decoded.lisp"
 '((defun fnn-extent-decoded-window-realize-octet)))
(defun fnn-extent-decoded-window-byte-at (&rest args)
  (push args *scalar-borrow-calls*) (values *scalar-borrow-word* 66))
(let ((*fnn-extent-window-mode* t) (*fnn-extent-window-worker* nil))
  (assert (equal (catch 'fnn-extent-cold
                   (fn-durable-realize-lz-octet 7 100 320 120 40 99 3 nil 1))
                 '(7 100 320 120 40 1 99 3 0))))
(let ((*fnn-extent-window-mode* t) (*fnn-extent-window-worker* :actual-worker)
      (*fnn-extent-window-token* :actual-token))
  (assert (= 66 (fn-durable-realize-lz-octet 7 100 320 120 40 99 3 nil 1)))
  (assert (equal (car *scalar-borrow-calls*)
                 '(:actual-worker :actual-token 7 100 320 120 40 99 3 0 1)))
  (dolist (*scalar-borrow-word* '(:cancelled :stale-job))
    (assert (eq *scalar-borrow-word*
                (catch 'fnn-extent-window-refused
                  (fn-durable-realize-lz-octet 7 100 320 120 40 99 3 nil 1)))))
  (let ((*scalar-borrow-word* :pending))
    (assert (handler-case
                (progn (fn-durable-realize-lz-octet 7 100 320 120 40 99 3 nil 1) nil)
              (fnn-extent-fault () t)))))
;; Exercise the actual compressed arena arm. Other storage kinds are outside
;; this physical getter fixture; no resident/staged representation is claimed.
(defmacro stobj-let (&rest ignored) (declare (ignore ignored))
  '(error "unexpected resident arena arm"))
(defun fn-arena$x-exti (h arena) (aref arena h))
(defun fn-arn-extentp (entry) (= (length entry) 6))
(defun fn-arn-lz-extentp (entry) (= (length entry) 8))
(load-deployed-forms "books/payload-arena-extent.lisp" '((defun fn-arena$x-get)))
(let ((*fnn-extent-window-mode* t) (*fnn-extent-window-worker* :actual-worker)
      (*fnn-extent-window-token* :actual-token))
  (assert (= 66 (fn-arena$x-get 0 1 #((7 100 320 120 40 99 3 nil))))))
(assert (= 1 (length *scalar-full-calls*)))
(format t "native_lz_scalar_raw: PASS actual arena scalar/normal nth/window cold/borrow/refusal/no full fallback~%")
