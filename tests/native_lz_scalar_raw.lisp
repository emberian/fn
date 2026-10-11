;;; Actual compressed arena scalar branch and native scalar/window dispatch.
;;; Existing whole decode and physical returned-worker borrow are recording
;;; boundaries. This does not qualify a decoded worker allocator or image.
(load "tests/native_section_envelope_raw.lisp")
(unless (find-package "ACL2_*1*_ACL2")
  (defpackage "ACL2_*1*_ACL2" (:use "CL")))
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
(defun fnn-core-page-read-pool (name &rest arguments)
  (declare (ignorable name arguments))
  (harness-stub-reached 'fnn-core-page-read-pool "host/native/extent.lisp"))
(defun fnn-extent-where (file eoff)
  (declare (ignorable file eoff))
  (harness-stub-reached 'fnn-extent-where "host/native/extent.lisp"))
;;; ---- derived stubs: END ----
(defun natp (x) (and (integerp x) (<= 0 x)))
(defun zp (x) (not (and (integerp x) (< 0 x))))
(load-deployed-forms "books/octets-stobj.lisp" '((defun fn-oct-nth)))
(load-deployed-forms "host/native/extent.lisp"
 '((defvar *fnn-extent-window-mode*) (defvar *fnn-extent-window-worker*)
   (defvar *fnn-extent-window-token*) (defmacro fnn-core-cold-single)
   (defvar *fnn-extent-lz-buffer-key*) (defvar *fnn-extent-stats*) (defvar *fnn-extent-lock*)
   (defun fnn-extent-lz-buffer-octet) (defun fn-durable-realize-lz-octet)))
(defvar *scalar-full-calls* nil)
(defvar *scalar-borrow-calls* nil)
(defvar *scalar-borrow-word* :byte)
;; The normal arm decodes the whole block once into the generated buffer
;; (fnn-extent-lz-buffer-octet): the compressed read and the decode into the
;; buffer are the recording boundaries; the buffer holds the decoded octets.
(defvar *dlz-buffer* (list nil))
(defvar *fnn-dlz* *dlz-buffer*)
(defun fn-durable-realize-octets (&rest args)
  (push args *scalar-full-calls*) :compressed)
(defun fnn-pzd-decode-into (dict compressed n sink)
  (declare (ignore dict compressed n))
  (funcall sink '(65 66 67))
  :ok)
(defun fn-dlz-fill-from (out st) (setf (car st) out))
(defun fn-dlz-nth (i st) (nth i (car st)))
(defun fnn-live-dlz () *fnn-dlz*)
(defun fnn-core (subject &rest args)
  (assert (member subject '(fn-oct-nth fn-pwz-cold-descriptor fn-pwz-nth)))
  (apply (symbol-function subject) args))
(defun fnn-cold-call (subject &rest args)
  (case subject
    (fn-owner-page-window-decoded-refusal (list :decoded-window-unavailable))
    ((fn-pwz-cold-descriptor fn-pwz-nth)
     (list (apply (symbol-function subject) args)))
    (otherwise (error "unexpected cold scalar subject ~s" subject))))
(let ((*fnn-extent-window-mode* nil))
  (assert (= 66 (fn-durable-realize-lz-octet 7 100 320 120 40 99 3 nil 1)))
  (assert (equal *scalar-full-calls* '((7 100 320 120 40 99)))))
;; No physical provider installed: the existing named ACL2 refusal survives.
(let ((*fnn-extent-window-mode* t))
  (assert (eq :decoded-window-unavailable
              (catch 'fnn-extent-window-refused
                (fn-durable-realize-lz-octet 7 100 320 120 40 99 3 nil 1)))))
(load-deployed-forms "books/decoded-window-descriptor.lisp"
 '((defun fn-pwz-nth) (defun fn-pwz-cold-descriptor)))
(load-deployed-forms "host/native/extent.lisp" '((define-condition fnn-extent-fault)))
(load-deployed-forms "host/native/extent.lisp"
 '((defvar *fnn-extent-window-cache*) (defvar *fnn-extent-cache-span*)
   (defvar *fnn-extent-cache-span-dst*)))
(load-deployed-forms "host/native/extent-decoded.lisp"
 '((defun fnn-extent-decoded-window-realize-octet)
   (defun fnn-extent-decoded-window-cache-byte)))
;; The worker's span copy and span borrow (fnn-extent-decoded-span-hit,
;; fnn-extent-decoded-window-span-octet) are not this fixture's subject: no
;; span is held, and a span miss falls through to the scalar borrow
;; (fnn-extent-decoded-window-byte-at, recorded below), as the deployed
;; span-octet does when ACL2 answers no span.
(defun fnn-extent-decoded-span-hit (worker token file eoff elen poff compressed trailer decoded dict i)
  (declare (ignore worker token file eoff elen poff compressed trailer decoded dict i))
  nil)
(defun fnn-extent-decoded-window-span-octet (worker token file eoff elen poff compressed trailer
                                             decoded dict dict-id i)
  (declare (ignore dict))
  (fnn-extent-decoded-window-byte-at worker token file eoff elen poff compressed
                                     trailer decoded dict-id i))
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
