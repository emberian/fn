;;; A cleanup that fails while its body is escaping is a recovery event, never
;;; a swallowed log line (AGENTS.md; planning/handoff-2026-10-03/failure-scope.md,
;;; review M3d).  Drives the deployed fnn-unwind-cleanups and
;;; fnn-escape-cleanup-failed (host/native/io.lisp, or the io.lisp named by
;;; FN_CLEANUP_HOST_SOURCE: the red run reads origin/next's) over the deployed
;;; ACL2 decisions (books/failure-scope.lisp, books/outcome-class.lisp), against
;;; a recording fnn-err.  Each case asserts what escapes AND what is recorded.
(load "tests/unwind_cleanups_prelude.lisp")
(in-package "ACL2")
(defvar *io-source* *unwind-prelude-io-source*)
;; The conditions and signalling functions the cases drive, from the same source.
(unwind-prelude-load-forms
 *io-source*
 '((define-condition fnn-store-error) (define-condition fnn-store-fault)
   (define-condition fnn-store-indeterminate) (define-condition fnn-os-error)
   (defun fnn-fault) (defun fnn-indeterminate) (defun fnn-os-fail) (defun fnn-refuse)))
(unwind-prelude-load-forms *io-source* '((defmacro fnn-unwind-cleanups)))

(defvar *err* nil)
(defun fnn-err (control &rest args) (push (apply #'format nil control args) *err*))
(unless (boundp '*fnn-escape-cleanup-debts*) (defvar *fnn-escape-cleanup-debts* (list nil)))

(defun check (ok what) (unless ok (error "FAILED: ~a" what)))
(defun escape-of (thunk)
  "The condition that left THUNK, or its values."
  (handler-case (values (multiple-value-list (funcall thunk)) nil)
    (serious-condition (c) (values nil c))))
(defmacro with-fresh (&body body)
  `(let ((*err* nil) (*fnn-escape-cleanup-debts* (list nil)) (*fnn-section-step* nil)) ,@body))
(defun failing-os () (fnn-os-fail 5 "/staged"))

;; 1. A known refusal escapes while one of three cleanups fails with an OS
;; error before any durable step: every cleanup runs; the failure is recorded;
;; the escape is the fault the cleanup is (a refusal says nothing happened),
;; naming both.
(with-fresh
  (let ((ran nil))
    (multiple-value-bind (values c)
        (escape-of (lambda ()
                     (fnn-unwind-cleanups ((fnn-refuse "body refused"))
                       (push 1 ran) (failing-os) (push 3 ran))))
      (check (null values) "case 1 escaped")
      (check (equal ran '(3 1)) "case 1 every cleanup attempted")
      (check (typep c 'fnn-store-fault) "case 1 escalated to a fault")
      (let ((text (princ-to-string c)))
        (check (search "Errno 5" text) "case 1 names the cleanup failure")
        (check (search "body refused" text) "case 1 names the primary"))
      (check (= (length (car *fnn-escape-cleanup-debts*)) 1) "case 1 recorded"))))

;; 2. The primary is a fence and a cleanup faults: the fence is never masked;
;; the primary object itself propagates and the failure is recorded.
(with-fresh
  (let ((primary (make-condition 'fnn-store-indeterminate :message "outcome unknown")))
    (multiple-value-bind (values c)
        (escape-of (lambda ()
                     (fnn-unwind-cleanups ((error primary)) (failing-os))))
      (check (null values) "case 2 escaped")
      (check (eq c primary) "case 2 the primary propagates as itself")
      (check (= (length (car *fnn-escape-cleanup-debts*)) 1) "case 2 recorded")
      (check (eq (first (first (car *fnn-escape-cleanup-debts*))) primary) "case 2 debt names the primary")
      (check (= (length *err*) 1) "case 2 the dominated outcome is logged too"))))

;; 3. The primary is a fault and a cleanup refuses: the first outcome of equal
;; rank stands; the refusal is floored at a fault, so it does not outrank.
(with-fresh
  (let ((primary (make-condition 'fnn-store-fault :message "body fault")))
    (multiple-value-bind (values c)
        (escape-of (lambda ()
                     (fnn-unwind-cleanups ((error primary)) (fnn-refuse "cleanup refused"))))
      (check (and (null values) (eq c primary)) "case 3 the primary fault propagates")
      (check (= (length (car *fnn-escape-cleanup-debts*)) 1) "case 3 recorded"))))

;; 4. An exit that is no condition (a throw) with a cleanup that fails after a
;; durable step: the cleanup failure is the fence (M2), no longer swallowed.
(with-fresh
  (let ((*fnn-section-step* :replaced))
    (multiple-value-bind (values c)
        (escape-of (lambda ()
                     (catch 'tag
                       (fnn-unwind-cleanups ((throw 'tag :thrown)) (failing-os))
                       :not-reached)))
      (check (null values) "case 4 escaped")
      (check (typep c 'fnn-store-indeterminate) "case 4 the cleanup failure fences")
      (check (= (length (car *fnn-escape-cleanup-debts*)) 1) "case 4 recorded"))))

;; 5. Several cleanup failures under one escape: all recorded, the worst
;; outcome escalates once.
(with-fresh
  (multiple-value-bind (values c)
      (escape-of (lambda ()
                   (fnn-unwind-cleanups ((fnn-refuse "body refused"))
                     (fnn-refuse "first cleanup") (failing-os))))
    (declare (ignore values))
    (check (typep c 'fnn-store-fault) "case 5 escalated")
    (check (= (length (car *fnn-escape-cleanup-debts*)) 2) "case 5 both recorded")))

;; 6. No cleanup failure: the escape is untouched and nothing is recorded.
(with-fresh
  (let ((primary (make-condition 'fnn-store-error :message "plain refusal")))
    (multiple-value-bind (values c)
        (escape-of (lambda () (fnn-unwind-cleanups ((error primary)) nil)))
      (check (and (null values) (eq c primary)) "case 6 the primary propagates")
      (check (and (null (car *fnn-escape-cleanup-debts*)) (null *err*)) "case 6 nothing recorded"))))

;; 7. A condition the body handled itself is no escape: normal completion keeps
;; the body's values and signals the first cleanup failure as itself, as before.
(with-fresh
  (check (equal (multiple-value-list
                 (fnn-unwind-cleanups ((handler-case (fnn-refuse "inner") (error () (values 1 2))))
                   nil))
                '(1 2))
         "case 7 values survive")
  (multiple-value-bind (values c)
      (escape-of (lambda ()
                   (fnn-unwind-cleanups ((handler-case (fnn-refuse "inner") (error () :handled)))
                     (fnn-refuse "first") (fnn-refuse "second"))))
    (declare (ignore values))
    (check (and (typep c 'fnn-store-error) (search "first" (princ-to-string c)))
           "case 7 the first cleanup failure is signalled")
    (check (null (car *fnn-escape-cleanup-debts*)) "case 7 a completed body records no escape debt")))

(format t "Unwind cleanup escalation passed (7 cases)~%")
