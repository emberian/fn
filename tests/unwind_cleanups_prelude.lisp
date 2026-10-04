;;; The deployed escape-path half of fnn-unwind-cleanups for a raw harness that
;;; evaluates the macro (host/native/io.lisp, or FN_CLEANUP_HOST_SOURCE): the
;;; helper fnn-escape-cleanup-failed with the ACL2 decisions it calls
;;; (books/failure-scope.lisp, books/outcome-class.lisp) and the observations
;;; they read, so that a cleanup failing while a body escapes is classified
;;; exactly as the host classifies it.  Load it after the harness's own stubs
;;; (fnn-err, and fnn-fault / fnn-indeterminate when a case lets a cleanup
;;; outrank its escape); it defines none of them.  Not a harness itself.
(require :sb-posix)
(require :sb-bsd-sockets)
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
(defun fnn-concat (&rest strings)
  (declare (ignorable strings))
  (harness-stub-reached 'fnn-concat "host/native/io.lisp"))
(defun fnn-emit (stream text)
  (declare (ignorable stream text))
  (harness-stub-reached 'fnn-emit "host/native/io.lisp"))
(defun fnn-log-offer (destination octets)
  (declare (ignorable destination octets))
  (harness-stub-reached 'fnn-log-offer "host/native/io.lisp"))
(defun fnn-string-octets (string)
  (declare (ignorable string))
  (harness-stub-reached 'fnn-string-octets "host/native/io.lisp"))
;;; ---- derived stubs: END ----
(declaim (declaration xargs))
(unless (fboundp 'member-equal) (defun member-equal (x l) (member x l :test #'equal)))
(unless (fboundp 'assoc-equal) (defun assoc-equal (x l) (assoc x l :test #'equal)))
(unless (fboundp 'strip-cdrs) (defun strip-cdrs (alist) (mapcar #'cdr alist)))

(defun unwind-prelude-load-forms (path wanted &key optional)
  "Evaluate PATH's top-level forms named by WANTED, (KIND NAME) each; a book's
defconst becomes a defparameter and its defun loses its xargs declaration.
OPTIONAL forms may be absent (a red run's origin/next has no helper)."
  (let ((missing (copy-list wanted)))
    (with-open-file (stream path)
      (loop for form = (read stream nil :eof)
            until (eq form :eof)
            when (and (consp form)
                      (member (list (car form) (cadr form)) wanted :test #'equal))
              do (eval (case (car form)
                         (defconst (cons 'defparameter (cdr form)))
                         (defun (destructuring-bind (name formals &rest body) (cdr form)
                                  `(defun ,name ,formals
                                     ,@(remove-if (lambda (f) (and (consp f) (eq (car f) 'declare)
                                                                   (consp (cadr f))
                                                                   (eq (car (cadr f)) 'xargs)))
                                                  body))))
                         (t form)))
                 (setf missing (remove (list (car form) (cadr form)) missing :test #'equal))))
    (when (and missing (not optional)) (error "deployed forms missing from ~a: ~s" path missing))))

(unwind-prelude-load-forms
 "books/outcome-class.lisp"
 '((defconst *fn-outcome-codes*) (defun fn-outcome-code)
   (defun fn-outcome-of-host-condition) (defun fn-outcome-host-condition-exit-code)))
(unwind-prelude-load-forms
 "books/failure-scope.lisp"
 '((defconst *fn-fs-indeterminate-classes*) (defconst *fn-fs-fault-classes*)
   (defconst *fn-fs-usage-classes*) (defconst *fn-fs-refusal-classes*)
   (defconst *fn-fs-os-classes*) (defun fn-fs-classify) (defun fn-fs-exit-code)
   (defun fn-fs-stop-exit-rank) (defun fn-fs-stop-exit-escalate)))
(defvar +fnn-exit-ok+ (fn-outcome-code :accepted))
(defvar +fnn-exit-refused+ (fn-outcome-code :refused))
(defvar +fnn-exit-uncertain+ (fn-outcome-code :fenced))
(defvar +fnn-exit-fault+ (fn-outcome-code :fault))
(defvar *unwind-prelude-io-source*
  (or (sb-ext:posix-getenv "FN_CLEANUP_HOST_SOURCE") "host/native/io.lisp"))
(unwind-prelude-load-forms
 *unwind-prelude-io-source*
 '((defvar *fnn-section-step*) (defun fnn-condition-class) (defun fnn-exit-code-for)))
;; Absent from a tree before the escalation: the stubs a harness already
;; defines then stand for the swallow, which is what a red run shows.
(unwind-prelude-load-forms
 *unwind-prelude-io-source*
 '((defvar *fnn-escape-cleanup-debts*) (defun fnn-escape-cleanup-failed))
 :optional t)
