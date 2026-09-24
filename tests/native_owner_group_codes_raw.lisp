;;; A rejected owner group lookup must become a completed refusal word.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

;; The deployed forms this boundary runs: the Store condition hierarchy from
;; io.lisp (the attempt handlers classify by it, including the p2-wire
;; fnn-store-io-refusal), then the attempt-handler macro and the attempt itself
;; from owner.lisp.  Each named form must be found, so a rename fails here
;; rather than leaving a stale stub in its place.
(defun load-deployed-forms (path wanted)
  (let ((missing (copy-list wanted)))
    (with-open-file (stream path)
      (loop for form = (read stream nil :eof)
            until (eq form :eof)
            when (and (consp form)
                      (member (car form) '(defun defmacro define-condition))
                      (member (list (car form) (cadr form)) wanted :test #'equal))
              do (eval form)
                 (setf missing (remove (list (car form) (cadr form)) missing
                                       :test #'equal))))
    (when missing (error "deployed forms missing from ~a: ~s" path missing))))

(load-deployed-forms "host/native/io.lisp"
                     '((define-condition fnn-store-error)
                       (define-condition fnn-store-fault)
                       (define-condition fnn-store-indeterminate)
                       (define-condition fnn-store-io-refusal)
                       (define-condition fnn-os-error)))
(defvar *calls* nil)
(defvar *bad-group* t)
(defvar *bad-charge* nil)
(defun fnn-owner-service-store (service) (declare (ignore service)) :store)
(defun fnn-charge (length)
  (declare (ignore length))
  (if *bad-charge* (error 'fnn-store-error :message "stub charge") 1))
(defun fnn-octet-list (x) x)
(defun fnn-owner-core (name &rest args)
  (push (cons name args) *calls*)
  (case name (fn-owner-group-codes (if *bad-group* :bad '(0)))
        (otherwise (error "unexpected ACL2 call ~s" name))))
(defun fnn-refuse (&rest args) (declare (ignore args)) (error 'fnn-store-error :message "stub"))
;; Reached only on the fault and unclassified-OS paths, which these cases
;; must not take: record it so a wrong classification is visible.
(defvar *fenced* nil)
(defun (setf fnn-store-fenced) (value store) (push (cons store value) *fenced*) value)
(defun fnn-err (&rest args) (push (cons 'fnn-err args) *calls*))

(load-deployed-forms "host/native/owner.lisp"
                     '((defmacro fnn-owner-attempt-handlers)
                       (defun fnn-owner-attempt)))

(unless (eq (fnn-owner-attempt :service '(1) '(2) '((102 110 46 108 105 118 101)) '(3))
            :refused)
  (error "unknown group escaped before the Store-attempt refusal handler"))
(unless (equal (reverse *calls*)
               '((fn-owner-group-codes ((102 110 46 108 105 118 101)))))
  (error "owner lookup did not use current ACL2 allocation domain: ~s"
         (reverse *calls*)))
(setq *bad-group* nil *bad-charge* t *calls* nil)
(unless (eq (fnn-owner-attempt :service '(1) '(2) '((102 110 46 116 101 115 116)) '(3))
            :refused)
  (error "charge preflight escaped before the Store-attempt refusal handler"))
(unless (equal (reverse *calls*)
               '((fn-owner-group-codes ((102 110 46 116 101 115 116)))))
  (error "charge refusal did not follow the ACL2 owner group lookup"))
(when *fenced*
  (error "a refused attempt fenced the store: ~s" *fenced*))
(format t "native owner group-code boundary passed~%")
