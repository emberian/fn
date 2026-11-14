;;; Execute the actual pure ACL2 classifier with deliberately noncanonical IDs.
;;; This controls predicate discrimination; B certification checks its guards
;;; and the live observer/registry-derived stop index in the real world.
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(declaim (declaration xargs))
(defconstant *fn2-stop-reason-kind* 140)
(defconstant *fn2-boot-kind* 113)
(defconstant *fn2-host-boot-recovery-detail* 104)
(defconstant *fn2-recovery-machine-state-done* 106)
(defconstant *fn2-rec-class-unknown* 114)
(defconstant *fn2-rec-assume-fence* 102)
(with-open-file (source "books/host-boundary.lisp")
  (loop for form = (read source nil nil) while form
        when (and (consp form) (eq (car form) 'defun)
                  (eq (cadr form) 'fn2-host-boot-refusal-class)) do (eval form)))
(let ((positive (list t *fn2-stop-reason-kind* *fn2-boot-kind*
                      *fn2-host-boot-recovery-detail* :ok
                      *fn2-recovery-machine-state-done* *fn2-rec-class-unknown*
                      1 0 *fn2-rec-assume-fence* 0)))
  (assert (eq (apply #'fn2-host-boot-refusal-class positive) :broad-dirty-tail-unknown))
  ;; Removing any identifying condition must not retain the policy diagnosis.
  (loop for index below (length positive)
        for mutated = (copy-list positive)
        do (setf (nth index mutated) :different)
           (assert (eq (apply #'fn2-host-boot-refusal-class mutated) :other-stop))))
(format t "Boot refusal classifier: positive and all eleven distinguishing controls passed.~%")
