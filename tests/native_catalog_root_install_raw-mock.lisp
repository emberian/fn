;;; Catalog-root install order, over the actual host forms fnn-install-stobj
;;; and fnn-owner-recover-core read from host/native/owner.lisp.  The ACL2
;;; seams (fnn-owner-core, fnn-owner-action) are recording doubles, so this is
;;; a -mock fixture: it checks the host's ORDER (reserve before every binding
;;; of a replacement catalog, the open's in-place load included) and is cited
;;; by no claim.  Harvest stub catalog-root-install-order (codex/night-plan
;;; 814bc2977), retargeted: the fn-hist arm detaches its history root and
;;; reserves no catalog root.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(define-condition install-fault (error) ())
(defvar *the-live-state* nil)
(defvar *fnn-cat* nil)
(defvar *fnn-hist* nil)
(defvar *trace* nil)
(defvar *tokens* nil)
(defvar *interrupt-after-reserve* nil)
(defun user-stobj-alist (state) state)
(defun fnn-fault (&rest args) (declare (ignore args)) (error 'install-fault))
(defun fnn-refuse (&rest args) (declare (ignore args)) (error 'install-fault))
(defun fnn-history-root-retire-held (root) (push (list :retire root) *trace*))
(defun fnn-store-open-mode (store) (declare (ignore store)) (list :full))
(defun fnn-store-root (store) store)
(defun fnn-call (&rest args) (declare (ignore args)) (list 0))
(defun fnn-live-arena () :arena)
(defun fnn-owner-core (name &rest args)
  (declare (ignore args))
  (push name *trace*)
  (case name
    (fn-owner-catalog-root-reserve
     ;; the binding has not happened yet: the old catalog is still live
     (assert (eq (cdr (assoc 'fn-cat *the-live-state*)) :old))
     (push (pop *tokens*) *trace*)
     (when *interrupt-after-reserve* (error 'install-fault))
     (car *trace*))
    (fn-owner-hroot-detach (list :detached :old-root))
    (t :noted)))
(defun fnn-owner-action (name &rest args)
  (declare (ignore args))
  (push name *trace*)
  ;; fn-owner-recover-from-store-open loads the catalog in place
  (setf (cdr (assoc 'fn-cat *the-live-state*)) :reloaded)
  :recovering)
(with-open-file (in "host/native/owner.lisp")
  (let ((*package* (find-package "ACL2")))
    (loop for form = (read in nil :eof) until (eq form :eof)
          when (and (consp form) (eq (car form) 'defun)
                    (member (cadr form) '(fnn-install-stobj fnn-owner-recover-core)))
            do (eval form))))
(defun reserve-before (later)
  (let ((order (reverse *trace*)))
    (let ((r (position 'fn-owner-catalog-root-reserve order))
          (l (position later order)))
      (and r l (< r l)))))
;; 1. The open's install reserves before its in-place catalog load.  Red
;; before the fix: no reservation, and a second install in one process
;; kept the first owner's token.
(let ((*the-live-state* (list (cons 'fn-cat :old) (cons 'fn-hist :h)))
      (*tokens* '((:catalog-root 0) (:catalog-root 1))) (*trace* nil))
  (fnn-owner-recover-core "store" nil 1 :entry)
  (assert (reserve-before 'fn-owner-recover-from-store-open))
  (assert (member '(:catalog-root 0) *trace* :test #'equal))
  (setf (cdr (assoc 'fn-cat *the-live-state*)) :old *trace* nil)
  (fnn-owner-recover-core "store" nil 1 :entry)
  (assert (reserve-before 'fn-owner-recover-from-store-open))
  (assert (member '(:catalog-root 1) *trace* :test #'equal)))
;; 2. The reclaim installer: an interrupted reservation leaves the live
;; catalog old; the retry reserves a distinct token, then binds.
(let ((*the-live-state* (list (cons 'fn-cat :old) (cons 'fn-hist :h)))
      (*tokens* '((:catalog-root 3) (:catalog-root 4))) (*trace* nil) (*fnn-cat* :old))
  (let ((*interrupt-after-reserve* t))
    (assert (handler-case (progn (fnn-install-stobj 'fn-cat :new) nil)
              (install-fault () t))))
  (assert (eq (cdr (assoc 'fn-cat *the-live-state*)) :old))
  (assert (eq *fnn-cat* :old))
  (fnn-install-stobj 'fn-cat :new)
  (assert (eq (cdr (assoc 'fn-cat *the-live-state*)) :new))
  (assert (eq *fnn-cat* :new))
  (assert (and (member '(:catalog-root 3) *trace* :test #'equal)
               (member '(:catalog-root 4) *trace* :test #'equal))))
;; 3. The fn-hist arm detaches its root, retires it, reserves no catalog root.
(let ((*the-live-state* (list (cons 'fn-cat :old) (cons 'fn-hist :h)))
      (*tokens* nil) (*trace* nil))
  (fnn-install-stobj 'fn-hist :new-history)
  (assert (eq *fnn-hist* :new-history))
  (assert (not (member 'fn-owner-catalog-root-reserve *trace*)))
  (assert (member '(:retire :old-root) *trace* :test #'equal)))
;; 4. An image without the catalog stobj refuses before any reservation.
(let ((*the-live-state* (list (cons 'fn-hist :h))) (*trace* nil))
  (assert (handler-case (progn (fnn-install-stobj 'fn-cat :absent) nil)
            (install-fault () t)))
  (assert (not (member 'fn-owner-catalog-root-reserve *trace*))))
(format t "CATALOG-ROOT-INSTALL-MOCK PASS~%")
