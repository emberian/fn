;;; Exercise the deployed consumer publication wrapper with recording Store
;;; stubs.  ACL2 constructs the event; this test observes only the native
;;; reservation/preparation/publication boundary and its refusal cut.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

;; The deployed forms this boundary runs, loaded by name so a rename fails
;; here rather than leaving a stale stub in its place.  Since m5-capacity
;; (ce27b18d) the host holds no count and no bound: the capacity refusal is
;; the owner's verdict, asked by the deployed fnn-owner-preflight-publication
;; (host/native/owner.lisp) through fn-owner-publication-verdict
;; (host/owner-host.lisp), whose word is books/store-budget.lisp
;; fn-sbud-verdict's.  Both are loaded here; only the ACL2 call is recorded.
(defun load-deployed-forms (path wanted)
  (let ((missing (copy-list wanted)))
    (with-open-file (stream path)
      (loop for form = (read stream nil :eof)
            until (eq form :eof)
            when (and (consp form)
                      (member (car form) '(defun defmacro defvar define-condition))
                      (member (list (car form) (cadr form)) wanted :test #'equal))
              do (eval form)
                 (setf missing (remove (list (car form) (cadr form)) missing
                                       :test #'equal))))
    (when missing (error "deployed forms missing from ~a: ~s" path missing))))

(defun read-acl2-defun (path name)
  "The form (defun NAME ...) of the ACL2 file PATH, read, never evaluated."
  (with-open-file (stream path)
    (loop for form = (read stream nil :eof)
          until (eq form :eof)
          when (and (consp form) (eq (car form) 'defun) (eq (cadr form) name))
            do (return form)
          finally (error "~a has no defun ~a" path name))))

(defun tree-mentions (tree atom)
  (or (eq tree atom)
      (and (consp tree) (or (tree-mentions (car tree) atom)
                            (tree-mentions (cdr tree) atom)))))

(defun keyword-leaves (tree)
  (cond ((keywordp tree) (list tree))
        ((consp tree) (append (keyword-leaves (car tree)) (keyword-leaves (cdr tree))))
        (t nil)))

;; ACL2's verdict words.  The host's verdict call is fn-sbud-verdict-at's, and
;; fn-sbud-verdict-at answers :admissible below the budget and one other word at
;; or over it; that word is the one the owner hands the host at capacity.
(defparameter *verdict-words*
  (let ((host (read-acl2-defun "host/owner-host.lisp" 'fn-owner-publication-verdict))
        (book (read-acl2-defun "books/store-budget.lisp" 'fn-sbud-verdict-at)))
    (unless (tree-mentions (cdddr host) 'fn-sbud-verdict-at)
      (error "fn-owner-publication-verdict no longer answers fn-sbud-verdict-at's word"))
    (let ((words (remove :guard (remove-duplicates (keyword-leaves (car (last book)))))))
      (unless (and (= (length words) 2) (member :admissible words))
        (error "fn-sbud-verdict-at's words changed: ~s" words))
      words)))
(defparameter *at-capacity* (car (remove :admissible *verdict-words*)))

(defvar *fnn-observe-callback* nil)
(defvar *fnn-finish-callback* nil)
(defvar *calls* nil)
(defvar *prepare-result* :prepared)
(defvar *verdict* :admissible)
(defstruct mock-service store)
(define-condition consumer-refusal (error) ())
(defun fnn-refuse (&rest args) (declare (ignore args)) (error 'consumer-refusal))
(defun fnn-indeterminate (&rest args) (declare (ignore args))
  (error "indeterminate consumer publication"))
(defun fnn-owner-service-store (service) (mock-service-store service))
(defun fnn-owner-observe (&rest args) (declare (ignore args)) nil)
(defun fnn-owner-finish (&rest args) (declare (ignore args)) nil)
(defun fnn-owner-core (name &rest args)
  (push (list* :core name args) *calls*)
  (case name
    (fn-owner-publication-verdict *verdict*)
    (fn-owner-next-txid 7)
    (otherwise (error "wrong core call ~s" name))))
(defun fnn-nat (x) (unless (and (integerp x) (<= 0 x)) (error "not nat")) x)
(defun fnn-advance-frontier (store txid)
  (declare (ignore store)) (push (list :advance txid) *calls*) :advanced)
(defun fnn-owner-action (name &rest args)
  (push (cons :action (cons name args)) *calls*)
  (ecase name
    (fn-owner-prepare-consumer *prepare-result*)
    (fn-owner-refuse-reservation :refused)))
(defun fnn-owner-publish-prepared (service label)
  (declare (ignore service)) (push (list :publish label) *calls*) :durable)

(load-deployed-forms "host/native/owner.lisp"
                     '((defun fnn-owner-preflight-publication)
                       (defun fnn-owner-consumer-commit)))

(defun check (condition description)
  (unless condition (error "~a" description)))

(let* ((event '(:consumer :opaque-acl2-event))
       (service (make-mock-service :store :store)))
  (setf *calls* nil *prepare-result* :prepared)
  (check (eq (fnn-owner-consumer-commit service event) :durable)
         "prepared event did not become durable")
  (check (equal (reverse *calls*)
                (list '(:core fn-owner-publication-verdict :consumer)
                      '(:core fn-owner-next-txid)
                      '(:advance 7)
                      (list :action 'fn-owner-prepare-consumer event)
                      '(:publish "consumer")))
         "consumer publication call order or event identity changed")

  (setf *calls* nil *prepare-result* :refused)
  (handler-case (progn (fnn-owner-consumer-commit service event)
                       (error "refused event published"))
    (consumer-refusal () nil))
  (check (equal (reverse *calls*)
                (list '(:core fn-owner-publication-verdict :consumer)
                      '(:core fn-owner-next-txid)
                      '(:advance 7)
                      (list :action 'fn-owner-prepare-consumer event)
                      '(:action fn-owner-refuse-reservation)))
         "refused reservation was not consumed before refusal")

  ;; At capacity the owner's verdict is fn-sbud-verdict's refusing word: the
  ;; deployed preflight refuses on it before a transaction id is taken, the
  ;; frontier advanced or anything prepared.
  (setf *verdict* *at-capacity* *prepare-result* :prepared *calls* nil)
  (handler-case (progn (fnn-owner-consumer-commit service event)
                       (error "capacity refusal missed"))
    (consumer-refusal () nil))
  (check (equal (reverse *calls*)
                '((:core fn-owner-publication-verdict :consumer)))
         "capacity refusal advanced the frontier or was not the owner's verdict"))
(format t "native owner consumer boundary passed~%")
