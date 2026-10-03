;;; What host/native/io.lisp reads from the books at load, for a raw SBCL
;;; witness that loads io.lisp outside the image (tests/test_native_*.sh):
;;; its exit-code constants call fn-outcome-code (books/outcome-class.lisp,
;;; PRF-143) and +fnn-gc-nursery-octets+ reads fn-profile-limit
;;; (books/profile-limits.lisp).  Each table is the book's own quoted
;;; constant, read from the book; each function is the book's body without
;;; its xargs (as tests/native_developer_selectors_raw.lisp does); io.lisp's
;;; exit map calls fn-outcome-host-condition-exit-code.  Five witnesses went
;;; red on this unseen (tooling-truth-2, 2026-09-29).
(in-package "ACL2")
(defun book-defconst-value (path name)
  (with-open-file (stream path)
    (loop for form = (read stream nil :eof)
          until (eq form :eof)
          when (and (consp form) (eq (car form) 'defconst) (eq (cadr form) name))
            do (return (eval (caddr form)))
          finally (error "~a: ~a not found" path name))))
;; ACL2's list primitives the book bodies below call.
(defun assoc-equal (x alist) (assoc x alist :test #'equal))
(defun member-equal (x l) (member x l :test #'equal))
(defun strip-cdrs (x) (mapcar #'cdr x))
(defun book-defuns (path names)
  "Each defun of NAMES in the book at PATH, its xargs declaration dropped,
compiled here: the book's own body, never a restatement."
  (with-open-file (stream path)
    (loop for form = (read stream nil :eof)
          until (eq form :eof)
          when (and (consp form) (eq (car form) 'defun) (member (cadr form) names))
            do (destructuring-bind (name formals &rest body) (cdr form)
                 (eval `(defun ,name ,formals
                          ,@(remove-if (lambda (f) (and (consp f) (eq (car f) 'declare)))
                                       body)))
                 (setq names (remove name names)))
          finally (when names (error "~a: ~a not found" path names)))))
(defparameter *fn-outcome-codes*
  (book-defconst-value "books/outcome-class.lisp" '*fn-outcome-codes*))
(book-defuns "books/outcome-class.lisp"
             '(fn-outcome-code fn-outcome-of-host-condition
               fn-outcome-host-condition-exit-code))
(defparameter *fn-profile-limits*
  (book-defconst-value "books/profile-limits.lisp" '*fn-profile-limits*))
(defmacro fn-profile-limit (key)
  (let ((row (assoc key *fn-profile-limits*)))
    (if row (second row) (error "~a is not a row of *fn-profile-limits*" key))))
;; An empty ACL2 world: a raw witness runs outside the image, so no entry has
;; formals (io.lisp's entry guard answers :unknown and checks nothing; the
;; image's own guard is the native modules' subject) and no entry takes a
;; stobj.  *t* and *nil* are ACL2's quoted terms; the guard-kind table is
;; the book's.
(defparameter *t* ''t)
(defparameter *nil* ''nil)
(defparameter *fn-entry-guard-kinds*
  (book-defconst-value "books/payload-kinds.lisp" '*fn-entry-guard-kinds*))
(defun w (state) (declare (ignore state)) nil)
(defun getpropc (symbol key &optional default world)
  (declare (ignore symbol key world))
  default)
(defun stobjs-in (name world) (declare (ignore name world)) nil)
;; host/native/owner.lisp's def-section declarations are accepted by ACL2 as
;; the image loads (books/failure-scope.lisp fn-fs-section-declp, lane
;; WRAPPER): the book's tables and bodies, so a raw witness that loads
;; owner.lisp loads its declarations exactly as the image does.
(defparameter *fn-fs-actors*
  (book-defconst-value "books/failure-scope.lisp" '*fn-fs-actors*))
(defparameter *fn-fs-gate-classes*
  (book-defconst-value "books/failure-scope.lisp" '*fn-fs-gate-classes*))
(defparameter *fn-fs-cleanup-purposes*
  (book-defconst-value "books/failure-scope.lisp" '*fn-fs-cleanup-purposes*))
(book-defuns "books/failure-scope.lisp"
             '(fn-fs-keyword-subsetp fn-fs-admissionp fn-fs-section-declp))
