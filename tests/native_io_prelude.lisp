;;; What host/native/io.lisp reads from the books at load, for a raw SBCL
;;; witness that loads io.lisp outside the image (tests/test_native_*.sh):
;;; its exit-code constants call fn-outcome-code (books/outcome-class.lisp,
;;; PRF-143) and +fnn-gc-nursery-octets+ reads fn-profile-limit
;;; (books/profile-limits.lisp).  Each table is the book's own quoted
;;; constant, read from the book; each function is the book's body without
;;; its xargs (as tests/native_developer_selectors_raw.lisp does).  Five
;;; witnesses went red on this unseen (tooling-truth-2, 2026-09-29).
(in-package "ACL2")
(defun book-defconst-value (path name)
  (with-open-file (stream path)
    (loop for form = (read stream nil :eof)
          until (eq form :eof)
          when (and (consp form) (eq (car form) 'defconst) (eq (cadr form) name))
            do (return (eval (caddr form)))
          finally (error "~a: ~a not found" path name))))
(defparameter *fn-outcome-codes*
  (book-defconst-value "books/outcome-class.lisp" '*fn-outcome-codes*))
(defun fn-outcome-code (class)
  (let ((pair (assoc class *fn-outcome-codes* :test #'equal)))
    (if (consp pair) (cdr pair) 3)))
(defparameter *fn-profile-limits*
  (book-defconst-value "books/profile-limits.lisp" '*fn-profile-limits*))
(defmacro fn-profile-limit (key)
  (let ((row (assoc key *fn-profile-limits*)))
    (if row (second row) (error "~a is not a row of *fn-profile-limits*" key))))
