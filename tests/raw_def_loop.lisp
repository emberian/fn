;;; Raw (plain SBCL, no ACL2) loader for def-loop-generated functions.
;;; books/def-loop.lisp is the one generator.  This file loads ITS program-mode
;;; helpers (every fn-dl- defun) and its def-loop macro textually, so a mock's
;;; (def-loop NAME) is expanded by the generator itself, never by a hand-copied
;;; defun.  Only ACL2 plumbing is stubbed: the world-reading read-only-stobj
;;; and stobj-name checks (ACL2 certified the book already), er/value/make-event/encapsulate,
;;; and the proof-only events (local defthm, verify-guards, in-theory, table),
;;; which expand to nothing.  mbe takes :exec, as the deployed image does.
;;; Loaded by tests/native_section_envelope_raw.lisp (package ACL2).

(defmacro local (&rest forms) (declare (ignore forms)) nil)
(defmacro defthm (&rest forms) (declare (ignore forms)) nil)
(defmacro verify-guards (&rest forms) (declare (ignore forms)) nil)
(defmacro in-theory (&rest forms) (declare (ignore forms)) nil)
(defmacro table (&rest forms) (declare (ignore forms)) nil)
(defmacro mbe (&key logic exec) (declare (ignore logic)) exec)
(defmacro encapsulate (sigs &rest forms) (declare (ignore sigs)) `(progn ,@forms))
(defmacro er-progn (&rest forms) `(progn ,@forms))
(defmacro value (x) `(values nil ,x state))
(defmacro er (soft ctx fmt &rest args) (declare (ignore soft))
  `(error "~a: ~?" ,ctx ,(substitute-tilde-x fmt) (list ,@args)))
(defun substitute-tilde-x (fmt)
  (let ((out (copy-seq fmt)))
    (loop for i from 0 below (1- (length out))
          when (char= (char out i) #\~)
            do (setf out (concatenate 'string (subseq out 0 i) "~"
                                      (if (digit-char-p (char out (1+ i))) "s" (string (char out (1+ i))))
                                      (subseq out (+ i 2)))))
    out))
(defmacro make-event (form)
  `(macrolet ((expand-now () (let ((state nil))
                               (multiple-value-bind (erp val) ,form
                                 (when erp (error "def-loop: ~s" erp))
                                 val))))
     (expand-now)))
(defun w (state) (declare (ignore state)) nil)
(defun getpropc (&rest args) (declare (ignore args)) nil)
(defun packn-pos (parts witness)
  (intern (format nil "~{~a~}" parts) (symbol-package witness)))
(defun strip-cars (l) (mapcar #'car l))
(defun symbol-listp (l) (and (listp l) (every #'symbolp l)))
(defun no-duplicatesp-eq (l) (= (length l) (length (remove-duplicates l))))
(defun member-eq (x l) (member x l :test #'eq))
(defun assoc-eq (x a) (assoc x a :test #'eq))
(defun subsetp-eq (a b) (subsetp a b :test #'eq))
(defun pairlis$ (x y) (loop for a in x for rest = y then (cdr rest) collect (cons a (car rest))))
(defun intersectp-eq (a b) (and (intersection a b :test #'eq) t))
(defun remove1-eq (x l) (remove x l :test #'eq :count 1))
(defun fn-dl-readonly-check (name stobjs terms state)
  (declare (ignore name stobjs terms)) (values nil nil state))
;; The stobj half of the world check: each :stobjs name is a formal (ACL2
;; certified that it names a stobj).
(defun fn-dl-stobjs-knownp (stobjs formals wrld)
  (declare (ignore wrld)) (subsetp stobjs formals :test #'eq))

(defun strip-xargs (body)
  (remove-if (lambda (f) (and (consp f) (eq (car f) 'declare) (consp (cadr f))
                              (eq (car (cadr f)) 'xargs)))
             body))

(defvar *raw-def-loop-generator-loaded* nil)
(defun raw-def-loop-load-generator ()
  (unless *raw-def-loop-generator-loaded*
    ;; the other shapes' helpers use ACL2 mv/mv-let; only :map is called here
    (handler-bind ((warning #'muffle-warning))
     (with-open-file (stream "books/def-loop.lisp")
      (loop for form = (read stream nil :eof)
            until (eq form :eof)
            do (when (consp form)
                 (cond ((and (eq (car form) 'defun)
                             (let ((n (symbol-name (cadr form))))
                               (and (> (length n) 6) (string= "FN-DL-" n :end2 6)))
                             (not (member (cadr form) '(fn-dl-readonly-check fn-dl-stobjs-knownp))))
                        (eval `(defun ,(cadr form) ,(caddr form) ,@(strip-xargs (cdddr form)))))
                       ((eq (car form) 'defmacro)
                        (when (eq (cadr form) 'def-loop) (eval form))))))))
    (setf *raw-def-loop-generator-loaded* t)))

(defun raw-def-loop-load (path name)
  "Read PATH's (def-loop NAME ...) form and evaluate it; true if found."
  (raw-def-loop-load-generator)
  (with-open-file (stream path)
    (loop for form = (read stream nil :eof)
          until (eq form :eof)
          when (and (consp form) (eq (car form) 'def-loop) (eq (cadr form) name))
            do (eval form) (return t))))
