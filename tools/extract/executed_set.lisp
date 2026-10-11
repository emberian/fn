;; tools/extract/executed_set.lisp -- the executed-set instrument (the measured
;; collapse, CORE-CENSUS-20261010.md; first written by Builder A as the census's
;; instrument.lisp).  A developer fn-core loads it through XL_HOOK=FILE
;; (core-main.lisp, package ACL2, before fn starts); executed_set.py drives the
;; workloads and reads what it writes.  A production core refuses XL_HOOK.
;;
;; Every global function the core carries outside SBCL's own packages is
;; encapsulated with a recorder.  The first call of a function in a process
;; appends its name to $FN_XC_OUT/<pid>.txt at once, under a lock, and forces
;; the line out, so a process ended by SIGKILL (the crash cases) keeps what it
;; ran.  What the recorder cannot see is written beside it, never dropped:
;;   <pid>.unobserved  each name that is not wrapped -- the raw-dispatch entries
;;                     (their dispatcher applies a captured object, so a call
;;                     never reaches the fdefinition), fnn-exit, and any name
;;                     whose encapsulation failed (with the condition);
;;   <pid>.wrapped     the count of wrapped names, written after wrapping.
;; executed_set.py counts every unobserved name as executed.  Calls SBCL
;; compiled as local or inline never reach a global entry either; the census
;; answers those by the static closure (a unit is removable only when every
;; static caller is itself never executed).
(defvar cl-user::*xc-dir* (sb-ext:posix-getenv "FN_XC_OUT"))
(defvar cl-user::*xc-lock* (sb-thread:make-mutex :name "executed-set"))
(defvar cl-user::*xc-stream* nil)

(defun cl-user::xc-path (kind)
  (format nil "~A/~D.~A" cl-user::*xc-dir* (sb-unix:unix-getpid) kind))

(defun cl-user::xc-line (stream name)
  (let ((*package* (find-package :keyword)) (*print-pretty* nil) (*print-readably* nil))
    (prin1 name stream) (terpri stream)))

(defun cl-user::xc-record (name)
  (sb-thread:with-mutex (cl-user::*xc-lock*)
    (unless cl-user::*xc-stream*
      (setf cl-user::*xc-stream*
            (open (cl-user::xc-path "txt") :direction :output :if-exists :append
                                           :if-does-not-exist :create)))
    (cl-user::xc-line cl-user::*xc-stream* name)
    (finish-output cl-user::*xc-stream*)))

(unless (and cl-user::*xc-dir* (plusp (length cl-user::*xc-dir*)))
  (format *error-output* "executed_set.lisp: FN_XC_OUT is not set~%")
  (sb-ext:exit :code 6 :abort t))

(let ((names nil) (unobserved nil) (skip (make-hash-table :test 'eq)) (wrapped 0))
  (dolist (nm (acl2::fnn-raw-dispatch-names))
    (setf (gethash nm skip) "raw-dispatch entry")
    (setf (gethash (acl2::fnn-dispatch-symbol nm) skip) "raw-dispatch target"))
  (setf (gethash 'acl2::fnn-exit skip) "the exit path")
  (do-all-symbols (s)
    (let ((p (symbol-package s)))
      (when (and p (not (eql 0 (search "SB-" (package-name p))))
                 (not (member (package-name p) '("COMMON-LISP" "KEYWORD" "COMMON-LISP-USER")
                              :test #'string=))
                 (fboundp s) (not (macro-function s)) (not (special-operator-p s)))
        (push s names))))
  (setf names (remove-duplicates names))
  (dolist (s names)
    (let ((reason (gethash s skip)))
      (if reason
          (push (cons s reason) unobserved)
          (let ((seen nil) (name s))
            (handler-case
                (progn
                  (sb-int:encapsulate
                   s 'executed-set
                   (lambda (f &rest args)
                     (unless seen
                       (setf seen t)
                       (cl-user::xc-record name))
                     (apply f args)))
                  (incf wrapped))
              (error (c) (push (cons s (princ-to-string c)) unobserved)))))))
  (with-open-file (o (cl-user::xc-path "unobserved") :direction :output :if-exists :supersede)
    (dolist (u unobserved)
      (cl-user::xc-line o (car u))
      (format o ";; ~A~%" (substitute #\Space #\Newline (cdr u)))))
  (with-open-file (o (cl-user::xc-path "wrapped") :direction :output :if-exists :supersede)
    (format o "~D~%" wrapped)))
