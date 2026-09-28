;;; tools/extract/clruntime.lisp -- the hand runtime of the Common Lisp
;;; product (lane extract-writable; A-TARGET-COMPILER, specs/failures.md):
;;; the few ACL2 runtime names the extracted definitions (tools/extract/cl.py)
;;; and host/native's raw Lisp call, over this process's own objects.  No
;;; ACL2: no world, no prover, no *1* machinery beyond what cl.py emits.
;;; Everything here is in the trust boundary beside the compiler.
(in-package "ACL2")

(defparameter *the-live-state* (intern "The Live State Itself" "ACL2_INVISIBLE"))

;;; --- state globals: ACL2's f-get-global/f-put-global over a table whose
;;; initial values are the image's at extraction (core-world.lisp) -----------
(defvar *xl-globals* (make-hash-table :test 'eq :synchronized t))
(defun xl-set-global (sym value) (setf (gethash sym *xl-globals*) value))
(defun f-get-global (sym state)
  (declare (ignore state))
  (multiple-value-bind (v found) (gethash sym *xl-globals*)
    (if found v (error "ACL2 state global ~s is unbound in this core" sym))))
(defun get-global (sym state) (f-get-global sym state))
(defun f-put-global (sym value state)
  (declare (ignore state))
  (setf (gethash sym *xl-globals*) value)
  *the-live-state*)
(defun put-global (sym value state) (f-put-global sym value state))
(defun f-boundp-global (sym state)
  (declare (ignore state))
  (nth-value 1 (gethash sym *xl-globals*)))
(defun boundp-global (sym state) (f-boundp-global sym state))

;;; --- the world: the properties host/native reads of an entry
;;; (fnn-entry-guard-spec, fnn-trailing-kind), the image's values -----------
(defvar *xl-props* (make-hash-table :test 'eq))
(defun xl-set-props (rows)
  (dolist (r rows)
    (setf (gethash (first r) *xl-props*)
          (list :formals (second r) :stobjs-in (third r) :guard (fourth r)))))
(defun w (state) (declare (ignore state)) :xl-world)
(defun getpropc (sym prop &optional default wrld)
  (declare (ignore wrld))
  (let ((p (gethash sym *xl-props*)))
    (if p
        (case prop
          (formals (getf p :formals))
          (stobjs-in (getf p :stobjs-in))
          (guard (getf p :guard))
          (t default))
        default)))
(defun stobjs-in (fn wrld)
  (declare (ignore wrld))
  (getpropc fn 'stobjs-in nil))

;;; --- the live stobjs (cl.py's xl-make-live-stobjs fills this at start) ----
(defvar *xl-user-stobj-alist* nil)
(defun user-stobj-alist (state) (declare (ignore state)) *xl-user-stobj-alist*)

;;; --- ACL2's error path.  A guard violation or hard error inside an entry
;;; halts it; host/native's fnn-call catches the throw and reports the fault
;;; `ACL2 error in ENTRY: ACL2 Halted' (exit :fault), as in the image. -------
(defun xl-halt () (throw 'raw-ev-fncall "ACL2 Halted"))
(defun xl-guard-violation (fn args)
  (declare (ignore args))
  (format *error-output* "ACL2 Error in ACL2-INTERFACE:  The guard for the function call (~a ...) is violated by the arguments in the call.~%" fn)
  (xl-halt))
(defun hard-error (ctx str alist)
  (declare (ignore alist))
  (format *error-output* "HARD ACL2 ERROR in ~a:  ~a~%" ctx str)
  (xl-halt))
(defun illegal (ctx str alist) (hard-error ctx str alist))
(defun throw-nonexec-error (fn actuals)
  (declare (ignore actuals))
  (hard-error fn "a non-executable function was called" nil))
(defun fmt-to-comment-window (&rest r) (declare (ignore r)) nil)
(defun fmt-to-comment-window! (&rest r) (declare (ignore r)) nil)
(defun fmt-to-comment-window+ (&rest r) (declare (ignore r)) nil)
(defun fmt-to-comment-window!+ (&rest r) (declare (ignore r)) nil)
(defun cw-print-base-radix (&rest r) (declare (ignore r)) nil)

;;; --- ACL2's total primitives, for :ideal bodies and *1* bodies ----------
(declaim (inline xl-car xl-cdr xl-+ xl-* xl-neg xl-<))
(defun xl-car (x) (if (consp x) (car x) nil))
(defun xl-cdr (x) (if (consp x) (cdr x) nil))
(defun xl-fix (x) (if (numberp x) x 0))
(defun xl-rfix (x) (if (rationalp x) x 0))
(defun xl-+ (x y) (+ (xl-fix x) (xl-fix y)))
(defun xl-* (x y) (* (xl-fix x) (xl-fix y)))
(defun xl-neg (x) (- (xl-fix x)))
(defun xl-recip (x) (let ((x (xl-fix x))) (if (eql x 0) 0 (/ x))))
(defun xl-< (x y)
  (let ((x (xl-fix x)) (y (xl-fix y)))
    (if (and (rationalp x) (rationalp y))
        (< x y)
        (let ((a (realpart x)) (b (realpart y)))
          (or (< a b) (and (= a b) (< (imagpart x) (imagpart y))))))))
(defun xl-char-code (x) (if (characterp x) (char-code x) 0))
(defun xl-code-char (x) (if (and (integerp x) (<= 0 x 255)) (code-char x) (code-char 0)))
(defun xl-numerator (x) (if (rationalp x) (numerator x) 0))
(defun xl-denominator (x) (if (rationalp x) (denominator x) 1))
(defun xl-realpart (x) (if (numberp x) (realpart x) 0))
(defun xl-imagpart (x) (if (numberp x) (imagpart x) 0))
(defun xl-complex (x y) (complex (xl-rfix x) (xl-rfix y)))
(defun xl-complex-rationalp (x) (and (complexp x) t))
(defun xl-symbol-name (x) (if (symbolp x) (symbol-name x) ""))
(defun xl-symbol-package-name (x)
  (if (symbolp x) (package-name (symbol-package x)) ""))
(defun xl-intern-in-package-of-symbol (str sym)
  (if (and (stringp str) (symbolp sym)) (values (intern str (symbol-package sym))) nil))
(defun xl-coerce (x y)
  (cond ((eq y 'list) (if (stringp x) (coerce x 'list) nil))
        (t (coerce (loop for c in (if (listp x) x nil) collect (if (characterp c) c (code-char 0)))
                   'string))))
(defun xl-bad-atom<= (x y)
  ;; ACL2's order on bad atoms; none reaches an extracted body
  (declare (ignore x y))
  (hard-error 'bad-atom<= "no bad atoms in this core" nil))

;;; --- a resizable stobj array (ACL2's resize: the old contents, then FILL) --
(defun xl-resize (old k fill)
  (let* ((new (make-array k :element-type (array-element-type old))))
    (dotimes (i k new)
      (setf (aref new i) (if (< i (length old)) (aref old i) (funcall fill))))))

;;; --- ACL2 built-ins with Common Lisp raw definitions: their total (logic)
;;; forms for :ideal and *1* bodies, and LEN's (a loop: the logical
;;; definition recurses once per cons) ----------------------------------------
(defun xl-ifix (x) (if (integerp x) x 0))
(defun xl-logand (x y) (logand (xl-ifix x) (xl-ifix y)))
(defun xl-logior (x y) (logior (xl-ifix x) (xl-ifix y)))
(defun xl-logxor (x y) (logxor (xl-ifix x) (xl-ifix y)))
(defun xl-logeqv (x y) (logeqv (xl-ifix x) (xl-ifix y)))
(defun xl-lognot (x) (lognot (xl-ifix x)))
(defun xl-ash (x y) (ash (xl-ifix x) (xl-ifix y)))
(defun xl-len (x) (loop for tail = x then (cdr tail) while (consp tail) count t))
