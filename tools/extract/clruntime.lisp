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
(defvar *xl-world-snapshot-loaded-p* nil)
(defun xl-set-world-snapshot (rows)
  "Install property pairs exported from the selected ACL2 world.
Presence is distinct from a present NIL value; no classes are inferred here."
  (clrhash *xl-props*)
  (dolist (row rows)
    (setf (gethash (car row) *xl-props*) (cdr row)))
  (setf *xl-world-snapshot-loaded-p* t))
(defun xl-set-props (rows)
  (setf *xl-world-snapshot-loaded-p* nil)
  (clrhash *xl-props*)
  (dolist (r rows)
    (setf (gethash (first r) *xl-props*)
          (list :formals (second r) :stobjs-in (third r) :guard (fourth r)))))
(defun w (state) (declare (ignore state)) :xl-world)
(defun getpropc (sym prop &optional default wrld)
  (declare (ignore wrld))
  (let ((p (gethash sym *xl-props*)))
    (if *xl-world-snapshot-loaded-p*
        (let ((entry (assoc prop p :test #'eq)))
          (if entry (cdr entry) default))
      (if p
        (case prop
          (formals (getf p :formals))
          (stobjs-in (getf p :stobjs-in))
          (guard (getf p :guard))
          (t default))
        default))))
(defun symbol-class (sym wrld)
  (getpropc sym 'symbol-class :missing-world-metadata wrld))
(defun stobjs-out (sym wrld)
  (getpropc sym 'stobjs-out :missing-world-metadata wrld))
(defun guard (sym ignored wrld)
  (declare (ignore ignored))
  (getpropc sym 'guard :missing-world-metadata wrld))
(defun table-alist (sym wrld)
  (unless *xl-world-snapshot-loaded-p*
    (error "Selected ACL2 world snapshot is unavailable"))
  (unless (assoc 'table-alist (gethash sym *xl-props*) :test #'eq)
    (error "Selected ACL2 table metadata is unavailable for ~s" sym))
  (getpropc sym 'table-alist nil wrld))
(defun get-stobj-creator (sym wrld)
  (getpropc sym :xl-stobj-creator nil wrld))
(defun get-stobj-recognizer (sym wrld)
  (getpropc sym :xl-stobj-recognizer nil wrld))
(defun get-event (sym wrld)
  (getpropc sym :xl-stobj-event nil wrld))
(defun fgetprop (sym prop default wrld)
  (getpropc sym prop default wrld))
(defun sgetprop (sym prop default world-name wrld)
  (unless (eq world-name 'current-acl2-world)
    (error "Only the selected current ACL2 world is exported"))
  (getpropc sym prop default wrld))
(defun stobjs-in (fn wrld)
  (declare (ignore wrld))
  (getpropc fn 'stobjs-in nil))

;;; --- the live stobjs (cl.py's xl-make-live-stobjs fills this at start) ----
(defvar *xl-user-stobj-alist* nil)
(defvar *xl-stobj-table-keys* (make-hash-table :test 'eq))
(defun xl-make-stobj-table (size &optional rehash-size rehash-threshold)
  (apply #'make-hash-table :test 'eq
         (append (and size (list :size size))
                 (and rehash-size (list :rehash-size rehash-size))
                 (and rehash-threshold (list :rehash-threshold rehash-threshold)))))
(defun xl-register-stobj-names (names)
  ;; The extracted served world is immutable: it has no ACL2 undo/redefinition
  ;; operation. Distinct congruent names retain distinct registry identities.
  (dolist (name names)
    (unless (gethash name *xl-stobj-table-keys*)
      (setf (gethash name *xl-stobj-table-keys*) (gensym (symbol-name name)))))
  nil)
(defun xl-stobj-table-key (name)
  (or (gethash name *xl-stobj-table-keys*)
      (error "stobj-table key is not in the extracted stobj registry: ~s" name)))
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
(defun xl-string-append (a b)
  (concatenate 'string (if (stringp a) a "") (if (stringp b) b "")))
(defun xl-niq (i j)
  (if (and (integerp i) (integerp j) (< 0 j) (<= 0 i)) (floor i j) 0))

;;; --- ACL2 list built-ins as loops: each equal to the logical definition on
;;; every input (an atom ends a list, as endp reads it) ------------------------
(defun xl-append (x y)
  (let ((acc nil))
    (loop while (consp x) do (push (car x) acc) (setq x (cdr x)))
    (let ((out y)) (dolist (e acc out) (setq out (cons e out))))))
(defun xl-strip-cars (x)
  (loop for tail = x then (cdr tail) while (consp tail) collect (xl-car (car tail))))
(defun xl-strip-cdrs (x)
  (loop for tail = x then (cdr tail) while (consp tail) collect (xl-cdr (car tail))))
(defun xl-true-list-fix (x)
  (loop for tail = x then (cdr tail) while (consp tail) collect (car tail)))
(defun xl-member-equal (x l)
  (loop for tail = l then (cdr tail) while (consp tail)
        when (equal x (car tail)) return tail))
(defun xl-remove-duplicates-equal (l)
  (loop for tail = l then (cdr tail) while (consp tail)
        unless (xl-member-equal (car tail) (cdr tail)) collect (car tail)))
(defun xl-intersection-equal (l1 l2)
  (loop for tail = l1 then (cdr tail) while (consp tail)
        when (xl-member-equal (car tail) l2) collect (car tail)))
(defun xl-string-append-lst (x)
  (apply #'concatenate 'string
         (loop for tail = x then (cdr tail) while (consp tail)
               collect (if (stringp (car tail)) (car tail) ""))))

;;; --- fast alists: ACL2's hons-get/hons-acons/make-fast-alist/
;;; fast-alist-free over a hash table (small-rows-a8's ask, 2026-09-29).
;;; Emitted from their logical definitions they walked the alist
;;; (hons-assoc-equal), so an index built with them (A8's, expiry's expired
;;; set) was linear per lookup in this core.  The alist stays the value, as
;;; ACL2's logic says; the table accelerates lookups on the newest version
;;; only, as in ACL2: hons-acons moves the table from ALIST to the new cons,
;;; so an older version is walked (still the logical answer).  The side
;;; table is weak on the alist, so a dropped alist frees its table without
;;; fast-alist-free.  Keys are hashed over their whole structure: SBCL's
;;; sxhash on a list reads a few elements, and octet-list keys sharing a
;;; prefix would all collide.
(defun xl-hons-hash (x)
  (let ((h 0) (stack (list x)))
    (declare (type (unsigned-byte 62) h))
    (loop while stack
          do (let ((y (pop stack)))
               (if (consp y)
                   (progn (push (cdr y) stack) (push (car y) stack)
                          (setf h (logand (+ (* h 31) 7) #x3fffffffffffffff)))
                   (setf h (logand (+ (* h 31) (sxhash y)) #x3fffffffffffffff)))))
    h))
(defun xl-hons-equal (x y) (equal x y))
(sb-ext:define-hash-table-test xl-hons-equal xl-hons-hash)
(defvar *xl-fast-alists*
  (make-hash-table :test 'eq :weakness :key :synchronized t))
(defun xl-fast-table (alist)
  "ALIST's table, built from ALIST (first binding of each key wins, as
hons-assoc-equal reads it) when it has none."
  (or (gethash alist *xl-fast-alists*)
      (let ((table (make-hash-table :test 'xl-hons-equal)))
        (loop for tail = alist then (cdr tail)
              while (consp tail)
              do (let ((pair (car tail)))
                   (when (and (consp pair)
                              (not (nth-value 1 (gethash (car pair) table))))
                     (setf (gethash (car pair) table) pair))))
        (unless (atom alist)
          (setf (gethash alist *xl-fast-alists*) table))
        table)))
(defun hons-assoc-equal-walk (key alist)
  (loop for tail = alist then (cdr tail)
        while (consp tail)
        do (let ((pair (car tail)))
             (when (and (consp pair) (equal key (car pair)))
               (return pair)))))
(defun hons-get (key alist)
  (let ((table (and (consp alist) (gethash alist *xl-fast-alists*))))
    (if table
        (values (gethash key table))
        (hons-assoc-equal-walk key alist))))
(defun hons-acons (key value alist)
  (let* ((table (if (consp alist) (xl-fast-table alist)
                    (make-hash-table :test 'xl-hons-equal)))
         (pair (cons key value))
         (new (cons pair alist)))
    (when (consp alist) (remhash alist *xl-fast-alists*))
    (setf (gethash key table) pair)
    (setf (gethash new *xl-fast-alists*) table)
    new))
(defun make-fast-alist (alist)
  (when (consp alist) (xl-fast-table alist))
  alist)
(defun fast-alist-free (alist)
  (when (consp alist) (remhash alist *xl-fast-alists*))
  alist)
