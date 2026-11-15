; Execute the production lowering and its emitted composed functions. This
; small host harness supplies metadata/unchanged-expression plumbing, not an
; accounting implementation; ACL2 admission remains a separate gate.
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(declaim (declaration xargs))
(defmacro mv (&rest xs) `(values ,@xs))
(defmacro mv-let (vars expr &body body) `(multiple-value-bind ,vars ,expr ,@body))
(defun fn2-arm-get (key xs) (getf xs key))
(defun fn2-decl-get (key xs) (getf xs key))
(defun fn2-decl-set (key value xs) (let ((out (copy-list xs))) (setf (getf out key) value) out))
(defun union-equal (xs ys) (union xs ys :test #'equal))
(defun member-eq (x xs) (member x xs))
(defun assoc-eq (x xs) (assoc x xs))
(defun natp (x) (and (integerp x) (<= 0 x)))
(defun nfix (x) (if (natp x) x 0))
(defun zp (x) (not (and (integerp x) (< 0 x))))
(defun fn2-cost-constant (x world) (declare (ignore x world)) nil)
(defun fn2-arm-use-name (x) (if (consp x) (car x) x))
(defun fn2-decl-row (key world) (cdr (assoc key world :test #'equal)))
(defun fn2-columns-sym (kind suffix) (intern (concatenate 'string (symbol-name kind) suffix) "ACL2"))
(defun msg (&rest xs) xs)
(defun fn2-arms-exprs (xs env acc fuel) (declare (ignore env fuel)) (mv nil xs acc))
(defun fn2-arms-wrap-writes (env body) (assert (null (getf env :written))) body)
(defparameter *fn2-arms-octet-exports* nil)
(with-open-file (in "books/machine-arms.lisp")
 (loop for form = (read in nil :eof) until (eq form :eof) do
  (when (and (eq (car form) 'defun)
   (member (cadr form) '(fn2-arms-add fn2-arms-sym fn2-arms-tuple fn2-arms-op-row
    fn2-arms-bound fn2-arms-loop-dim fn2-arms-loop-terms fn2-arms-loop-add
    fn2-arms-calls-cost fn2-arms-account-floor fn2-arms-prefix-charges
    fn2-arms-prefix-report fn2-arms-charge-form fn2-arms-terminal))) (eval form))))
(let* ((world '(((:cost lookup) :bytes 8192 :steps 3 :descriptors 0)
                ((:cost put) :bytes 4096 :steps 2 :descriptors 0)))
       (env (list :world world :kind 'probe :path-calls '(put)))
       (charge nil) (bounds nil))
 (mv-let (err form acc) (fn2-arms-charge-form 17 1 0 t env nil 64)
  (assert (null err)) (setf charge form bounds (getf acc :charges)))
 (eval `(defun probe-sub-put (id budget fn2-core)
          (declare (ignore id budget)) ,charge))
 (assert (equal (multiple-value-list (probe-sub-put 0 0 'state)) '(4096 2 0 t state)))
 (let* ((caller (list :kind 'probe :world world :path-calls '(lookup)
                      :subs (list (cons 'put (list :charges bounds)))))
        (code nil) (derived nil))
  (mv-let (err form acc) (fn2-arms-terminal '(:goto put) caller nil 64)
   (assert (null err)) (setf code form derived (getf acc :charges)))
  (eval `(defun composed (id budget fn2-core) ,code))
  (assert (equal (multiple-value-list (composed 0 0 'state)) '(12288 5 0 t state)))
  (assert (equal derived '((12288 5 0))))
  ; A second boundary adds only its own prefix, not the first one again.
  (eval `(defun nested (id budget fn2-core)
    ,(fn2-arms-prefix-report '(composed id budget fn2-core) 11 7 nil)))
  (assert (equal (multiple-value-list (nested 0 0 'state)) '(12299 12 0 t state))))
 ; Zero explicit report cannot erase the callback's charge (the end path).
 (mv-let (err form acc) (fn2-arms-charge-form 0 0 0 nil
                         (list :world world :path-calls '(lookup)) nil 64)
  (declare (ignore acc)) (assert (null err))
  (assert (equal (multiple-value-list (eval `(let ((fn2-core 's)) ,form))) '(8192 3 0 nil s))))
 ; Dynamic explicit charge and actual repeat passes stay visible; unused
 ; declared descriptor capacity must never become a fabricated issue.
 (mv-let (err form acc) (fn2-arms-charge-form 'n 1 1 t
   (list :world world :path-calls '(put) :lets '((n . 9000))
         :loops '((left 4 7 2 0 4)) :children '(table pool)) nil 64)
  (assert (null err))
  (assert (equal (getf acc :charges) '((9028 10 1))))
  (assert (equal (multiple-value-list
   (eval `(let ((n 6000) (left 1) (table 'table-value) (pool 'pool-value)) ,form)))
   '(6021 8 1 t table-value pool-value)))))
(format t "ARM ACCOUNTING COMPOSED CONTROLS PASS~%")
