;;; tools/runtime_floor/shim.lisp -- the plain-CL runtime the exported fn
;;; definitions call (lane runtime-floor).  Portable CL.  Every name here is a
;;; cut point of the export (extract.lisp *rf-cut*): ACL2's error path, the
;;; wormhole undo, hons/fast alists (by their logical definitions plus an
;;; index), the memo tables and the world.  Loaded after 00-packages.lisp.
(in-package "ACL2")

(eval-when (:compile-toplevel :load-toplevel :execute)
  (unless (find-package "ACL2_INVISIBLE") (make-package "ACL2_INVISIBLE" :use nil)))
(defparameter *the-live-state* (intern "The Live State Itself" "ACL2_INVISIBLE"))

(defun rf-fresh (x)
  (cond ((stringp x) x)
        ((simple-vector-p x) (map 'simple-vector #'rf-fresh x))
        ((arrayp x) (copy-seq x))
        ((and (consp x) (rf-has-array x)) (cons (rf-fresh (car x)) (rf-fresh (cdr x))))
        (t x)))
(defun rf-has-array (x)
  (cond ((stringp x) nil)
        ((arrayp x) t)
        ((consp x) (or (rf-has-array (car x)) (rf-has-array (cdr x))))
        (t nil)))

(define-condition rf-acl2-error (error)
  ((what :initarg :what :reader rf-acl2-error-what))
  (:report (lambda (c s) (format s "ACL2 error ~s" (rf-acl2-error-what c)))))

(defun hard-error (ctx str alist)
  (error 'rf-acl2-error :what (list :hard-error ctx str alist)))
(defun illegal (ctx str alist)
  (error 'rf-acl2-error :what (list :illegal ctx str alist)))
(defun throw-raw-ev-fncall (val) (throw 'raw-ev-fncall val))
(defun throw-nonexec-error (fn actuals)
  (error 'rf-acl2-error :what (list :non-executable fn actuals)))
(defun replace-live-stobjs-in-list (l) l)
(defun push-wormhole-undo-formi (&rest r) (declare (ignore r)) nil)
(defun fmt-to-comment-window (&rest r) (declare (ignore r)) nil)
(defun memoize-flush1 (&rest r) (declare (ignore r)) nil)
(defun w (state)
  (declare (ignore state))
  (error 'rf-acl2-error :what (list :no-world)))

;;; hons and fast alists
(defvar *rf-fast-alists* (make-hash-table :test 'eq))
(defun hons-equal (x y) (equal x y))
(defun hons-copy (x) x)
(defun hons (x y) (cons x y))
(defun hons-assoc-equal (key alist)
  (loop for tail on alist
        when (and (consp (car tail)) (equal key (caar tail))) return (car tail)))
(defun hons-get (key alist)
  (let ((ht (and (consp alist) (gethash alist *rf-fast-alists*))))
    (if ht (values (gethash key ht)) (hons-assoc-equal key alist))))
(defun hons-acons (key val alist)
  (let* ((pair (cons key val)) (new (cons pair alist)))
    (cond ((atom alist)
           (let ((ht (make-hash-table :test 'equal)))
             (setf (gethash key ht) pair (gethash new *rf-fast-alists*) ht)))
          (t (let ((ht (gethash alist *rf-fast-alists*)))
               (when ht
                 (remhash alist *rf-fast-alists*)
                 (setf (gethash key ht) pair (gethash new *rf-fast-alists*) ht)))))
    new))
(defun fast-alist-free (alist) (remhash alist *rf-fast-alists*) alist)

(defun rf-guard-violation (fn args)
  (error 'rf-acl2-error :what (list :guard-violation fn args)))
