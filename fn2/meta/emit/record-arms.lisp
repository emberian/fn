; fn2/meta/emit/record-arms.lisp: the recorder of the measure (LEAN-METATHEORY section -1,
; item 3). Raw Lisp, loaded after the simulator is loaded and the loop is left; test-only, never
; certified. META-RECORD-INSTALL wraps the child-form arm functions the world defines (every arm,
; handler and sub-arm of every kind in child form) so that each call the simulator makes is
; written, as the logical values of its arguments and of its results, to one line of the record:
;
;   (FN (ARG ...) (RESULT ...))
;
; A stobj argument or result is its logical value (a true list of its fields, an array field the
; list of its elements), read through the stobj's own accessors before the call (the call updates
; the live stobjs in place) and after it. Calls are sampled per function (the first *META-FIRST*,
; then every *META-EVERY*-th, at most *META-MAX* more), and a long array prints run-length
; encoded, so the record stays tens of megabytes.
(in-package "ACL2")

(defvar *meta-record-out* nil)
(defvar *meta-record-counts* (make-hash-table :test 'eq))
(defvar *meta-first* 24)
(defvar *meta-every* 41)
(defvar *meta-max* 48)
(defvar *meta-stobj-fields* (make-hash-table :test 'eq))

(defun meta-sym (&rest parts)
  (intern (apply #'concatenate 'string (mapcar (lambda (p) (if (symbolp p) (symbol-name p) p)) parts))
          "ACL2"))

(defun meta-fields (stobj)
  ; ((accessor length-fn) ...) per field in order; length-fn nil for a scalar field
  (or (gethash stobj *meta-stobj-fields*)
      (setf (gethash stobj *meta-stobj-fields*)
            (let ((ev (get-event stobj (w *the-live-state*))))
              (loop for f in (cddr ev)
                    until (keywordp f)
                    collect (let* ((name (if (consp f) (car f) f))
                                   (type (and (consp f) (cadr (member :type f)))))
                              (if (and (consp type) (eq (car type) 'array))
                                  (list (meta-sym name "I") (meta-sym name "-LENGTH"))
                                (list name nil))))))))

; A long array field prints run-length encoded, (FN2-META-RLE N1 V1 N2 V2 ...), which the Lean
; reader expands back to the field's list (Fn2.ACL2.Read.expandRle).
(defun meta-rle (xs)
  (let ((out nil) (run 0) (cur nil))
    (dolist (x xs)
      (if (and (> run 0) (eql x cur)) (incf run)
        (progn (when (> run 0) (push run out) (push cur out)) (setq cur x run 1))))
    (when (> run 0) (push run out) (push cur out))
    (cons 'fn2-meta-rle (nreverse out))))

; The accessors of an :inline stobj are macros in raw Lisp: each stobj's converter is a compiled
; function whose body expands them.
(defvar *meta-converters* (make-hash-table :test 'eq))
(defun meta-converter (stobj)
  (or (gethash stobj *meta-converters*)
      (setf (gethash stobj *meta-converters*)
            (compile nil
                     `(lambda (st)
                        (list ,@(loop for (acc len) in (meta-fields stobj)
                                      collect (if len
                                                  `(let ((xs (loop for i below (,len st) collect (,acc i st))))
                                                     (if (> (length xs) 64) (meta-rle xs) xs))
                                                `(,acc st)))))))))

(defun meta-logical (stobj live) (funcall (meta-converter stobj) live))

(defun meta-convert (vals stobjs)
  (loop for v in vals for s in stobjs collect (if s (meta-logical s v) v)))

(defun meta-sample-p (fn)
  (let ((n (incf (gethash fn *meta-record-counts* 0))))
    (and (<= n (+ *meta-first* (* *meta-every* *meta-max*)))
         (or (<= n *meta-first*) (zerop (mod n *meta-every*))))))

(defun meta-wrap (fn)
  (let* ((w (w *the-live-state*))
         (orig (symbol-function fn))
         (ins (getpropc fn 'stobjs-in nil w))
         (outs (getpropc fn 'stobjs-out nil w)))
    (setf (symbol-function fn)
          (lambda (&rest args)
            (if (not (meta-sample-p fn)) (apply orig args)
              (let* ((in (meta-convert args ins))
                     (res (multiple-value-list (apply orig args)))
                     (out (meta-convert res outs)))
                (let ((*package* (find-package "ACL2")) (*print-case* :upcase) (*print-pretty* nil)
                      (*print-length* nil) (*print-level* nil) (*print-escape* t) (*print-base* 10)
                      (*print-radix* nil))
                  (prin1 (list fn in out) *meta-record-out*)
                  (terpri *meta-record-out*))
                (values-list res)))))))

(defun meta-arm-fns ()
  (let ((w (w *the-live-state*)) (out nil))
    (loop for (k) in (table-alist 'fn2-machine-kinds w)
          do (dolist (spec '((:arms "-RUN-") (:observe-arms "-ON-") (:subarms "-SUB-")))
               (dolist (e (fn2-machine-declared k (car spec) w))
                 (let ((f (fn2-arms-child-name (fn2-arms-fn-name k (cadr spec) (car e)))))
                   (when (function-symbolp f w) (push f out))))))
    out))

(defun meta-record-install (path)
  (setq *meta-record-out* (open path :direction :output :if-exists :supersede))
  (let ((fns (meta-arm-fns)))
    (dolist (f fns) (meta-wrap f))
    (format t "~&META RECORD installed on ~a functions~%" (length fns))))

(defun meta-record-finish ()
  (close *meta-record-out*)
  (let ((rows nil))
    (maphash (lambda (k v) (push (list k v) rows)) *meta-record-counts*)
    (format t "~&META RECORD calls ~s~%" (sort rows #'string< :key (lambda (r) (symbol-name (car r)))))))
