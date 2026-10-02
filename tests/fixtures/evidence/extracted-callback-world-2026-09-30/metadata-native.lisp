(in-package "ACL2")
(defun fnn-fault (control &rest args)
  (error 'fnn-store-fault :message (apply #'format nil control args)))

(defvar *fnn-raw-dispatch* (make-hash-table :test 'eq)
  "entry name -> its raw (guard-verified, compiled) function symbol")

(defvar *fnn-dispatch-counterpart* nil
  "T when the developer selector keeps the executable-counterpart path.")

(defun fnn-install-raw-dispatch (&key (report t))
  "Fill *fnn-raw-dispatch* from the fn-interfaces table of the loaded world:
the :raw-with and :raw-guarded entries, checked against the world; the count."
  (let ((wrld (w *the-live-state*)))
    (clrhash *fnn-raw-dispatch*)
    (dolist (entry (table-alist 'fn-interfaces wrld))
      (let ((name (car entry))
            (theorems (cadr (assoc-keyword :raw-with (cdr entry))))
            (guarded (assoc-keyword :raw-guarded (cdr entry))))
        (when (or theorems guarded)
          (when guarded
            (let ((problem (fn-di-raw-guarded-problem name (cdr entry) wrld)))
              (when problem
                (error "fnn-install-raw-dispatch: ~a has a refused guarded declaration: ~s"
                       name problem))))
          ;; Recheck the loaded table at the dispatch installation boundary,
          ;; rather than assuming every table entry came from definterface.
          (let ((problem (and theorems (fn-di-raw-with-problem name (cdr entry) wrld))))
            (when problem
              (error "fnn-install-raw-dispatch: ~a has a refused declaration: ~s"
                     name problem)))
          (multiple-value-bind (target-problem target)
              (if guarded (fn-di-raw-guarded-target name (cdr entry) wrld)
                (values nil name))
            (when target-problem
              (error "fnn-install-raw-dispatch: refused creator target for ~a: ~s" name target-problem))
            (let ((raw target))
            (when (and raw (macro-function raw))
              (error "fnn-install-raw-dispatch: ~a resolved to a macro, not a raw function" name))
            (unless (and raw (fboundp raw))
              (error "fnn-install-raw-dispatch: ~a has a raw declaration but no raw definition" name))
            (unless (eq (symbol-class name wrld) :common-lisp-compliant)
              (error "fnn-install-raw-dispatch: ~a has a raw declaration but is ~a, not guard-verified"
                     name (symbol-class name wrld)))
            (when (and guarded (not (compiled-function-p (symbol-function raw))))
              (error "fnn-install-raw-dispatch: ~a has no compiled guarded callback" name))
            (setf (gethash name *fnn-raw-dispatch*) raw)
            (when report
              (format t "~&FN_RAW_DISPATCH ~(~a~) ~(~a~) invariant-risk=~a with=~(~a~)~%"
                      name (symbol-class name wrld)
                      (if (getpropc name 'invariant-risk nil wrld) "t" "nil")
                      (if guarded (cadr guarded) theorems))))))))
    (hash-table-count *fnn-raw-dispatch*)))

(defun fnn-fixed-raw-callback (name)
  "Return the selected compiled raw entry; refuse an unprepared hot callback."
  (when *fnn-dispatch-counterpart*
    (fnn-fault "fixed callback ~(~a~) requires raw dispatch" name))
  (let ((raw (gethash name *fnn-raw-dispatch*)))
    (unless (and raw (fboundp raw))
      (fnn-fault "fixed callback ~(~a~) is missing verified raw dispatch" name))
    (when (macro-function raw)
      (fnn-fault "fixed callback ~(~a~) names a macro, not a callable function" name))
    (let ((function (symbol-function raw)))
      (unless (compiled-function-p function)
        (fnn-fault "fixed callback ~(~a~) is not compiled" name))
      function)))
