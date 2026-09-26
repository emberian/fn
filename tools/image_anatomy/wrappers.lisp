; tools/image_anatomy/wrappers.lisp -- the host wrappers' classes (lane
; image-anatomy): every function the ld'ed host/*.lisp files define (world
; triples after the last include-book, outside every book), by symbol-class
; and by whether its guard is T.  A reading only.
(in-package "ACL2")
(let ((wrld (w *the-live-state*)) (in-book nil) (rows (make-hash-table :test 'equal))
      (seen (make-hash-table)))
  (dolist (tr (reverse wrld))
    (when (and (eq (car tr) 'include-book-path) (eq (cadr tr) 'global-value))
      (setq in-book (cddr tr)))
    (when (and (eq (cadr tr) 'formals) (null in-book)
               (not (fgetprop (car tr) 'predefined nil wrld))
               (not (gethash (car tr) seen)))
      (setf (gethash (car tr) seen) t)
      (let* ((f (car tr))
             (class (fgetprop f 'symbol-class nil wrld))
             (guard (fgetprop f 'guard t wrld)))
        (incf (gethash (list class (if (equal guard t) :guard-t :guarded)) rows 0)))))
  (maphash (lambda (k v) (format t "~&IA-WRAPPERS ~s ~d~%" k v)) rows))
