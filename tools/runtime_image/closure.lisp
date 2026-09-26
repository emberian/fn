; tools/runtime_image/closure.lisp -- the executable closure of the host, in
; raw mode, over the world a session built exactly as host/native/build.lisp
; builds it.  Roots: every function the ld'ed host wrappers define (their
; events are :top-level, in no book) and every ACL2 function symbol named in
; host/native/*.lisp (the file RI_ROOTS lists those names, one per line).
; Edges: a function's unnormalized body, its guard, and its attachment.  Each
; reached function is mapped to the book that introduced it (Kestrel's
; book-of-event, restated here so that no book is added to the world).
(in-package "ACL2")

(defun ri-book-of (name wrld)
  (cond ((getpropc name 'predefined nil wrld) :built-in)
        (t (let ((ev-wrld (decode-logical-name name wrld)))
             (if ev-wrld
                 (let ((p (getpropc 'include-book-path 'global-value nil ev-wrld)))
                   (if p (car p) :top-level))
               nil)))))

(defun ri-book-string (b)
  (cond ((stringp b)
         ; A relocated certificate names the tree it was made in; the book is
         ; the path below its last "/books/".
         (let ((i (search "/books/" b :from-end t)))
           (if i (subseq b (1+ i)) b)))
        ((sysfile-p b) (concatenate 'string "[books]/" (sysfile-filename b)))
        (t (format nil "~(~a~)" b))))

(defun ri-callees (f wrld)
  (let ((out nil))
    (let ((body (getpropc f 'unnormalized-body nil wrld)))
      (when body (setq out (all-fnnames body))))
    (let ((g (getpropc f 'guard nil wrld)))
      (when g (setq out (union-eq (all-fnnames g) out))))
    (let ((a (getpropc f 'attachment nil wrld)))
      (cond ((and a (symbolp a))
             (let* ((alist (getpropc a 'attachment nil wrld))
                    (pair (and (alistp alist) (assoc-eq f alist))))
               (when (and (cdr pair) (symbolp (cdr pair))) (push (cdr pair) out))))
            ((alistp a)
             (let ((pair (assoc-eq f a)))
               (when (and (cdr pair) (symbolp (cdr pair))) (push (cdr pair) out))))))
    out))

(defun ri-closure-report (roots-file)
  (let* ((wrld (w *the-live-state*))
         (reached (make-hash-table :test 'eq))
         (stack nil)
         (book-fns (make-hash-table :test 'equal))
         (book-thms (make-hash-table :test 'equal))
         (book-reached (make-hash-table :test 'equal))
         (named 0) (toplevel 0))
    ; Roots from the raw host's text.
    (with-open-file (in roots-file)
      (loop for line = (read-line in nil nil) while line do
        (let ((s (find-symbol (string-upcase line) "ACL2")))
          (when (and s (function-symbolp s wrld))
            (incf named) (push s stack)))))
    ; Roots from the ld'ed host wrappers, and per-book counts over the world.
    (dolist (triple wrld)
      (when (eq (cadr triple) 'formals)
        (let* ((f (car triple)) (b (ri-book-of f wrld)))
          (when (eq b :top-level) (incf toplevel) (push f stack))
          (when (or (stringp b) (sysfile-p b))
            (incf (gethash (ri-book-string b) book-fns 0)))))
      (when (eq (cadr triple) 'theorem)
        (let ((b (ri-book-of (car triple) wrld)))
          (when (or (stringp b) (sysfile-p b))
            (incf (gethash (ri-book-string b) book-thms 0))))))
    (loop while stack do
      (let ((f (pop stack)))
        (unless (gethash f reached)
          (setf (gethash f reached) t)
          (dolist (g (ri-callees f wrld))
            (unless (gethash g reached) (push g stack))))))
    (let ((n 0) (builtin 0))
      (maphash (lambda (f v) (declare (ignore v))
                 (incf n)
                 (let ((b (ri-book-of f wrld)))
                   (cond ((eq b :built-in) (incf builtin))
                         ((or (stringp b) (sysfile-p b))
                          (incf (gethash (ri-book-string b) book-reached 0))))))
               reached)
      (format t "~&RI-CLOSURE roots-named=~d roots-toplevel=~d reached=~d built-in=~d~%"
              named toplevel n builtin))
    (dolist (entry (global-val 'include-book-alist wrld))
      (let ((b (ri-book-string (car entry))))
        (format t "~&RI-BOOK ~a fns=~d thms=~d reached=~d~%" b
                (gethash b book-fns 0) (gethash b book-thms 0)
                (gethash b book-reached 0))))))
