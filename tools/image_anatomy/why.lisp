; tools/image_anatomy/why.lisp -- after shake.lisp is loaded (not run): which
; root chain keeps a function (IA_WHY names, one per line) in the closure.
(in-package "ACL2")
(defvar *ia-parent* (make-hash-table :test 'eq))
(defvar *ia-current* :root)
(defun ia-root-fn (f)
  (when (and (functionp f) (not (gethash f *ia-kept*)))
    (setf (gethash f *ia-kept*) t)
    (setf (gethash f *ia-parent*) *ia-current*)
    (push f *ia-work*)))
(defun ia-closure ()
  (loop while *ia-work* do
    (let ((f (pop *ia-work*)))
      (let ((*ia-current* f))
        (dolist (g (ignore-errors (sb-introspect:find-function-callees f)))
          (ia-root-fn g))
        (let ((code (ia-code-of f)))
          (when code
            (ignore-errors
             (sb-introspect::map-code-constants
              code (lambda (c)
                     (cond ((symbolp c) (ia-root-symbol c))
                           ((functionp c) (ia-root-fn c))))))))))))
(defun ia-why-main ()
  (ia-index-functions)
  (let ((*ia-current* :root)) (ia-roots))
  (ia-closure)
  (dolist (name (ia-read-lines (sb-ext:posix-getenv "IA_WHY")))
    (let* ((s (let ((*package* (find-package "ACL2"))) (read-from-string name)))
           (f (and (fboundp s) (symbol-function s))))
      (format t "~&IA-WHY ~a:" name)
      (loop for x = f then (gethash x *ia-parent*)
            for i below 40
            while (and x (not (eq x :root)))
            do (format t " <- ~a" (or (gethash x *ia-fn->name*) (sb-kernel:%fun-name x))))
      (terpri))))
