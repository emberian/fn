; tools/runtime_image/export-estimate.lisp -- lane image-floor: the size of
; what an ACL2-free export of the host's executable closure would carry, in an
; unsaved session built as host/native/build.lisp builds it (after closure.lisp,
; which defines ri-callees).  For every function the closure reaches: its raw
; compiled code object and its *1* code object (each counted once), and the
; heap objects their constants reach that no other counted object reached.
; Prints RI-EXPORT lines.  A measurement only.
(in-package "ACL2")

(defun ri-export-estimate (roots-file)
  (let* ((wrld (w *the-live-state*))
         (reached (make-hash-table :test 'eq))
         (stack nil)
         (codes (make-hash-table :test 'eq))
         (seen (make-hash-table :test 'eq :size 2000000))
         (raw-code 0) (oneify-code 0) (raw-fns 0) (oneify-fns 0) (consts 0))
    (with-open-file (in roots-file)
      (loop for line = (read-line in nil nil) while line do
        (let ((s (find-symbol (string-upcase line) "ACL2")))
          (when (and s (function-symbolp s wrld)) (push s stack)))))
    (dolist (triple wrld)
      (when (and (eq (cadr triple) 'formals)
                 (eq (ri-book-of (car triple) wrld) :top-level))
        (push (car triple) stack)))
    (loop while stack do
      (let ((f (pop stack)))
        (unless (gethash f reached)
          (setf (gethash f reached) t)
          (dolist (g (ri-callees f wrld))
            (unless (gethash g reached) (push g stack))))))
    (flet ((code-of (sym)
             (and (fboundp sym) (not (macro-function sym))
                  (let ((fn (symbol-function sym)))
                    (and (functionp fn)
                         (sb-kernel:fun-code-header (sb-kernel:%fun-fun fn))))))
           (count-code (code)
             (let ((n (sb-ext:primitive-object-size code)) (c 0))
               (loop for i from sb-vm:code-constants-offset
                       below (sb-kernel:code-header-words code)
                     do (incf c (ri-retained (sb-kernel:code-header-ref code i) seen)))
               (values n c))))
      (maphash
       (lambda (f v)
         (declare (ignore v))
         (let ((code (code-of f)))
           (when (and code (not (gethash code codes)))
             (setf (gethash code codes) t)
             (multiple-value-bind (n c) (count-code code)
               (incf raw-code n) (incf consts c) (incf raw-fns))))
         (let* ((s (*1*-symbol? f)) (code (and s (code-of s))))
           (when (and code (not (gethash code codes)))
             (setf (gethash code codes) t)
             (multiple-value-bind (n c) (count-code code)
               (incf oneify-code n) (incf consts c) (incf oneify-fns)))))
       reached)
      (format t "~&RI-EXPORT reached=~d raw-fns=~d raw-code=~d oneify-fns=~d oneify-code=~d constants=~d~%"
              (hash-table-count reached) raw-fns raw-code oneify-fns oneify-code consts))))
