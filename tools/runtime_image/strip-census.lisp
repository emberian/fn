; tools/runtime_image/strip-census.lisp -- raw-mode census of the CURRENT
; values of the installed world, by property and by global-value name
; (lane image-floor).  Loaded after world-measure.lisp at the end of an
; unsaved session; prints RI-CUR lines.  A measurement only.
(in-package "ACL2")

(defun ri-current-census (label)
  (let* ((key *current-acl2-world-key*)
         (syms (make-hash-table :test 'eq))
         (seen (make-hash-table :test 'eq :size 4000000))
         (by-prop (make-hash-table :test 'eq))
         (by-global (make-hash-table :test 'eq))
         (count-prop (make-hash-table :test 'eq)))
    (dolist (triple (w *the-live-state*)) (setf (gethash (car triple) syms) t))
    ;; Pass 1 skips the world indices (zap tables of world tails, which
    ;; reach the whole history); pass 2 attributes what only they reach.
    (dolist (pass '(1 2))
    (maphash
     (lambda (s v)
       (declare (ignore v))
       (dolist (entry (get s key))
         (let ((val (cadr entry)))
           (unless (or (eq val *acl2-property-unbound*)
                       (not (eq (= pass 2)
                                (and (eq (car entry) 'global-value)
                                     (member s '(event-index command-index))
                                     t))))
             (let ((n (+ 32 (ri-retained val seen))))
               (incf (gethash (car entry) by-prop 0) n)
               (incf (gethash (car entry) count-prop 0))
               (when (eq (car entry) 'global-value)
                 (incf (gethash s by-global 0) n)))))))
     syms))
    (flet ((dump (tag table n)
             (let ((rows nil))
               (maphash (lambda (k v) (push (cons k v) rows)) table)
               (setq rows (sort rows #'> :key #'cdr))
               (loop for (k . v) in (subseq rows 0 (min n (length rows)))
                     do (format t "~&~a ~a ~a ~d ~d~%" tag label k v
                                (gethash k count-prop 0))))))
      (dump "RI-CUR-PROP" by-prop 400)
      (dump "RI-CUR-GLOBAL" by-global 60))))
