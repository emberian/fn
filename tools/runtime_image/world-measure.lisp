; tools/runtime_image/world-measure.lisp -- raw-mode measurement of the
; logical world an image carries.  Loaded (after `(set-raw-mode t)') at the
; end of a session that has built the image's world, never saved into an
; image.  It prints lines starting RI- that tools/runtime_image/closure.py
; reads.  A measurement only: it decides nothing the node does.
(in-package "ACL2")

(defun ri-object-size (x)
  (sb-ext:primitive-object-size x))

; Octets newly reachable from X that are not yet in SEEN: conses, vectors,
; strings, numbers that live in the heap.  Symbols, functions and packages
; are not descended into: they are the image's code and names, not the world.
(defun ri-retained (x seen)
  (let ((total 0) (stack (list x)))
    (loop while stack do
      (let ((o (pop stack)))
        (unless (or (symbolp o) (functionp o) (packagep o) (characterp o)
                    (typep o 'fixnum) (gethash o seen))
          (setf (gethash o seen) t)
          (incf total (ri-object-size o))
          (cond ((consp o) (push (car o) stack) (push (cdr o) stack))
                ((and (simple-vector-p o))
                 (loop for e across o do (push e stack)))))))
    total))

(defun ri-world-report (label)
  (let* ((wrld (w *the-live-state*))
         (seen (make-hash-table :test 'eq :size 4000000))
         (by-prop (make-hash-table :test 'eq))
         (triples 0) (landmarks 0) (theorems 0) (functions 0))
    (sb-ext:gc :full t)
    (format t "~&RI-HEAP ~a dynamic-usage=~d~%" label (sb-kernel:dynamic-usage))
    (dolist (triple (reverse wrld))
      (incf triples)
      (let ((prop (cadr triple)))
        (when (and (eq (car triple) 'event-landmark) (eq prop 'global-value))
          (incf landmarks))
        (when (eq prop 'theorem) (incf theorems))
        (when (eq prop 'formals) (incf functions))
        (incf (gethash prop by-prop 0)
              (+ 32 (ri-retained (cddr triple) seen)))))
    (format t "~&RI-WORLD ~a triples=~d events=~d theorem-props=~d formals-props=~d~%"
            label triples landmarks theorems functions)
    (let ((rows nil) (sum 0))
      (maphash (lambda (k v) (push (cons k v) rows) (incf sum v)) by-prop)
      (format t "~&RI-WORLD-BYTES ~a total=~d~%" label sum)
      (loop for (k . v) in (subseq (sort rows #'> :key #'cdr) 0 (min 25 (length rows)))
            do (format t "~&RI-PROP ~a ~a ~d~%" label k v)))))

; The heap a world-free image would shed, measured rather than estimated: in
; the (unsaved) session, strip every installed world property except KEEP
; from each symbol's property alist, replace the world by its KEEP triples,
; drop the world stacks ACL2 keeps for undo, collect, and read the dynamic
; usage.  The session is unusable afterwards; nothing is saved.  Any
; reference this misses keeps its objects alive, so the figure is a lower
; bound on what a world-free image sheds.
(defparameter *ri-execution-props*
  '(symbol-class stobjs-in stobjs-out formals invariant-risk absstobj-info stobj
    stobj-function attachment predefined constrainedp guard))

(defun ri-strip-report (label keep)
  (let* ((key *current-acl2-world-key*)
         (wrld (w *the-live-state*))
         (syms (make-hash-table :test 'eq)))
    (dolist (triple wrld) (setf (gethash (car triple) syms) t))
    (maphash (lambda (s v)
               (declare (ignore v))
               (setf (get s key)
                     (remove-if-not (lambda (entry) (member (car entry) keep))
                                    (get s key))))
             syms)
    (setf (symbol-value 'ACL2_GLOBAL_ACL2::CURRENT-ACL2-WORLD)
          (remove-if-not (lambda (triple) (member (cadr triple) keep)) wrld))
    (setq wrld nil)
    (dolist (g '(ACL2_GLOBAL_ACL2::UNDONE-WORLDS-KILL-RING
                 ACL2_GLOBAL_ACL2::LAST-MAKE-EVENT-EXPANSION))
      (when (boundp g) (setf (symbol-value g) nil)))
    (sb-ext:gc :full t)
    (format t "~&RI-STRIP ~a keep=~d dynamic-usage=~d~%" label (length keep)
            (sb-kernel:dynamic-usage))))
