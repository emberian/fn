; Keep defteeth's generated wrappers, and verify their guards before use.
; The generator owns their bodies; this adapter adds no witness or claim.
(in-package "ACL2")
(include-book "defkeystone")
(defun fn-lc-teeth-prepare-wrappers (events hints)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp events)
  (let* ((e (car events)) (d (cadr e))
         (rest (fn-lc-teeth-prepare-wrappers (cdr events) hints)))
   (if (and (equal (car e) 'local) (equal (car d) 'defun))
    (cons e (cons (list 'local (list 'verify-guards (cadr d) :hints hints)) rest))
    rest)) nil))
