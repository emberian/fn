; PRF-1133: actual guard-verified destructive arena boundary.
(in-package "ACL2")
(include-book "payload-view-lease")
(include-book "payload-arena")
(defun fn-pvl-clear (s fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-arena-p fn-arena)))
  (let ((answer (fn-pvl-reset s)))
    (if (not (eq (car answer) :reset)) (mv answer fn-arena)
      (let ((fn-arena (fn-arena-clear fn-arena))) (mv answer fn-arena)))))
(defthm fn-pvl-refused-clear-keeps-the-actual-arena
  (implies (not (eq (car (fn-pvl-reset s)) :reset))
           (equal (mv-nth 1 (fn-pvl-clear s fn-arena)) fn-arena))
  :hints (("Goal" :in-theory (enable fn-pvl-clear))))
(defthm fn-pvl-accepted-clear-is-the-actual-empty-arena
  (implies (eq (car (fn-pvl-reset s)) :reset)
           (equal (mv-nth 1 (fn-pvl-clear s fn-arena)) nil))
  :hints (("Goal" :in-theory (enable fn-pvl-clear))))
(in-theory (disable fn-pvl-clear))
