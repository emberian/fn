; Total model accessors. The logical terms remain ACL2's list operations;
; executable calls also accept malformed model inputs without Lisp type errors.
(in-package "ACL2")
(defun fn-lc-head (x)
 (declare (xargs :guard t))
 (mbe :logic (car x) :exec (if (consp x) (car x) nil)))
(defun fn-lc-rest (x)
 (declare (xargs :guard t))
 (mbe :logic (cdr x) :exec (if (consp x) (cdr x) nil)))
(defun fn-lc-at (n x)
 (declare (xargs :guard t :measure (nfix n)))
 (if (consp x)
  (if (zp (nfix n)) (car x) (fn-lc-at (1- (nfix n)) (cdr x))) nil))
(defthm fn-lc-at-is-nth
 (equal (fn-lc-at n x) (nth n x))
 :hints (("Goal" :induct (fn-lc-at n x) :in-theory (enable nth))))
(defun fn-lc-drop (n x)
 (declare (xargs :guard t :measure (nfix n)))
 (if (zp (nfix n)) x (fn-lc-drop (1- (nfix n)) (fn-lc-rest x))))
(defthm fn-lc-drop-is-nthcdr
 (equal (fn-lc-drop n x) (nthcdr n x))
 :hints (("Goal" :induct (fn-lc-drop n x) :in-theory (enable nthcdr))))
(defun fn-lc-take (n x)
 (declare (xargs :guard t :measure (nfix n)))
 (if (zp (nfix n)) nil
  (cons (fn-lc-head x) (fn-lc-take (1- (nfix n)) (fn-lc-rest x)))))
(defthm fn-lc-take-is-take
 (equal (fn-lc-take n x) (take n x))
 :hints (("Goal" :induct (fn-lc-take n x) :in-theory (enable take))))
(defun fn-lc-join (a b)
 (declare (xargs :guard t))
 (if (consp a) (cons (car a) (fn-lc-join (cdr a) b)) b))
(defthm fn-lc-join-is-append
 (equal (fn-lc-join a b) (append a b)))
(defun fn-lc-assoc (key xs)
 (declare (xargs :guard t))
 (if (consp xs)
  (if (equal key (fn-lc-head (car xs))) (car xs)
   (fn-lc-assoc key (cdr xs))) nil))
(defthm fn-lc-assoc-is-assoc-equal
 (equal (fn-lc-assoc key xs) (assoc-equal key xs))
 :hints (("Goal" :induct (fn-lc-assoc key xs) :in-theory (enable assoc-equal))))
