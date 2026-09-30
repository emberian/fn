; Generic persistent positive-natural binary trie, extracted without entry dependencies.
(in-package "ACL2")
(include-book "acceptance-alloc")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-gnix-val (node)
  (declare (xargs :guard t))
  (fn-ag-car node))

(defun fn-gnix-zero (node)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr node)))

(defun fn-gnix-one (node)
  (declare (xargs :guard t))
  (fn-ag-cdr (fn-ag-cdr node)))

; The root holds 1 (and every non-number, which no caller asks for); above
; it, the low bit picks the child and the rest of the number goes down.
(defun fn-gnix-get (n node)
  (declare (xargs :guard t :measure (nfix n)))
  (cond ((not (consp node)) nil)
        ((or (not (integerp n)) (<= n 1)) (fn-gnix-val node))
        ((evenp n) (fn-gnix-get (floor n 2) (fn-gnix-zero node)))
        (t (fn-gnix-get (floor n 2) (fn-gnix-one node)))))

(defun fn-gnix-set (n value node)
  (declare (xargs :guard t :measure (nfix n)))
  (cond ((or (not (integerp n)) (<= n 1))
         (cons value (fn-ag-cdr node)))
        ((evenp n)
         (cons (fn-gnix-val node)
               (cons (fn-gnix-set (floor n 2) value (fn-gnix-zero node))
                     (fn-gnix-one node))))
        (t
         (cons (fn-gnix-val node)
               (cons (fn-gnix-zero node)
                     (fn-gnix-set (floor n 2) value (fn-gnix-one node)))))))

(defthm fn-gnix-get-of-nil
  (equal (fn-gnix-get n nil) nil))

(local
 (defun fn-gnix-get-set-induct (n m node)
   (declare (xargs :measure (nfix n)))
   (cond ((or (not (integerp n)) (<= n 1)) (list m node))
         ((or (not (integerp m)) (<= m 1)) (list n node))
         ((evenp n)
          (fn-gnix-get-set-induct (floor n 2) (floor m 2) (fn-gnix-zero node)))
         (t (fn-gnix-get-set-induct (floor n 2) (floor m 2) (fn-gnix-one node))))))

; The trie is a map: reading a number after setting one reads the value set
; when they are the same number and the old value otherwise.
(defthm fn-gnix-get-of-set
  (implies (and (posp n) (posp m))
           (equal (fn-gnix-get n (fn-gnix-set m value node))
                  (if (equal n m) value (fn-gnix-get n node))))
  :hints (("Goal" :induct (fn-gnix-get-set-induct n m node)
           :in-theory (enable fn-gnix-get fn-gnix-set))))


(in-theory (disable (:definition fn-gnix-set)))
