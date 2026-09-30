; Borrowed current-codec values for bounded checkpoint preparation.
; A span names raw payload bytes in the immutable history pool, not a
; complete codec instruction. The row source owns root/epoch/pin/lease.
(in-package "ACL2")
(include-book "store-tree-codec")

(defun fn-hdc-atom (value)
  (declare (xargs :guard t))
  (list :atom value))

(defun fn-hdc-pair (a d)
  (declare (xargs :guard t))
  (list :pair a d))

(defun fn-hdc-span (op package-index offset count)
  (declare (xargs :guard (and (member-equal op '(3 4 6))
                              (natp package-index) (< package-index 3)
                              (natp offset) (natp count))))
  (list :span op package-index offset count))

(defun fn-hdc-car (node)
  (declare (xargs :guard t))
  (if (and (consp node) (eq (car node) :pair) (consp (cdr node)))
      (cadr node) nil))

(defun fn-hdc-cdr (node)
  (declare (xargs :guard t))
  (if (and (consp node) (eq (car node) :pair)
           (consp (cdr node)) (consp (cddr node)))
      (caddr node) nil))

; This is the named representation abstraction, not an executable fallback.
; It is deliberately non-executable: no tick may coerce/intern a whole span.
(defun-nx fn-hdc-abstract (node pool)
  (declare (xargs :measure (acl2-count node)))
  (cond ((not (consp node)) nil)
        ((eq (car node) :atom) (cadr node))
        ((eq (car node) :pair)
         (cons (fn-hdc-abstract (cadr node) pool)
               (fn-hdc-abstract (caddr node) pool)))
        ((eq (car node) :span)
         (let* ((op (cadr node)) (pkg (caddr node))
                (bytes (take (nfix (nth 4 node))
                             (nthcdr (nfix (nth 3 node)) pool))))
           (cond ((equal op 6) bytes)
                 ((equal op 3) (coerce (fn-scc-octets-chars bytes) 'string))
                 ((equal op 4) (fn-scc-intern pkg
                                             (coerce (fn-scc-octets-chars bytes) 'string)))
                 (t nil))))
        (t nil)))

(defthm fn-hdc-abstract-atom
  (equal (fn-hdc-abstract (fn-hdc-atom value) pool) value))

(defthm fn-hdc-abstract-pair
  (equal (fn-hdc-abstract (fn-hdc-pair a d) pool)
         (cons (fn-hdc-abstract a pool) (fn-hdc-abstract d pool))))

(defthm fn-hdc-car-of-pair
  (equal (fn-hdc-car (fn-hdc-pair a d)) a))
(defthm fn-hdc-cdr-of-pair
  (equal (fn-hdc-cdr (fn-hdc-pair a d)) d))

(in-theory (disable fn-hdc-atom fn-hdc-pair fn-hdc-span
                    fn-hdc-car fn-hdc-cdr fn-hdc-abstract))
