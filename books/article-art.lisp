; fn: one article representation, header list and packed body.
; The list constructor and abstraction are specifications; the served wire
; constructor retains the body store's packed digits without unpacking.
(in-package "ACL2")
(include-book "packed-octets")

(defun fn-art-crlfp (x)
  (declare (xargs :guard t))
  (and (consp x) (equal (car x) 13)
       (consp (cdr x)) (equal (cadr x) 10)))

(defun fn-art-double-crlfp (x)
  (declare (xargs :guard t))
  (and (fn-art-crlfp x) (fn-art-crlfp (cddr x))))

; At noninitial positions the separator includes the preceding line's CRLF.
(defun fn-art-split-rest (x)
  (declare (xargs :guard t))
  (cond ((fn-art-double-crlfp x)
         (mv (list 13 10 13 10) (cddddr x)))
        ((consp x)
         (mv-let (head body) (fn-art-split-rest (cdr x))
           (mv (cons (car x) head) body)))
        (t (mv nil nil))))

(defun fn-art-split (x)
  (declare (xargs :guard t))
  (if (fn-art-crlfp x)
      (mv (list 13 10) (cddr x))
    (fn-art-split-rest x)))

(defun fn-art-rest-separated-headp (head)
  (declare (xargs :guard t))
  (if (fn-art-double-crlfp head)
      (equal (cddddr head) nil)
    (and (consp head) (fn-art-rest-separated-headp (cdr head)))))

(defun fn-art-first-separator-headp (head)
  (declare (xargs :guard t))
  (if (fn-art-crlfp head)
      (equal (cddr head) nil)
    (fn-art-rest-separated-headp head)))

(defun fn-art-no-rest-separatorp (head)
  (declare (xargs :guard t))
  (and (not (fn-art-double-crlfp head))
       (if (consp head) (fn-art-no-rest-separatorp (cdr head)) (null head))))

(defun fn-art-no-separatorp (head)
  (declare (xargs :guard t))
  (and (not (fn-art-crlfp head)) (fn-art-no-rest-separatorp head)))

(defun fn-art-head (a) (declare (xargs :guard t)) (if (consp a) (car a) nil))
(defun fn-art-body (a) (declare (xargs :guard t)) (if (consp a) (cdr a) 1))
(defun fn-art-octets (a)
  (declare (xargs :guard t))
  (append (true-list-fix (fn-art-head a)) (fn-bch-unpack (fn-art-body a))))
(defun fn-art-of (x)
  (declare (xargs :guard t))
  (mv-let (head body) (fn-art-split x)
    (cons head (fn-bch-pack body))))

(defun fn-art-headp (a)
  (declare (xargs :guard t))
  (and (consp a)
       (fn-bch-octetsp (fn-art-head a))
       (fn-bch-packedp (fn-art-body a))
       (or (fn-art-first-separator-headp (fn-art-head a))
           (and (equal (fn-art-body a) 1)
                (fn-art-no-separatorp (fn-art-head a))))))

(local (defthm fn-art-octetsp-true-listp
         (implies (fn-bch-octetsp x) (true-listp x))))

(local
 (defthm fn-art-split-rest-recomposes
   (implies (fn-bch-octetsp x)
            (equal (append (mv-nth 0 (fn-art-split-rest x))
                           (mv-nth 1 (fn-art-split-rest x))) x))))

(local
 (defthm fn-art-split-rest-octets
   (implies (fn-bch-octetsp x)
            (and (fn-bch-octetsp (mv-nth 0 (fn-art-split-rest x)))
                 (fn-bch-octetsp (mv-nth 1 (fn-art-split-rest x)))))))

(local
 (defthm fn-art-split-rest-boundary
   (or (fn-art-rest-separated-headp (mv-nth 0 (fn-art-split-rest x)))
       (and (equal (mv-nth 1 (fn-art-split-rest x)) nil)
            (fn-art-no-rest-separatorp (mv-nth 0 (fn-art-split-rest x)))))))

(local
 (defthm fn-art-split-rest-initial-crlf
   (equal (fn-art-crlfp (mv-nth 0 (fn-art-split-rest x)))
          (fn-art-crlfp x))))

(defthm fn-art-split-recomposes
  (implies (fn-bch-octetsp x)
           (mv-let (head body) (fn-art-split x)
             (and (equal (append head body) x)
                  (or (and (true-listp head)
                           (fn-art-first-separator-headp head))
                      (equal body nil)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-art-split-rest fn-bch-octetsp
                               fn-art-rest-separated-headp fn-art-no-rest-separatorp)
           :use ((:instance fn-art-split-rest-boundary)
                 (:instance fn-art-split-rest-octets)
                 (:instance fn-art-split-rest-recomposes)))))

(local (defthm fn-art-octetsp-fix
         (implies (fn-bch-octetsp x) (equal (true-list-fix x) x))))

(defthm fn-art-of-roundtrip
  (implies (fn-bch-octetsp x)
           (and (equal (fn-art-octets (fn-art-of x)) x)
                (fn-art-headp (fn-art-of x))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-art-split-rest fn-bch-pack fn-bch-unpack
                               fn-art-rest-separated-headp fn-art-no-rest-separatorp)
           :use ((:instance fn-art-split-rest-boundary)
                 (:instance fn-art-split-rest-octets)
                 (:instance fn-art-split-rest-recomposes)))))
