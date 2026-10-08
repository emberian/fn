; fn: exact header-line boundaries for injection recipe walkers.
(in-package "ACL2")

; N includes CRLF.  No earlier CR or LF is permitted: checking just the
; last two positions would allow a short header to skip into the body.
; Every fixed-date caller supplies 39 or 49; no article body is scanned.
(defun fn-pb-fixed-linep (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (and (natp n)
       (<= 2 n)
       (consp x)
       (if (equal n 2)
           (and (equal (car x) 13)
                (consp (cdr x))
                (equal (cadr x) 10))
         (and (not (equal (car x) 13))
              (not (equal (car x) 10))
              (fn-pb-fixed-linep (- n 1) (cdr x))))))

(defun fn-pb-line-textp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (not (equal (car x) 13))
           (not (equal (car x) 10))
           (fn-pb-line-textp (cdr x)))
    (null x)))

(defthm fn-pb-line-textp-is-true-list
  (implies (fn-pb-line-textp x) (true-listp x)))

(defthm fn-pb-line-text-fix
  (implies (fn-pb-line-textp x) (equal (true-list-fix x) x)))

(defthm fn-pb-fixed-linep-of-text
  (implies (fn-pb-line-textp text)
           (fn-pb-fixed-linep (+ 2 (len text))
                              (append text (cons 13 (cons 10 tail))))))

(defthm fn-pb-line-textp-of-append
  (equal (fn-pb-line-textp (append x y))
         (and (fn-pb-line-textp (true-list-fix x))
              (fn-pb-line-textp y))))

(defthm fn-pb-fixed-linep-sufficient-length
  (implies (fn-pb-fixed-linep n x) (<= n (len x)))
  :rule-classes :linear)

(defthm fn-pb-fixed-linep-of-append
  (implies (fn-pb-fixed-linep n x)
           (fn-pb-fixed-linep n (append x y))))

(local (defthm fn-pb-consp-take
         (equal (consp (take n x)) (not (zp n)))))
(local (defthm fn-pb-car-take
         (implies (not (zp n)) (equal (car (take n x)) (car x)))))

(defthm fn-pb-fixed-linep-of-take
  (implies (and (natp n) (natp k) (<= n k))
           (equal (fn-pb-fixed-linep n (take k x))
                  (fn-pb-fixed-linep n x))))

(local (defthm fn-pb-take-len
         (implies (true-listp x) (equal (take (len x) x) x))))

(defthm fn-pb-fixed-linep-of-bounded-take
  (implies (and (natp n) (true-listp x))
           (equal (fn-pb-fixed-linep n (take (min n (len x)) x))
                  (fn-pb-fixed-linep n x)))
  :hints (("Goal" :cases ((<= n (len x))) :do-not-induct t)))
