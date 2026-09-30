; PRF-1113. Compositional canonical Store tree size carries.
; Library dependency for P12/S7, not a claim that the live owner maintains it.
(in-package "ACL2")
(include-book "store-tree-codec")
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

; No byte list is allocated. Work is the existing codec integer's digit width.
(defun fn-scs-width (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) 0 (+ 1 (fn-scs-width (floor n 256)))))

(defthm fn-scs-width-is-digit-length
  (equal (fn-scs-width n) (len (fn-scc-le-digits n)))
  :hints (("Goal" :in-theory (enable fn-scs-width fn-scc-le-digits))))

(defun fn-scs-atom-size (x)
  (declare (xargs :guard (or (integerp x) (characterp x) (stringp x) (symbolp x))))
  (cond ((null x) 1)
        ((natp x) (+ 2 (fn-scs-width x)))
        ((integerp x) (+ 2 (fn-scs-width (- -1 x))))
        ((characterp x) 2)
        ((stringp x) (+ 2 (fn-scs-width (length x)) (length x)))
        (t (+ 3 (fn-scs-width (length (symbol-name x)))
              (length (symbol-name x))))))

(local
 (defthm fn-scs-chars-length
   (equal (len (fn-scc-chars-octets xs)) (len xs))
   :hints (("Goal" :induct (len xs) :in-theory (enable fn-scc-chars-octets)))))
(local
 (defthm fn-scs-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(defthm fn-scs-atom-size-is-encoded-length
  (equal (fn-scs-atom-size x) (len (fn-scc-atom-octets x)))
  :hints (("Goal" :in-theory (e/d (fn-scs-atom-size fn-scc-atom-octets
                                    fn-scc-string-octets fn-scc-nat-octets)
                                   (fn-scs-width fn-scc-le-digits)))))

; Fixed-size sidecar: (encoded-octets octet-list-length-or-nil octet-atom-p).
; NIL has octet-list length zero; every constructed cons has octet-atom-p NIL.
; The second/third fields preserve the codec's octet-list collapsing decision.
(defun fn-scs-carryp (c)
  (declare (xargs :guard t))
  (and (consp c) (consp (cdr c)) (consp (cddr c)) (null (cdddr c))
       (natp (car c)) (or (null (cadr c)) (natp (cadr c)))
       (booleanp (caddr c))))

(defun fn-scs-atom (x)
  (declare (xargs :guard (or (integerp x) (characterp x) (stringp x) (symbolp x))))
  (list (fn-scs-atom-size x) (if (null x) 0 nil) (fn-scc-octetp x)))

(defun fn-scs-cons (a d)
  (declare (xargs :guard (and (fn-scs-carryp a) (fn-scs-carryp d))))
  (if (and (caddr a) (natp (cadr d)))
      (let ((n (+ 1 (cadr d))))
        (list (+ 2 (fn-scs-width n) n) n nil))
    (list (+ 1 (car a) (car d)) nil nil)))

; Logical correspondence only. Never execute this over a shared context at POST.
(defun fn-scs-summary (x)
  (declare (xargs :guard (fn-scc-treep x) :verify-guards nil))
  (list (len (fn-scc-encode x))
        (if (fn-scc-octet-listp x) (len x) nil)
        (fn-scc-octetp x)))

(defthm fn-scs-summary-shape
  (fn-scs-carryp (fn-scs-summary x))
  :hints (("Goal" :in-theory (enable fn-scs-summary fn-scs-carryp))))

(defthm fn-scs-atom-establishes-summary
  (implies (atom x) (equal (fn-scs-atom x) (fn-scs-summary x)))
  :hints (("Goal" :in-theory (e/d (fn-scs-atom fn-scs-summary fn-scc-program
                                    fn-scc-octets-valuep fn-scc-octet-listp)
                                   (fn-scs-atom-size fn-scc-atom-octets)))))

; Keystone: size maintenance at a constructor reads only the child sidecars.
(defthm fn-scs-cons-preserves-canonical-size
  (implies (and (equal a (fn-scs-summary x))
                (equal d (fn-scs-summary y)))
           (equal (fn-scs-cons a d) (fn-scs-summary (cons x y))))
  :hints (("Goal" :in-theory (e/d (fn-scs-cons fn-scs-summary fn-scc-program
                                    fn-scc-octets-valuep fn-scc-octet-listp
                                    fn-scc-nat-octets fn-scc-octetp)
                                   (fn-scs-width fn-scc-le-digits
                                    fn-scc-atom-octets)))))

(in-theory (disable fn-scs-width fn-scs-atom-size fn-scs-carryp fn-scs-atom
                    fn-scs-cons fn-scs-summary))

; Constructor helpers for fixed record spines. Shared children arrive with their
; own carries; this walks the new spine only, never a child/context value.
(defun fn-scs-carry-listp (cs)
  (declare (xargs :guard t))
  (if (consp cs)
      (and (fn-scs-carryp (car cs)) (fn-scs-carry-listp (cdr cs)))
    (null cs)))

(defthm fn-scs-atom-carryp
  (fn-scs-carryp (fn-scs-atom x))
  :hints (("Goal" :in-theory (enable fn-scs-carryp fn-scs-atom
                                    fn-scs-atom-size))))

(defthm fn-scs-cons-carryp
  (implies (and (fn-scs-carryp a) (fn-scs-carryp d))
           (fn-scs-carryp (fn-scs-cons a d)))
  :hints (("Goal" :in-theory (enable fn-scs-carryp fn-scs-cons))))

(defun fn-scs-spine (cs)
  (declare (xargs :guard (fn-scs-carry-listp cs)))
  (if (consp cs)
      (fn-scs-cons (car cs) (fn-scs-spine (cdr cs)))
    (fn-scs-atom nil)))

(defun fn-scs-correspondsp (cs xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs)
      (and (consp cs) (equal (car cs) (fn-scs-summary (car xs)))
           (fn-scs-correspondsp (cdr cs) (cdr xs)))
    (and (null cs) (null xs))))

(defthm fn-scs-spine-preserves-canonical-size
  (implies (fn-scs-correspondsp cs xs)
           (equal (fn-scs-spine cs) (fn-scs-summary xs)))
  :hints (("Goal" :induct (fn-scs-correspondsp cs xs)
           :in-theory (enable fn-scs-spine fn-scs-correspondsp))))

(in-theory (disable fn-scs-carry-listp fn-scs-spine fn-scs-correspondsp))

; A bounded decoder already knows a byte string's length. No second walk.
(defun fn-scs-octets (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) (fn-scs-atom nil)
    (list (+ 2 (fn-scs-width n) n) n nil)))

(defthm fn-scs-octets-establishes-canonical-size
  (implies (and (fn-scc-octet-listp xs) (equal n (len xs)))
           (equal (fn-scs-octets n) (fn-scs-summary xs)))
  :hints (("Goal" :in-theory (e/d (fn-scs-octets fn-scs-summary fn-scc-program
                                    fn-scc-octets-valuep fn-scc-nat-octets
                                    fn-scc-octet-listp fn-scc-octetp)
                                   (fn-scs-width fn-scc-le-digits fn-scc-atom-octets)))))
(in-theory (disable fn-scs-octets))

; Fixed-record metadata checks stop after N cells even on malformed input.
(defun fn-scs-fixed-carriesp (n cs)
  (declare (xargs :guard (natp n)))
  (if (zp n) (null cs)
    (and (consp cs) (fn-scs-carryp (car cs))
         (fn-scs-fixed-carriesp (1- n) (cdr cs)))))

(defthm fn-scs-fixed-carriesp-shape
  (implies (and (natp n) (fn-scs-fixed-carriesp n cs))
           (and (true-listp cs) (equal (len cs) n) (fn-scs-carry-listp cs)))
  :hints (("Goal" :induct (fn-scs-fixed-carriesp n cs)
           :in-theory (enable fn-scs-carry-listp)))
  :rule-classes (:rewrite (:forward-chaining
                           :trigger-terms ((fn-scs-fixed-carriesp n cs)))))
(in-theory (disable fn-scs-fixed-carriesp))
