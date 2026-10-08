; Shared total list helpers and CRLF framing from wire-grammar.
; Extracted without changing the function or theorem forms; the full grammar
; still includes these events. Statement transport needs only this layer.
(in-package "ACL2")
(include-book "cbor-invariants")
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (enable fn-cbor-octet-listp)))

(defun fn-wg-take (n xs)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil
    (cons (if (consp xs) (car xs) nil)
          (fn-wg-take (1- n) (if (consp xs) (cdr xs) nil)))))

(defun fn-wg-drop (n xs)
  (declare (xargs :guard (natp n)))
  (if (zp n) xs
    (fn-wg-drop (1- n) (if (consp xs) (cdr xs) nil))))

(defun fn-wg-prefixp (p xs)
  (declare (xargs :guard t))
  (if (consp p)
      (and (consp xs) (equal (car p) (car xs))
           (fn-wg-prefixp (cdr p) (cdr xs)))
    t))

(defun fn-wg-app (xs ys)
  (declare (xargs :guard t))
  (if (consp xs) (cons (car xs) (fn-wg-app (cdr xs) ys)) ys))

(defthm fn-wg-len-of-drop
  (equal (len (fn-wg-drop n xs)) (nfix (- (len xs) (nfix n)))))

(defthm fn-wg-len-of-take
  (equal (len (fn-wg-take n xs)) (nfix n)))

(defthm fn-wg-len-of-app
  (equal (len (fn-wg-app xs ys)) (+ (len xs) (len ys))))

(defthm fn-wg-app-is-append
  (implies (true-listp xs) (equal (fn-wg-app xs ys) (append xs ys))))

(in-theory (disable fn-wg-app-is-append))

(defthm fn-wg-app-assoc
  (equal (fn-wg-app (fn-wg-app xs ys) zs) (fn-wg-app xs (fn-wg-app ys zs))))

(defthm fn-wg-take-of-app
  (implies (equal (nfix n) (len xs))
           (equal (fn-wg-take n (fn-wg-app xs ys)) (true-list-fix xs)))
  :hints (("Goal" :induct (fn-wg-take n xs))))

(defthm fn-wg-drop-of-app
  (implies (equal (nfix n) (len xs))
           (equal (fn-wg-drop n (fn-wg-app xs ys)) ys))
  :hints (("Goal" :induct (fn-wg-drop n xs))))

(defthm fn-wg-prefixp-of-app
  (implies (true-listp p) (fn-wg-prefixp p (fn-wg-app p ys))))

(defthm fn-wg-app-take-drop
  (implies (<= (nfix n) (len xs))
           (equal (fn-wg-app (fn-wg-take n xs) (fn-wg-drop n xs)) xs))
  :hints (("Goal" :induct (fn-wg-drop n xs))))

(defthm fn-wg-prefixp-app-drop
  (implies (and (fn-wg-prefixp p xs) (true-listp p))
           (equal (fn-wg-app p (fn-wg-drop (len p) xs)) xs)))

(defthm fn-wg-prefixp-len
  (implies (fn-wg-prefixp p xs) (<= (len p) (len xs)))
  :rule-classes :linear)

(defthm fn-wg-true-listp-of-take
  (true-listp (fn-wg-take n xs)))

(defthm fn-wg-take-of-len
  (implies (equal (nfix n) (len xs)) (equal (fn-wg-take n xs) (true-list-fix xs)))
  :hints (("Goal" :induct (fn-wg-take n xs))))

(defthm fn-wg-true-listp-of-app
  (equal (true-listp (fn-wg-app xs ys)) (true-listp ys)))

(defthm fn-wg-octets-of-app
  (implies (and (fn-cbor-octet-listp xs) (fn-cbor-octet-listp ys))
           (fn-cbor-octet-listp (fn-wg-app xs ys))))

(defthm fn-wg-app-nil
  (implies (true-listp xs) (equal (fn-wg-app xs nil) xs)))

(defthm fn-wg-consp-of-app
  (equal (consp (fn-wg-app xs ys)) (or (consp xs) (consp ys))))

(defthm fn-wg-octets-of-take
  (implies (and (fn-cbor-octet-listp xs) (<= (nfix n) (len xs)))
           (fn-cbor-octet-listp (fn-wg-take n xs))))

(defthm fn-wg-octets-of-drop
  (implies (fn-cbor-octet-listp xs)
           (fn-cbor-octet-listp (fn-wg-drop n xs))))

(defthm fn-wg-true-listp-of-drop
  (implies (true-listp xs) (true-listp (fn-wg-drop n xs))))

(defthm fn-wg-drop-of-app-longer
  (implies (<= (len xs) (nfix n))
           (equal (fn-wg-drop n (fn-wg-app xs ys)) (fn-wg-drop (- (nfix n) (len xs)) ys)))
  :hints (("Goal" :induct (fn-wg-drop n xs))))

(defthm fn-wg-true-list-fix-of-take
  (equal (true-list-fix (fn-wg-take n xs)) (fn-wg-take n xs)))

(defthm fn-wg-consp-of-drop
  (implies (< (nfix n) (len xs)) (consp (fn-wg-drop n xs))))

(defun fn-wg-lines (w text)
  (declare (xargs :guard (natp w) :measure (len text)))
  (if (or (not (consp text)) (zp w)) nil
    (if (<= (len text) w)
        (fn-wg-app text (list 13 10))
      (fn-wg-app (fn-wg-take w text)
                 (cons 13 (cons 10 (fn-wg-lines w (fn-wg-drop w text))))))))

(defun fn-wg-unlines (w xs)
  (declare (xargs :guard (natp w) :measure (len xs)))
  (if (or (not (consp xs)) (zp w)) nil
    (if (<= (len xs) (+ w 2))
        (fn-wg-take (nfix (- (len xs) 2)) xs)
      (fn-wg-app (fn-wg-take w xs)
                 (fn-wg-unlines w (fn-wg-drop (+ w 2) xs))))))

(local (defthm fn-wg-consp-when-len-positive
  (implies (< 0 (len x)) (consp x))))

(defthm fn-wg-lines-octets
  (implies (fn-cbor-octet-listp text)
           (fn-cbor-octet-listp (fn-wg-lines w text))))

(defthm fn-wg-lines-consp
  (implies (and (consp text) (posp w)) (consp (fn-wg-lines w text))))

(defthm fn-wg-lines-len-positive
  (implies (and (consp text) (posp w)) (< 0 (len (fn-wg-lines w text))))
  :rule-classes :linear)

(defthm fn-wg-unlines-of-lines
  (implies (and (posp w) (true-listp text))
           (equal (fn-wg-unlines w (fn-wg-lines w text)) text))
  :hints (("Goal" :induct (fn-wg-lines w text))
          ("Subgoal *1/3" :expand ((fn-wg-unlines w (fn-wg-app (fn-wg-take w text)
                                       (list* 13 10 (fn-wg-lines w (fn-wg-drop w text)))))))
          ("Subgoal *1/2" :expand ((fn-wg-unlines w (fn-wg-app text '(13 10)))))))
