(in-package "ACL2")
(include-book "byte-store-frame")
(local (include-book "arithmetic/top" :dir :system))

(defconst *fn-bs-txn-name-minimum-width* 20)
(defconst *fn-bs-txn-name-suffix* '(#\. #\t #\x #\n))

(defun fn-bs-txn-zeroes (count)
  (declare (xargs :guard t :measure (nfix count)))
  (if (not (posp count)) nil
    (cons #\0 (fn-bs-txn-zeroes (1- count)))))

; ACL2's decimal printer is a :program function whose useful inverse theorems
; live in an optional std/strings book.  Keep this deployment-facing codec
; portable by defining the small logical renderer it needs here.  This list is
; least-significant digit first, which gives it a direct arithmetic inverse.
(defun fn-bs-txn-natural-digits-rev (n)
  (declare (xargs :guard t :measure (nfix n)))
  (let ((n (nfix n)))
    (if (< n 10)
        (list (digit-to-char n))
      (cons (digit-to-char (mod n 10))
            (fn-bs-txn-natural-digits-rev (floor n 10))))))

(defun fn-bs-txn-reverse (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (append (fn-bs-txn-reverse (cdr xs)) (list (car xs)))
    nil))

(defun fn-bs-txn-natural-digits (n)
  (declare (xargs :guard t))
  (fn-bs-txn-reverse (fn-bs-txn-natural-digits-rev n)))

(defun fn-bs-txn-digits (n)
  (declare (xargs :guard t))
  (let ((digits (fn-bs-txn-natural-digits n)))
    (append (fn-bs-txn-zeroes
             (nfix (- *fn-bs-txn-name-minimum-width* (len digits))))
            digits)))

(defun fn-bs-txn-name-chars (n)
  (declare (xargs :guard t))
  (append (fn-bs-txn-digits n) *fn-bs-txn-name-suffix*))

(defun fn-bs-txn-name-impl (n)
  (declare (xargs :guard t :verify-guards nil))
  (coerce (fn-bs-txn-name-chars n) 'string))

(local
 (defun fn-bs-txn-digit-value (char)
   (declare (xargs :guard t))
   (case char
     (#\1 1) (#\2 2) (#\3 3) (#\4 4) (#\5 5)
     (#\6 6) (#\7 7) (#\8 8) (#\9 9)
     (otherwise 0))))

(local
 (defun fn-bs-txn-undigits-rev (chars)
   (declare (xargs :guard t))
   (if (consp chars)
       (+ (fn-bs-txn-digit-value (car chars))
          (* 10 (fn-bs-txn-undigits-rev (cdr chars))))
     0)))

(local
 (defun fn-bs-txn-decode-digits (chars)
   (declare (xargs :guard t))
   (fn-bs-txn-undigits-rev (fn-bs-txn-reverse chars))))

(local
 (defthm fn-bs-txn-append-associative
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-bs-txn-append-nil-right
   (implies (true-listp xs) (equal (append xs nil) xs))))

(local
 (defthm fn-bs-txn-reverse-true-listp
   (true-listp (fn-bs-txn-reverse xs))))

(local
 (defthm fn-bs-txn-reverse-append
   (equal (fn-bs-txn-reverse (append a b))
          (append (fn-bs-txn-reverse b) (fn-bs-txn-reverse a)))
   :hints (("Goal" :induct (append a b)))))

(local
 (defthm fn-bs-txn-reverse-involution
   (implies (true-listp xs)
            (equal (fn-bs-txn-reverse (fn-bs-txn-reverse xs)) xs))))

(local
 (defthm fn-bs-txn-digit-value-of-digit-to-char
   (implies (and (natp digit) (< digit 10))
            (equal (fn-bs-txn-digit-value (digit-to-char digit)) digit))
   :hints (("Goal" :in-theory (enable digit-to-char)))))

(local
 (defthm fn-bs-txn-natural-digits-rev-characters
   (character-listp (fn-bs-txn-natural-digits-rev n))
   :hints (("Goal" :in-theory (enable fn-bs-txn-natural-digits-rev)))))

(local
 (defthm fn-bs-txn-natural-digits-rev-true-listp
   (true-listp (fn-bs-txn-natural-digits-rev n))))

(local
 (defthm fn-bs-txn-undigits-rev-append-zeroes
   (equal (fn-bs-txn-undigits-rev
           (append chars (fn-bs-txn-zeroes count)))
          (fn-bs-txn-undigits-rev chars))
   :hints (("Goal" :induct (fn-bs-txn-undigits-rev chars)))))

(local
 (defthm fn-bs-txn-undigits-rev-inverts-natural-digits-rev
   (equal (fn-bs-txn-undigits-rev (fn-bs-txn-natural-digits-rev n))
          (nfix n))
   :hints (("Goal"
            :in-theory (e/d (fn-bs-txn-natural-digits-rev) (floor mod))
            :induct (fn-bs-txn-natural-digits-rev n)))))

(local
 (defthm fn-bs-txn-append-zero-to-zeroes
   (equal (append (fn-bs-txn-zeroes count) '(#\0))
          (cons #\0 (fn-bs-txn-zeroes count)))
   :hints (("Goal" :induct (fn-bs-txn-zeroes count)
            :in-theory (e/d (fn-bs-txn-zeroes) (floor mod))))))

(local
 (defthm fn-bs-txn-reverse-zeroes
   (equal (fn-bs-txn-reverse (fn-bs-txn-zeroes count))
          (fn-bs-txn-zeroes count))
   :hints (("Goal" :induct (fn-bs-txn-zeroes count)
            :in-theory (e/d (fn-bs-txn-reverse fn-bs-txn-zeroes)
                            (floor mod))))))

(local
 (defthm fn-bs-txn-decode-digits-left-inverse
   (equal (fn-bs-txn-decode-digits (fn-bs-txn-digits n)) (nfix n))
   :hints (("Goal"
            :use ((:instance fn-bs-txn-reverse-involution
                             (xs (fn-bs-txn-natural-digits-rev n))))
            :in-theory (enable fn-bs-txn-decode-digits fn-bs-txn-digits
                               fn-bs-txn-natural-digits)))))

(local
 (defthm fn-bs-txn-zeroes-characters
   (character-listp (fn-bs-txn-zeroes count))))

(defthm fn-bs-txn-name-chars-characters
  (character-listp (fn-bs-txn-name-chars n))
  :hints (("Goal" :in-theory (enable fn-bs-txn-name-chars fn-bs-txn-digits
                                      fn-bs-txn-natural-digits))))

(local
 (defthm fn-bs-txn-digits-true-listp
   (true-listp (fn-bs-txn-digits n))
   :hints (("Goal" :in-theory (enable fn-bs-txn-digits
                                       fn-bs-txn-natural-digits)))))

(defthm fn-bs-txn-zeroes-length
  (equal (len (fn-bs-txn-zeroes count)) (nfix count)))

(local
 (defthm fn-bs-txn-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(defthm fn-bs-txn-digits-length
  (equal (len (fn-bs-txn-digits n))
         (+ (nfix (- *fn-bs-txn-name-minimum-width*
                     (len (fn-bs-txn-natural-digits n))))
            (len (fn-bs-txn-natural-digits n))))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:definition fn-bs-txn-digits)
              (:definition nfix)
              (:rewrite fn-bs-txn-len-append)
              (:rewrite fn-bs-txn-zeroes-length))))))

(verify-guards fn-bs-txn-name-impl
  :hints (("Goal" :use ((:instance fn-bs-txn-name-chars-characters (n n))))))

(local
 (defthm fn-bs-txn-digits-decode
   (equal (fn-bs-txn-decode-digits (fn-bs-txn-digits n)) (nfix n))
   :hints (("Goal" :use fn-bs-txn-decode-digits-left-inverse))))

(local
 (defthm fn-bs-txn-cancel-equal-prefix
   (implies (and (true-listp a) (true-listp b))
            (equal (equal (append prefix a) (append prefix b))
                   (equal a b)))
   :hints (("Goal" :induct (append prefix a)))))

(local
 (defthm fn-bs-txn-cancel-equal-suffix
   (implies (and (true-listp a) (true-listp b))
            (equal (equal (append a suffix) (append b suffix))
                   (equal a b)))
   :hints (("Goal"
            :use ((:instance fn-bs-txn-reverse-append (a a) (b suffix))
                  (:instance fn-bs-txn-reverse-append (a b) (b suffix))
                  (:instance fn-bs-txn-cancel-equal-prefix
                             (prefix (fn-bs-txn-reverse suffix))
                             (a (fn-bs-txn-reverse a))
                             (b (fn-bs-txn-reverse b)))
                  (:instance fn-bs-txn-reverse-true-listp (xs a))
                  (:instance fn-bs-txn-reverse-true-listp (xs b))
                  (:instance fn-bs-txn-reverse-involution (xs a))
                  (:instance fn-bs-txn-reverse-involution (xs b)))
            :in-theory (theory 'minimal-theory)))))

(defthm fn-bs-txn-name-chars-equal-implies-digits-equal
  (implies (equal (fn-bs-txn-name-chars i) (fn-bs-txn-name-chars j))
           (equal (fn-bs-txn-digits i) (fn-bs-txn-digits j)))
  :hints (("Goal"
           :use ((:instance fn-bs-txn-digits-true-listp (n i))
                 (:instance fn-bs-txn-digits-true-listp (n j))
                 (:instance fn-bs-txn-cancel-equal-suffix
                            (a (fn-bs-txn-digits i))
                            (b (fn-bs-txn-digits j))
                            (suffix *fn-bs-txn-name-suffix*)))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '((:definition fn-bs-txn-name-chars)))))
  :rule-classes nil)

(local
 (defthm fn-bs-txn-coerce-inverse
   (implies (character-listp chars)
            (equal (coerce (coerce chars 'string) 'list) chars))
   :rule-classes nil
   :hints (("Goal" :use coerce-inverse-2))))

(defthm fn-bs-txn-name-impl-equal-implies-chars-equal
  (implies (equal (fn-bs-txn-name-impl i) (fn-bs-txn-name-impl j))
           (equal (fn-bs-txn-name-chars i) (fn-bs-txn-name-chars j)))
  :hints (("Goal"
           :use ((:instance fn-bs-txn-coerce-inverse
                            (chars (fn-bs-txn-name-chars i)))
                 (:instance fn-bs-txn-coerce-inverse
                            (chars (fn-bs-txn-name-chars j)))
                 (:instance fn-bs-txn-name-chars-characters (n i))
                 (:instance fn-bs-txn-name-chars-characters (n j)))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '((:definition fn-bs-txn-name-impl)))))
  :rule-classes nil)

(defthm fn-bs-txn-digits-equal-implies-nfix-equal
  (implies (equal (fn-bs-txn-digits i) (fn-bs-txn-digits j))
           (equal (nfix i) (nfix j)))
  :hints (("Goal" :use ((:instance fn-bs-txn-digits-decode (n i))
                         (:instance fn-bs-txn-digits-decode (n j)))
           :in-theory (theory 'minimal-theory)))
  :rule-classes nil)

(defthm fn-bs-txn-name-impl-injective
  (implies (and (natp i) (natp j)
                (equal (fn-bs-txn-name-impl i) (fn-bs-txn-name-impl j)))
           (equal i j))
  :hints (("Goal" :use (fn-bs-txn-name-impl-equal-implies-chars-equal
                         fn-bs-txn-name-chars-equal-implies-digits-equal
                         fn-bs-txn-digits-equal-implies-nfix-equal)
           :in-theory (union-theories (theory 'minimal-theory)
                                      '((:definition nfix)
                                        (:compound-recognizer
                                         natp-compound-recognizer)))))
  :rule-classes nil)

(defattach (fn-bs-txn-name fn-bs-txn-name-impl)
  :hints (("Goal" :use fn-bs-txn-name-impl-injective)))
