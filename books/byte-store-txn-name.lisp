(in-package "ACL2")
(include-book "byte-store-frame")
(include-book "std/strings/explode-nonnegative-integer" :dir :system)
(include-book "std/lists/append" :dir :system)
(local (include-book "arithmetic/top" :dir :system))

(defconst *fn-bs-txn-name-minimum-width* 20)
(defconst *fn-bs-txn-name-suffix* '(#\. #\t #\x #\n))

(defun fn-bs-txn-zeroes (count)
  (declare (xargs :guard t :measure (nfix count)))
  (if (not (posp count)) nil
    (cons #\0 (fn-bs-txn-zeroes (1- count)))))

(defun fn-bs-txn-digits (n)
  (declare (xargs :guard t))
  (let ((digits (explode-nonnegative-integer (nfix n) 10 nil)))
    (append (fn-bs-txn-zeroes
             (nfix (- *fn-bs-txn-name-minimum-width* (len digits))))
            digits)))

(defun fn-bs-txn-name-chars (n)
  (declare (xargs :guard t))
  (append (fn-bs-txn-digits n) *fn-bs-txn-name-suffix*))

(defun fn-bs-txn-name-impl (n)
  (declare (xargs :guard t :verify-guards nil))
  (coerce (fn-bs-txn-name-chars n) 'string))

(local (defthm fn-bs-txn-zeroes-characters
         (character-listp (fn-bs-txn-zeroes count))))
(local (defthm fn-bs-txn-explode-characters
         (character-listp (explode-nonnegative-integer (nfix n) 10 nil))))
(defthm fn-bs-txn-name-chars-characters
  (character-listp (fn-bs-txn-name-chars n))
  :hints (("Goal" :in-theory (enable fn-bs-txn-name-chars fn-bs-txn-digits))))
(local
 (defthm fn-bs-txn-digits-true-listp
   (true-listp (fn-bs-txn-digits n))
   :hints (("Goal" :in-theory (enable fn-bs-txn-digits)))))
(defthm fn-bs-txn-zeroes-length
  (equal (len (fn-bs-txn-zeroes count)) (nfix count)))
(defthm fn-bs-txn-digits-length
  (equal (len (fn-bs-txn-digits n))
         (+ (nfix (- *fn-bs-txn-name-minimum-width*
                     (len (explode-nonnegative-integer (nfix n) 10 nil))))
            (len (explode-nonnegative-integer (nfix n) 10 nil))))
  :hints (("Goal" :in-theory (enable fn-bs-txn-digits))))
(local
 (defthm fn-bs-txn-suffix-equality-has-equal-digit-lengths
   (implies (equal (append a *fn-bs-txn-name-suffix*)
                   (append b *fn-bs-txn-name-suffix*))
            (equal (len a) (len b)))))
(verify-guards fn-bs-txn-name-impl
  :hints (("Goal" :use ((:instance fn-bs-txn-name-chars-characters (n n))))))

; A leading zero contributes zero at the most-significant end.  This local
; inverse fact is the only padding-specific arithmetic in the realization.
(local
 (defthm fn-bs-txn-basic-unexplode-trailing-zero
   (equal (basic-unexplode-core (append chars '(#\0)))
          (basic-unexplode-core chars))
   :hints (("Goal" :induct (basic-unexplode-core chars)
            :in-theory (enable basic-unexplode-core)))))

(local
 (defthm fn-bs-txn-unexplode-leading-zero
   (equal (unexplode-nonnegative-integer (cons #\0 chars))
          (unexplode-nonnegative-integer chars))
   :hints (("Goal"
            :use ((:instance fn-bs-txn-basic-unexplode-trailing-zero
                             (chars (rev chars))))
            :in-theory (enable unexplode-nonnegative-integer)))))

(local
 (defthm fn-bs-txn-unexplode-zero-prefix
   (equal (unexplode-nonnegative-integer
           (append (fn-bs-txn-zeroes count) chars))
          (unexplode-nonnegative-integer chars))
   :hints (("Goal" :induct (fn-bs-txn-zeroes count)
            :in-theory (enable fn-bs-txn-zeroes)))))

(defthm fn-bs-txn-digits-decode
  (equal (unexplode-nonnegative-integer (fn-bs-txn-digits n))
         (nfix n))
  :hints (("Goal"
           :use ((:instance fn-bs-txn-unexplode-zero-prefix
                            (count (nfix (- *fn-bs-txn-name-minimum-width*
                                            (len (explode-nonnegative-integer
                                                  (nfix n) 10 nil)))))
                            (chars (explode-nonnegative-integer (nfix n) 10 nil)))
                 (:instance unexplode-nonnegative-integer-of-explode-nonnegative-integer
                            (n (nfix n))))
           :in-theory (enable fn-bs-txn-digits))))

(local
 (defthm fn-bs-txn-coerce-inverse
   (implies (character-listp chars)
            (equal (coerce (coerce chars 'string) 'list) chars))
   :rule-classes nil
   :hints (("Goal" :use coerce-inverse-2))))

(defthm fn-bs-txn-name-chars-equal-implies-digits-equal
  (implies (equal (fn-bs-txn-name-chars i) (fn-bs-txn-name-chars j))
           (equal (fn-bs-txn-digits i) (fn-bs-txn-digits j)))
  :hints (("Goal"
           :use ((:instance fn-bs-txn-digits-true-listp (n i))
                 (:instance fn-bs-txn-digits-true-listp (n j)))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '((:definition fn-bs-txn-name-chars)
              (:rewrite equal-of-append-and-append-same-arg2)
              (:rewrite list-fix-when-true-listp)))))
  :rule-classes nil)

(defthm fn-bs-txn-name-impl-equal-implies-chars-equal
  (implies (equal (fn-bs-txn-name-impl i) (fn-bs-txn-name-impl j))
           (equal (fn-bs-txn-name-chars i) (fn-bs-txn-name-chars j)))
  :hints (("Goal"
           :use ((:instance fn-bs-txn-coerce-inverse (chars (fn-bs-txn-name-chars i)))
                 (:instance fn-bs-txn-coerce-inverse (chars (fn-bs-txn-name-chars j)))
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
