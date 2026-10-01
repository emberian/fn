; Proof-only source slice to actual BLAKE3 input boundary.
(in-package "ACL2")
(include-book "blake3-stobj")
(include-book "octet-window")

(local
 (defun ewsw-prefix-induct (j n xs)
  (declare (xargs :measure (nfix j)))
  (if (or (zp j) (zp n) (atom xs)) nil
    (ewsw-prefix-induct (1- j) (1- n) (cdr xs)))))

(local
 (defthm ewsw-nthx-firstn
  (implies (and (natp j) (natp n) (< j n))
           (equal (fn-b3-nthx j (fn-b3-firstn n xs)) (fn-b3-nthx j xs)))
  :hints (("Goal" :induct (ewsw-prefix-induct j n xs)
                  :in-theory (enable fn-b3-nthx fn-b3-firstn)
                  :expand ((fn-b3-firstn n xs))))))

(local
 (defthm ewsw-nthcdr-firstn
  (implies (and (natp j) (natp n) (<= j n))
           (equal (fn-b3-nthcdrx j (fn-b3-firstn n xs))
                  (fn-b3-firstn (- n j) (fn-b3-nthcdrx j xs))))
  :hints (("Goal" :induct (ewsw-prefix-induct j n xs)
                  :in-theory (enable fn-b3-nthcdrx fn-b3-firstn)
                  :expand ((fn-b3-firstn n xs))))))

(local
 (defun ewsw-words-induct (k n xs)
  (declare (xargs :measure (nfix k)))
  (if (zp k) (list n xs)
    (ewsw-words-induct (1- k) (- n 4) (fn-b3-nthcdrx 4 xs)))))

(local
 (defthm ewsw-zero-words-by-definition
  (equal (fn-b3-words 0 xs) nil)
  :hints (("Goal" :in-theory (enable fn-b3-words)))))

(defthm fn-ews-words-of-enough-prefix
 (implies (and (natp k) (natp n) (<= (* 4 k) n))
          (equal (fn-b3-words k (fn-b3-firstn n xs)) (fn-b3-words k xs)))
 :hints (("Goal" :induct (ewsw-words-induct k n xs)
                  :expand ((fn-b3-words k (fn-b3-firstn n xs)) (fn-b3-words k xs))
                  :in-theory (disable fn-b3-words fn-b3-firstn fn-b3-nthx fn-b3-nthcdrx))))

(local
 (defthm ewsw-firstn-all
  (implies (and (true-listp xs) (natp n) (<= (len xs) n))
           (equal (fn-b3-firstn n xs) xs))
  :hints (("Goal" :induct (fn-b3-firstn n xs)
                  :in-theory (enable fn-b3-firstn)))))

(local
 (defthm ewsw-firstn-of-firstn
  (equal (fn-b3-firstn n (fn-b3-firstn m xs))
         (fn-b3-firstn (min (nfix n) (nfix m)) xs))
  :hints (("Goal" :induct (ewsw-prefix-induct n m xs)
                  :in-theory (enable fn-b3-firstn min)))))

(defthm fn-ews-words-of-exact-prefix
 (implies (and (natp k) (true-listp xs))
          (equal (fn-b3-words k (fn-b3-firstn (min (* 4 k) (len xs)) xs))
                 (fn-b3-words k xs)))
 :hints (("Goal" :cases ((<= (* 4 k) (len xs)))
                  :in-theory (enable min))))

(local
 (defthm ewsw-nthcdr-is-nthcdrx
  (implies (true-listp xs)
           (equal (nthcdr (nfix n) xs) (fn-b3-nthcdrx n xs)))
  :hints (("Goal" :induct (fn-b3-nthcdrx n xs)
                  :in-theory (enable fn-b3-nthcdrx nthcdr)))))

(local
 (defthm ewsw-take-is-firstn
  (implies (and (natp n) (<= n (len xs)))
           (equal (take n xs) (fn-b3-firstn n xs)))
  :hints (("Goal" :induct (fn-b3-firstn n xs)
                  :in-theory (enable fn-b3-firstn take)))))

(local
 (defthm ewsw-natural-nthcdr
  (implies (and (natp n) (true-listp xs))
           (equal (nthcdr n xs) (fn-b3-nthcdrx n xs)))
  :hints (("Goal" :use ewsw-nthcdr-is-nthcdrx))))

(defthm fn-ews-window-words-are-span-words
 (implies (and (natp k) (natp start) (natp count)
               (true-listp msg) (<= start (len msg)))
          (equal (fn-b3-words k
                   (fn-shr-win start (min (* 4 k) (min count (- (len msg) start))) msg))
                 (fn-b3-words k (fn-b3-firstn count (fn-b3-nthcdrx start msg)))))
 :hints (("Goal" :do-not-induct t
  :use (:instance fn-ews-words-of-exact-prefix
         (xs (fn-b3-firstn count (fn-b3-nthcdrx start msg))))
  :in-theory (e/d (fn-shr-win) (fn-b3-words fn-b3-firstn fn-b3-nthcdrx
                               fn-ews-words-of-exact-prefix)))))
