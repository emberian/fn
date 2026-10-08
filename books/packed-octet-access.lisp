; fn: indexed access to a packed body without copying a bignum suffix.
(in-package "ACL2")
(include-book "packed-octets")
(local (include-book "arithmetic-5/top" :dir :system))
; Each octet uses eight LOGBITP observations of the original natural.
; The local arithmetic proves the bit slice and total unpacked length.


(defun fn-poa-bits (width index n)
  (declare (xargs :guard (and (natp width) (natp index) (integerp n))))
  (if (zp width) 0
    (+ (if (logbitp index n) 1 0)
       (* 2 (fn-poa-bits (- width 1) (+ index 1) n)))))

(local (defthm fn-paa-low-bit
 (implies (integerp n)
  (equal (if (logbitp 0 n) 1 0) (mod n 2)))
 :hints (("Goal" :in-theory (enable logbitp oddp evenp)))))

(local (defthm fn-paa-mod-decompose
 (implies (and (integerp n) (posp p))
  (equal (mod n (* 2 p))
         (+ (mod n 2) (* 2 (mod (floor n 2) p)))))))

(local (in-theory (disable fn-paa-mod-decompose)))

(local (defthm fn-paa-floor-compose
 (implies (and (integerp n) (natp index))
  (equal (floor (floor n (expt 2 index)) 2)
         (floor n (expt 2 (+ 1 index)))))
 :hints (("Goal" :expand ((expt 2 (+ 1 index)))))))

(local (defthm fn-paa-index-bit
 (implies (and (natp index) (integerp n))
  (equal (mod (floor n (expt 2 index)) 2)
         (if (logbitp index n) 1 0)))
 :hints (("Goal" :use ((:instance fn-paa-low-bit (n (floor n (expt 2 index)))))
          :in-theory (e/d (logbitp) (fn-paa-low-bit))))))

(local (defthm fn-paa-mod-one (implies (integerp n) (equal (mod n 1) 0))))

(local (defthm fn-paa-bits-is-slice
 (implies (and (natp width) (natp index) (integerp n))
  (equal (fn-poa-bits width index n)
         (mod (floor n (expt 2 index)) (expt 2 width))))
 :hints (("Goal" :induct (fn-poa-bits width index n)
          :in-theory (union-theories
            '(fn-poa-bits natp zp zip fix posp fn-paa-index-bit fn-paa-floor-compose fn-paa-mod-one
              default-+-1 default-+-2 default-*-1 default-*-2
              commutativity-of-+ expt-type-prescription-integerp-base
              expt-type-prescription-positive-base (:type-prescription floor) (:type-prescription fn-poa-bits))
            (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))))
         ("Subgoal *1/2" :use ((:instance fn-paa-mod-decompose
                              (n (floor n (expt 2 index))) (p (expt 2 (- width 1)))))
          :expand ((expt 2 width))))))

(local (defthm fn-paa-tail-decompose
 (implies (and (integerp n) (posp index))
  (equal (floor n (expt 2 index))
         (floor (floor n 2) (expt 2 (- index 1)))))
 :hints (("Goal" :expand ((expt 2 index))))))

(local (defthm fn-paa-half-length
 (implies (natp n)
  (equal (integer-length (floor n 2))
         (nfix (- (integer-length n) 1))))
 :hints (("Goal" :expand ((integer-length n))
          :in-theory (disable integer-length)))))

(local (defun fn-paa-tail-ind (index n)
 (if (zp index) n (fn-paa-tail-ind (- index 1) (floor n 2)))))

(local (defthm fn-paa-floor-one (implies (integerp n) (equal (floor n 1) n))))

(local (defthm fn-paa-length-of-tail
 (implies (and (natp index) (natp n))
  (equal (integer-length (floor n (expt 2 index)))
         (nfix (- (integer-length n) index))))
 :hints (("Goal" :induct (fn-paa-tail-ind index n)
          :in-theory (union-theories
           '(natp nfix zp posp fn-paa-half-length fn-paa-floor-one (:induction fn-paa-tail-ind)
             default-+-1 default-+-2 default-unary-minus
             commutativity-of-+ associativity-of-+ commutativity-2-of-+
             (:type-prescription floor) floor-nonnegative (:type-prescription integer-length))
           (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))))
         ("Subgoal *1/2" :use ((:instance fn-paa-tail-decompose))))))

(local (in-theory (disable fn-paa-tail-decompose fn-paa-index-bit)))

(local (defthm fn-paa-zero-length
 (implies (natp n)
  (equal (equal (integer-length n) 0) (equal n 0)))
 :hints (("Goal" :expand ((integer-length n)) :in-theory (disable integer-length)))))

(local (defthm fn-paa-length-floor-eight
 (implies (natp n)
  (equal (integer-length (floor n 256)) (nfix (- (integer-length n) 8))))
 :hints (("Goal" :use ((:instance fn-paa-length-of-tail (index 8)))
          :in-theory (disable fn-paa-length-of-tail integer-length)))))

(local (defthm fn-paa-small-length
 (implies (and (natp n) (< n 256)) (<= (integer-length n) 8))
 :rule-classes :linear
 :hints (("Goal" :use ((:instance fn-paa-length-floor-eight))
          :in-theory (disable integer-length fn-paa-length-floor-eight)))))

(local (defthm fn-paa-large-length
 (implies (and (natp n) (<= 256 n)) (< 8 (integer-length n)))
 :rule-classes :linear
 :hints (("Goal" :use ((:instance fn-paa-length-floor-eight))
          :in-theory (disable integer-length fn-paa-length-floor-eight)))))

(defun fn-poa-length (n)
 (declare (xargs :guard t))
 (nfix (floor (- (integer-length (nfix n)) 1) 8)))

(defthm fn-poa-length-is-unpack-length
 (equal (fn-poa-length n) (len (fn-bch-unpack n)))
 :hints (("Goal" :induct (fn-bch-unpack n)
          :in-theory (e/d (fn-poa-length fn-bch-unpack) (integer-length)))))

(defun fn-poa-octet (index n)
 (declare (xargs :guard t))
 (fn-poa-bits 8 (* 8 (nfix index)) (nfix n)))

(local (defthm fn-paa-octet-is-slice
 (equal (fn-poa-octet index n)
        (mod (floor (nfix n) (expt 2 (* 8 (nfix index)))) 256))
 :hints (("Goal" :in-theory (e/d (fn-poa-octet) (fn-poa-bits))))))

(local (defthm fn-paa-octet-zero
 (implies (natp n) (equal (fn-poa-octet 0 n) (mod n 256)))))

(local (defthm fn-paa-octet-next
 (implies (and (natp index) (natp n))
  (equal (fn-poa-octet (+ 1 index) n)
         (fn-poa-octet index (floor n 256))))
 :hints (("Goal" :in-theory (disable fn-poa-octet fn-poa-bits)))))

(local (defthm fn-paa-octet-is-nth
 (implies (and (natp index) (< index (len (fn-bch-unpack n))))
  (equal (fn-poa-octet index n) (nth index (fn-bch-unpack n))))
 :hints (("Goal" :induct (fn-bch-digits n index)
          :in-theory (e/d (fn-bch-unpack nth)
                    (fn-poa-octet fn-paa-octet-is-slice fn-poa-bits integer-length))
          :expand ((fn-poa-octet 0 n)))
         ("Subgoal *1/2" :use ((:instance fn-paa-octet-next (index (- index 1))))))))

(local (defthm fn-paa-nth-of-nfix
 (equal (nth (nfix index) xs) (nth index xs))
 :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-poa-octet-is-indexed-octet
 (implies (< (nfix index) (len (fn-bch-unpack n)))
  (equal (fn-poa-octet index n) (nth index (fn-bch-unpack n))))
 :hints (("Goal" :use ((:instance fn-paa-octet-is-nth (index (nfix index))))
          :in-theory (e/d (fn-poa-octet) (fn-paa-octet-is-nth fn-paa-octet-is-slice fn-poa-bits)))))

(defthm fn-poa-octet-bound
 (and (natp (fn-poa-octet index n)) (< (fn-poa-octet index n) 256))
 :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :in-theory (disable fn-poa-octet fn-poa-bits fn-paa-octet-is-nth fn-poa-octet-is-indexed-octet
                                      |(mod (floor x y) z)|))))

(in-theory (disable fn-poa-bits fn-poa-length fn-poa-octet))
