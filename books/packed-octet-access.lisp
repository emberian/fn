; fn: indexed access to a packed body without copying a bignum suffix.
(in-package "ACL2")
(include-book "packed-octets")
(local (include-book "ihs/logops-lemmas" :dir :system))

; Width is eight at the octet boundary. LOGBITP observes the original N;
; recursion builds only the small result, never a shifted copy of N.
(defun fn-poa-bits (width index n)
  (declare (xargs :guard (and (natp width) (natp index) (integerp n))))
  (if (zp width) 0
    (+ (if (logbitp index n) 1 0)
       (* 2 (fn-poa-bits (- width 1) (+ index 1) n)))))

(local (defthm fn-poa-low-bit
 (implies (integerp n)
  (equal (if (logbitp 0 n) 1 0) (logcar n)))
 :hints (("Goal" :in-theory (e/d (logbitp* bitp) (logbitp logcar))))))

(local (defthm fn-poa-next-tail
 (implies (and (natp index) (integerp n))
  (equal (logcdr (logtail index n)) (logtail (+ 1 index) n)))
 :hints (("Goal" :use ((:instance logtail-logtail (pos index) (pos1 1) (i n)))
          :in-theory (e/d (logtail*) (logtail-logtail logtail logcdr))))))

(local (defthm fn-poa-index-bit
 (implies (and (natp index) (integerp n))
  (equal (logcar (logtail index n)) (if (logbitp index n) 1 0)))
 :hints (("Goal" :use ((:instance fn-poa-low-bit (n (logtail index n))))
          :in-theory (disable fn-poa-low-bit logcar logtail logbitp)))))

(local (defthm fn-poa-bits-is-slice
 (implies (and (natp width) (natp index) (integerp n))
  (equal (fn-poa-bits width index n)
         (loghead width (logtail index n))))
 :hints (("Goal" :induct (fn-poa-bits width index n)
          :in-theory (e/d (fn-poa-bits loghead* logcons)
                          (loghead logtail logcdr logcar logbitp))
          :expand ((loghead width (logtail index n)))))))

(local (defun fn-poa-tail-ind (index n)
 (if (zp index) n (fn-poa-tail-ind (- index 1) (logcdr n)))))

(local (defthm fn-poa-length-of-tail
 (implies (and (natp index) (natp n))
  (equal (integer-length (logtail index n))
         (nfix (- (integer-length n) index))))
 :hints (("Goal" :induct (fn-poa-tail-ind index n)
          :in-theory (e/d (logtail* integer-length*)
                          (logtail integer-length logcdr))))))

; Drop the most significant base-256 digit, exactly as FN-BCH-UNPACK does.
; The equality below is total, including noncanonical natural encodings.
(defun fn-poa-length (n)
 (declare (xargs :guard t))
 (nfix (floor (- (integer-length (nfix n)) 1) 8)))

(local (defthm fn-poa-tail-eight
 (implies (natp n) (equal (logtail 8 n) (floor n 256)))
 :hints (("Goal" :in-theory (enable logtail)))))

(local (defthm fn-poa-length-floor-eight
 (implies (natp n)
  (equal (integer-length (floor n 256))
         (nfix (- (integer-length n) 8))))
 :hints (("Goal" :use ((:instance fn-poa-length-of-tail (index 8)))
          :in-theory (disable fn-poa-length-of-tail integer-length logtail)))))

(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm fn-poa-small-length
 (implies (and (natp n) (< n 256)) (<= (integer-length n) 8))
 :rule-classes :linear
 :hints (("Goal" :use ((:instance integer-length-unsigned-byte (size 8) (i n)))
          :in-theory (enable unsigned-byte-p)))))

(local (defthm fn-poa-large-length
 (implies (and (natp n) (<= 256 n)) (< 8 (integer-length n)))
 :rule-classes :linear
 :hints (("Goal" :use ((:instance fn-poa-length-floor-eight))
          :in-theory (e/d (equal-integer-length-0)
                         (integer-length fn-poa-length-floor-eight))))))

(defthm fn-poa-length-is-unpack-length
 (equal (fn-poa-length n) (len (fn-bch-unpack n)))
 :hints (("Goal" :induct (fn-bch-unpack n)
          :in-theory (e/d (fn-poa-length fn-bch-unpack) (integer-length)))))

(defun fn-poa-octet (index n)
 (declare (xargs :guard t))
 (fn-poa-bits 8 (* 8 (nfix index)) (nfix n)))

(local (defthm fn-poa-octet-is-slice
 (equal (fn-poa-octet index n)
        (loghead 8 (logtail (* 8 (nfix index)) (nfix n))))
 :hints (("Goal" :in-theory (e/d (fn-poa-octet)
                               (fn-poa-bits loghead logtail))))))

(local (defthm fn-poa-octet-zero
 (implies (natp n) (equal (fn-poa-octet 0 n) (mod n 256)))
 :hints (("Goal" :in-theory (enable loghead logtail)))))

(local (defthm fn-poa-octet-next
 (implies (and (natp index) (natp n))
  (equal (fn-poa-octet (+ 1 index) n)
         (fn-poa-octet index (floor n 256))))
 :hints (("Goal" :use ((:instance logtail-logtail (pos 8) (pos1 (* 8 index)) (i n)))
          :in-theory (disable loghead logtail fn-poa-octet fn-poa-bits logtail-logtail)))))

(local (defthm fn-poa-octet-is-nth
 (implies (and (natp index) (< index (len (fn-bch-unpack n))))
  (equal (fn-poa-octet index n) (nth index (fn-bch-unpack n))))
 :hints (("Goal" :induct (fn-bch-digits n index)
          :in-theory (e/d (fn-bch-unpack nth)
                    (fn-poa-octet fn-poa-octet-is-slice fn-poa-bits integer-length))
          :expand ((fn-poa-octet 0 n)))
         ("Subgoal *1/2" :use ((:instance fn-poa-octet-next (index (- index 1))))))))

(local (defthm fn-poa-nth-of-nfix
 (equal (nth (nfix index) xs) (nth index xs))
 :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-poa-octet-is-indexed-octet
 (implies (< (nfix index) (len (fn-bch-unpack n)))
  (equal (fn-poa-octet index n) (nth index (fn-bch-unpack n))))
 :hints (("Goal" :use ((:instance fn-poa-octet-is-nth (index (nfix index))))
          :in-theory (e/d (fn-poa-octet)
                    (fn-poa-octet-is-nth fn-poa-octet-is-slice fn-poa-bits)))))

(defthm fn-poa-octet-bound
 (and (natp (fn-poa-octet index n)) (< (fn-poa-octet index n) 256))
 :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :in-theory
          (disable fn-poa-octet fn-poa-bits fn-poa-octet-is-nth
                   fn-poa-octet-is-indexed-octet loghead logtail))))

(in-theory (disable fn-poa-bits fn-poa-length fn-poa-octet))
