; Equations retained by the bounded Ribbon insertion and read by the probe.
(in-package "ACL2")
(include-book "ribbon")
(include-book "owed-discharge")

; Evaluate a row against arbitrary candidate solution bytes.  An absent suffix
; contributes zero.  Packing the two coefficient words makes the carry across
; bit 31 in the insertion shift explicit.

(include-book "ihs/logops-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))

(defun fn2-ribbon-equation-value (mask z)
   (if (atom z) 0
     (logxor (if (logbitp 0 mask) (ifix (car z)) 0)
             (fn2-ribbon-equation-value (logcdr mask) (cdr z)))))

(local
 (defun fn2-ribbon-mask-pair-induct (a b z)
   (if (atom z) (list a b)
     (fn2-ribbon-mask-pair-induct (logcdr a) (logcdr b) (cdr z)))))

(local
 (defthm fn2-ribbon-cancel-xor
   (equal (logxor x (logxor x y)) (ifix y))
   :hints ((logbitp-reasoning))))

(local
 (defthm fn2-ribbon-equation-value-of-xor
   (equal (fn2-ribbon-equation-value (logxor a b) z)
          (logxor (fn2-ribbon-equation-value a z)
                  (fn2-ribbon-equation-value b z)))
   :hints (("Goal" :induct (fn2-ribbon-mask-pair-induct a b z)))))

(defun fn2-ribbon-row-mask (lo hi)
   (logapp 32 lo (loghead 32 hi)))

(local
 (defthm fn2-ribbon-row-mask-of-xor
   (equal (fn2-ribbon-row-mask (fn2-ribbon-xor32 lo a) (fn2-ribbon-xor32 hi b))
          (logxor (fn2-ribbon-row-mask lo hi) (fn2-ribbon-row-mask a b)))
   :hints (("Goal" :in-theory (enable fn2-ribbon-xor32))
           (logbitp-reasoning))))

(local
 (defthm fn2-ribbon-logbitp-of-logcdr
   (implies (natp i)
            (equal (logbitp i (logcdr x)) (logbitp (1+ i) x)))
   :hints (("Goal" :expand (logbitp (+ 1 i) x)))))

(local
 (defthm fn2-ribbon-low-bit
   (equal (equal 1 (loghead 1 x)) (logbitp 0 x))
   :hints (("Goal" :expand ((loghead 1 x) (logbitp 0 x))
            :in-theory (enable logcons)))))

(local
 (defthm fn2-ribbon-row-mask-of-shift
   (equal (fn2-ribbon-row-mask (fn2-ribbon-shr1 lo hi) (fn2-ribbon-shr hi 1))
          (logcdr (fn2-ribbon-row-mask lo hi)))
   :hints (("Goal" :in-theory (enable fn2-ribbon-shr1 fn2-ribbon-shr))
           (logbitp-reasoning))))

(defun fn2-ribbon-equation-at (s lo hi z)
   (fn2-ribbon-equation-value (fn2-ribbon-row-mask lo hi) (nthcdr s z)))

(local
 (defthm fn2-ribbon-equation-value-of-zero
   (equal (fn2-ribbon-equation-value 0 z) 0)))

(local
 (defthm fn2-ribbon-equation-at-of-xor
   (equal (fn2-ribbon-equation-at s (fn2-ribbon-xor32 lo a) (fn2-ribbon-xor32 hi b) z)
          (logxor (fn2-ribbon-equation-at s lo hi z) (fn2-ribbon-equation-at s a b z)))
   :hints (("Goal" :in-theory (disable fn2-ribbon-row-mask)))))

(local
 (defthm fn2-ribbon-nthcdr-successor
   (implies (natp s) (equal (nthcdr (+ 1 s) z) (cdr (nthcdr s z))))
   :hints (("Goal" :induct (nthcdr s z)))))

(local
 (defthm fn2-ribbon-row-mask-pivot
   (equal (logbitp 0 (fn2-ribbon-row-mask lo hi)) (logbitp 0 lo))
   :hints (("Goal" :in-theory (enable* logbitp-case-splits)))))

(local
 (defthm fn2-ribbon-equation-at-of-shift
   (implies (and (natp s) (not (logbitp 0 lo)))
            (equal (fn2-ribbon-equation-at (1+ s) (fn2-ribbon-shr1 lo hi)
                                           (fn2-ribbon-shr hi 1) z)
                   (fn2-ribbon-equation-at s lo hi z)))
   :hints (("Goal"
            :expand ((fn2-ribbon-equation-value (fn2-ribbon-row-mask lo hi) (nthcdr s z)))
            :in-theory (disable fn2-ribbon-row-mask nthcdr)))))

; The installed rows constrain the same solutions as the old rows together
; with the input equation.  On :more the residual equation still belongs
; to the caller and is part of that equivalence.

(defun fn2-ribbon-band-satisfied-p (slots base z fn2-ribbon-band)
   (declare (xargs :stobjs fn2-ribbon-band :measure (nfix slots) :verify-guards nil))
   (if (zp slots) t
     (let* ((s (1- slots)) (r (+ base s)))
       (and (equal (fn2-ribbon-equation-at s (fn2-ribbon-band-lo r fn2-ribbon-band)
                                           (fn2-ribbon-band-hi r fn2-ribbon-band) z) 0)
            (fn2-ribbon-band-satisfied-p s base z fn2-ribbon-band)))))

(local (in-theory (disable fn2-ribbon-equation-at fn2-ribbon-band-lo fn2-ribbon-band-hi
                           fn2-ribbon-band-rows)))

(local
 (defthm fn2-ribbon-satisfied-row
   (implies (and (fn2-ribbon-band-satisfied-p slots base z fn2-ribbon-band)
                 (natp slots) (natp s) (< s slots))
            (equal (fn2-ribbon-equation-at s (fn2-ribbon-band-lo (+ base s) fn2-ribbon-band)
                                          (fn2-ribbon-band-hi (+ base s) fn2-ribbon-band) z) 0))
   :hints (("Goal" :induct (fn2-ribbon-band-satisfied-p slots base z fn2-ribbon-band)))
   :rule-classes ((:rewrite :match-free :all))))

(local
 (defthm fn2-ribbon-zero-row-satisfied
   (equal (fn2-ribbon-equation-at s 0 0 z) 0)
   :hints (("Goal" :in-theory (enable fn2-ribbon-equation-at)))))

(local
 (defthm fn2-ribbon-satisfied-after-install
   (implies
    (and (natp s) (natp base) (natp slots)
         (equal (fn2-ribbon-band-lo (+ base s) fn2-ribbon-band) 0)
         (equal (fn2-ribbon-band-hi (+ base s) fn2-ribbon-band) 0))
    (equal (fn2-ribbon-band-satisfied-p
            slots base z (fn2-ribbon-band-put (+ base s) (lo lo) (hi hi)))
           (and (fn2-ribbon-band-satisfied-p slots base z fn2-ribbon-band)
                (or (<= slots s) (equal (fn2-ribbon-equation-at s lo hi z) 0)))))
   :hints (("Goal" :induct (fn2-ribbon-band-satisfied-p slots base z fn2-ribbon-band)
            :in-theory (enable fn2-ribbon-band-lo fn2-ribbon-band-hi)))))

(local
 (defthm fn2-ribbon-insert-solution-set
   (implies
    (and (natp s) (natp base) (natp slots))
    (mv-let (code next next-lo next-hi band)
      (fn2-ribbon-insert fuel s lo hi base slots fn2-ribbon-band)
      (implies (member-eq code '(:ok :redundant :more))
               (iff (and (fn2-ribbon-band-satisfied-p slots base z band)
                         (or (not (eq code :more))
                             (equal (fn2-ribbon-equation-at next next-lo next-hi z) 0)))
                    (and (fn2-ribbon-band-satisfied-p slots base z fn2-ribbon-band)
                         (equal (fn2-ribbon-equation-at s lo hi z) 0))))))
   :hints (("Goal" :induct (fn2-ribbon-insert fuel s lo hi base slots fn2-ribbon-band)
            :in-theory (e/d (fn2-ribbon-insert) (fn2-ribbon-band-satisfied-p fn2-ribbon-band-set-lo
                                fn2-ribbon-band-set-hi))))
   :rule-classes nil))

; Insertion and back substitution address the band by row.  The query
; addresses the serialized solution by page offset.

(local
 (defun fn2-ribbon-solution-bytes-agree-p
   (k j r end s pslot pgen pk ps pg fn2-ribbon-band fn2-pool)
   (declare (xargs :stobjs (fn2-ribbon-band fn2-pool) :measure (nfix k)
                   :verify-guards nil))
   (if (zp k) t
     (let ((x (+ r j)))
       (and (< x end)
            (< x (fn2-ribbon-band-rows fn2-ribbon-band))
            (unsigned-byte-p 8 (fn2-ribbon-band-z x fn2-ribbon-band))
            (mv-let (code byte)
              (fn2-pool-read pslot pgen (+ *fn2-ribbon-base* s j) pk ps pg fn2-pool)
              (and (eq code :ok) (equal byte (fn2-ribbon-band-z x fn2-ribbon-band))))
            (fn2-ribbon-solution-bytes-agree-p
             (1- k) (1+ j) r end s pslot pgen pk ps pg
             fn2-ribbon-band fn2-pool))))))

(local
 (defthm fn2-ribbon-probe-dot-agrees-with-band
   (implies
    (fn2-ribbon-solution-bytes-agree-p
     k j r end s pslot pgen pk ps pg fn2-ribbon-band fn2-pool)
    (equal (fn2-ribbon-probe-dot k j s lo hi acc pslot pgen pk ps pg fn2-pool)
           (fn2-ribbon-dot k j r end lo hi acc fn2-ribbon-band)))
   :hints (("Goal"
            :induct (fn2-ribbon-dot k j r end lo hi acc fn2-ribbon-band)
            :in-theory
            (union-theories
             '(fn2-ribbon-dot fn2-ribbon-probe-dot fn2-ribbon-solution-bytes-agree-p
               car-cons cdr-cons)
             (theory 'minimal-theory))))))

; Back substitution walks down the band.  Writing a pivot byte cancels its
; tail dot product, and subsequent writes below it preserve that equation.

(local
 (defthm fn2-ribbon-xor8-of-delta
   (implies (unsigned-byte-p 8 delta)
            (equal (fn2-ribbon-xor8 (logxor delta acc) byte)
                   (logxor delta (fn2-ribbon-xor8 acc byte))))
   :hints (("Goal" :in-theory (enable fn2-ribbon-xor8)))))

(local
 (defthm fn2-ribbon-dot-of-delta
   (implies (unsigned-byte-p 8 delta)
            (equal (fn2-ribbon-dot k j r end lo hi (logxor delta acc) fn2-ribbon-band)
                   (mv-let (code result) (fn2-ribbon-dot k j r end lo hi acc fn2-ribbon-band)
                     (mv code (logxor delta result)))))
   :hints (("Goal" :induct (fn2-ribbon-dot k j r end lo hi acc fn2-ribbon-band)
            :in-theory (e/d (fn2-ribbon-dot)
                            (commutativity-of-logxor fn2-ribbon-band-z))))))

(local
 (defthm fn2-ribbon-solution-update-reads
   (implies (and (natp x) (natp y))
            (and (equal (fn2-ribbon-band-z y (fn2-ribbon-band-set-z x v fn2-ribbon-band))
                        (if (equal x y) v (fn2-ribbon-band-z y fn2-ribbon-band)))
                 (equal (fn2-ribbon-band-lo y (fn2-ribbon-band-set-z x v fn2-ribbon-band))
                        (fn2-ribbon-band-lo y fn2-ribbon-band))
                 (equal (fn2-ribbon-band-hi y (fn2-ribbon-band-set-z x v fn2-ribbon-band))
                        (fn2-ribbon-band-hi y fn2-ribbon-band))))
   :hints (("Goal" :in-theory (enable fn2-ribbon-band-set-z fn2-ribbon-band-lo fn2-ribbon-band-hi
                                      update-fn2-ribbon-band-z$ai)))))

(local
 (defthm fn2-ribbon-solution-update-rows
   (equal (fn2-ribbon-band-rows (fn2-ribbon-band-set-z x v fn2-ribbon-band))
          (fn2-ribbon-band-rows fn2-ribbon-band))
   :hints (("Goal" :in-theory (enable fn2-ribbon-band-rows fn2-ribbon-band-set-z
                                      update-fn2-ribbon-band-z$ai)))))

(local
 (defthm fn2-ribbon-dot-above-updated-byte
   (implies (and (natp x) (natp r) (natp j) (< x (+ r j)))
            (equal (fn2-ribbon-dot k j r end lo hi acc
                                   (fn2-ribbon-band-set-z x v fn2-ribbon-band))
                   (fn2-ribbon-dot k j r end lo hi acc fn2-ribbon-band)))
   :hints (("Goal" :induct (fn2-ribbon-dot k j r end lo hi acc fn2-ribbon-band)
            :expand ((:free (band) (fn2-ribbon-dot k j r end lo hi acc band)))
            :in-theory (e/d (fn2-ribbon-dot)
                            (fn2-ribbon-band-set-z fn2-ribbon-band-z))))))

(local
 (defthm fn2-ribbon-dot-byte
   (implies (unsigned-byte-p 8 acc)
            (unsigned-byte-p 8 (mv-nth 1 (fn2-ribbon-dot k j r end lo hi acc fn2-ribbon-band))))
   :hints (("Goal" :induct (fn2-ribbon-dot k j r end lo hi acc fn2-ribbon-band)
            :in-theory (e/d (fn2-ribbon-dot) (unsigned-byte-p fn2-ribbon-band-z))))))

(local
 (defthm fn2-ribbon-dot-zero-result-integer
   (integerp (mv-nth 1 (fn2-ribbon-dot k j r end lo hi 0 fn2-ribbon-band)))
   :hints (("Goal" :use ((:instance fn2-ribbon-dot-byte (acc 0)))
            :in-theory (disable fn2-ribbon-dot-byte)))
   :rule-classes :type-prescription))

(local
 (defthm fn2-ribbon-dot-cancels-own-result
   (let* ((tail (fn2-ribbon-dot k j r end lo hi 0 fn2-ribbon-band))
          (v (mv-nth 1 tail)))
     (equal (fn2-ribbon-dot k j r end lo hi v fn2-ribbon-band)
            (list (mv-nth 0 tail) 0)))
   :hints (("Goal"
            :use ((:instance fn2-ribbon-dot-of-delta (acc 0)
                   (delta (mv-nth 1 (fn2-ribbon-dot k j r end lo hi 0 fn2-ribbon-band)))))
            :in-theory (disable fn2-ribbon-dot-of-delta)))))

(local
 (defthm fn2-ribbon-xor8-zero-byte
   (implies (unsigned-byte-p 8 v) (equal (fn2-ribbon-xor8 0 v) v))
   :hints (("Goal" :in-theory (enable fn2-ribbon-xor8)))))

(local
 (defthm fn2-ribbon-back-substitute-pivot
   (let* ((tail (fn2-ribbon-dot 63 1 r end lo hi 0 fn2-ribbon-band))
          (v (mv-nth 1 tail)))
     (implies (and (natp r) (< r end) (< r (fn2-ribbon-band-rows fn2-ribbon-band))
                   (logbitp 0 lo) (equal (mv-nth 0 tail) :ok))
              (equal (fn2-ribbon-dot 64 0 r end lo hi 0 (fn2-ribbon-band-set-z r v fn2-ribbon-band))
                     '(:ok 0))))
   :hints (("Goal" :expand ((:free (band) (fn2-ribbon-dot 64 0 r end lo hi 0 band)))
            :in-theory (disable fn2-ribbon-band-set-z fn2-ribbon-band-z)))))

(local
 (defthm fn2-ribbon-dot-of-zero-row
   (equal (fn2-ribbon-dot k j r end 0 0 acc fn2-ribbon-band) (list :ok acc))
   :hints (("Goal" :induct (fn2-ribbon-dot k j r end 0 0 acc fn2-ribbon-band)
            :in-theory (enable fn2-ribbon-dot)))))

(local
 (defthm fn2-ribbon-dot-above-solve
   (implies (and (natp base) (natp i) (natp r) (<= (+ base i) r))
            (equal (fn2-ribbon-dot 64 0 r end lo hi 0
                    (mv-nth 1 (fn2-ribbon-solve-rows n i base end seed fn2-ribbon-band)))
                   (fn2-ribbon-dot 64 0 r end lo hi 0 fn2-ribbon-band)))
   :hints (("Goal" :induct (fn2-ribbon-solve-rows n i base end seed fn2-ribbon-band)
            :in-theory (e/d (fn2-ribbon-solve-rows)
                            (fn2-ribbon-band-set-z fn2-ribbon-dot))))))

(local
 (defthm fn2-ribbon-solved-row-dot
   (let* ((r (+ base s))
          (lo (fn2-ribbon-band-lo r fn2-ribbon-band))
          (hi (fn2-ribbon-band-hi r fn2-ribbon-band))
          (run (fn2-ribbon-solve-rows n i base end seed fn2-ribbon-band)))
     (implies (and (natp base) (natp s) (natp i) (natp n)
                   (<= (- i n) s) (< s i) (< r end)
                   (or (and (equal lo 0) (equal hi 0)) (logbitp 0 lo))
                   (equal (mv-nth 0 run) :ok))
              (equal (fn2-ribbon-dot 64 0 r end lo hi 0 (mv-nth 1 run))
                     '(:ok 0))))
   :hints (("Goal" :induct (fn2-ribbon-solve-rows n i base end seed fn2-ribbon-band)
            :in-theory (e/d (fn2-ribbon-solve-rows)
                            (fn2-ribbon-band-set-z fn2-ribbon-dot))))
   :rule-classes nil))

; The solved bytes satisfy the same equations quantified over during insertion.
(defun fn2-ribbon-band-suffix (x end fn2-ribbon-band)
   (declare (xargs :stobjs fn2-ribbon-band :verify-guards nil :measure (nfix (- end x))))
   (if (zp (- end x)) nil
     (cons (loghead 8 (fn2-ribbon-band-z x fn2-ribbon-band))
           (fn2-ribbon-band-suffix (+ 1 x) end fn2-ribbon-band))))

(local
 (defthm fn2-ribbon-cdr-of-mask-slice
   (implies (and (posp k) (natp j))
            (equal (logcdr (loghead k (logtail j m)))
                   (loghead (1- k) (logtail (1+ j) m))))
   :hints ((logbitp-reasoning))))

(local
 (defthm fn2-ribbon-mask-slice-first-bit
   (implies (and (posp k) (natp j) (< j 64))
            (equal (logbitp 0 (loghead k (logtail j (fn2-ribbon-row-mask lo hi))))
                   (if (< j 32) (logbitp j lo) (logbitp (- j 32) hi))))
   :hints (("Goal" :in-theory (enable* logbitp-case-splits)))))

(local
 (defthm fn2-ribbon-xor8-of-byte
   (implies (unsigned-byte-p 8 acc)
            (equal (fn2-ribbon-xor8 acc v) (logxor acc (loghead 8 v))))
   :hints (("Goal" :in-theory (enable fn2-ribbon-xor8)))))

(local
 (defthm fn2-ribbon-empty-band-suffix
   (implies (<= end x) (equal (fn2-ribbon-band-suffix x end fn2-ribbon-band) nil))
   :hints (("Goal" :expand (fn2-ribbon-band-suffix x end fn2-ribbon-band)))))

(local
 (defthm fn2-ribbon-dot-evaluates-mask
   (let ((dot (fn2-ribbon-dot k j r end lo hi acc fn2-ribbon-band)))
     (implies (and (natp k) (natp j) (<= (+ j k) 64) (natp r) (natp end)
                   (unsigned-byte-p 8 acc) (equal (mv-nth 0 dot) :ok))
              (equal (mv-nth 1 dot)
                     (logxor acc
                             (fn2-ribbon-equation-value
                              (loghead k (logtail j (fn2-ribbon-row-mask lo hi)))
                              (fn2-ribbon-band-suffix (+ r j) end fn2-ribbon-band))))))
   :hints (("Goal" :induct (fn2-ribbon-dot k j r end lo hi acc fn2-ribbon-band)
            :expand ((fn2-ribbon-equation-value (loghead k (logtail j (fn2-ribbon-row-mask lo hi)))
                                                (fn2-ribbon-band-suffix (+ r j) end fn2-ribbon-band))
                     (fn2-ribbon-band-suffix (+ r j) end fn2-ribbon-band))
            :in-theory (e/d (fn2-ribbon-dot) (fn2-ribbon-row-mask fn2-ribbon-band-z))))
   :rule-classes nil))

(local
 (defun fn2-ribbon-suffix-induct (s base)
   (if (zp s) base (fn2-ribbon-suffix-induct (1- s) (1+ base)))))

(local
 (defthm fn2-ribbon-nthcdr-of-band-suffix
   (implies (and (natp s) (natp base) (natp end))
            (equal (nthcdr s (fn2-ribbon-band-suffix base end fn2-ribbon-band))
                   (fn2-ribbon-band-suffix (+ s base) end fn2-ribbon-band)))
   :hints (("Goal" :induct (fn2-ribbon-suffix-induct s base)
            :expand ((fn2-ribbon-band-suffix base end fn2-ribbon-band))
            :in-theory (disable fn2-ribbon-nthcdr-successor)))))

(local
 (defthm fn2-ribbon-row-mask-width
   (unsigned-byte-p 64 (fn2-ribbon-row-mask lo hi))))

(local
 (defthm fn2-ribbon-dot-evaluates-equation-at
   (implies (and (natp s) (natp base) (natp end)
                 (equal (mv-nth 0 (fn2-ribbon-dot 64 0 (+ s base) end lo hi 0 fn2-ribbon-band)) :ok))
            (equal (mv-nth 1 (fn2-ribbon-dot 64 0 (+ s base) end lo hi 0 fn2-ribbon-band))
                   (fn2-ribbon-equation-at s lo hi
                                          (fn2-ribbon-band-suffix base end fn2-ribbon-band))))
   :hints (("Goal" :use ((:instance fn2-ribbon-dot-evaluates-mask (r (+ s base))
                                    (k 64) (j 0) (acc 0)))
            :in-theory (e/d (fn2-ribbon-equation-at)
                            (fn2-ribbon-row-mask fn2-ribbon-equation-value))))
   :rule-classes nil))

(defun fn2-ribbon-pivots-p (slots base fn2-ribbon-band)
   (declare (xargs :stobjs fn2-ribbon-band :measure (nfix slots) :verify-guards nil))
   (if (zp slots) t
     (let* ((s (1- slots)) (r (+ base s))
            (lo (fn2-ribbon-band-lo r fn2-ribbon-band))
            (hi (fn2-ribbon-band-hi r fn2-ribbon-band)))
       (and (or (and (equal lo 0) (equal hi 0)) (logbitp 0 lo))
            (fn2-ribbon-pivots-p s base fn2-ribbon-band)))))

(local
 (defthm fn2-ribbon-solved-row-equation
   (let* ((r (+ base s))
          (lo (fn2-ribbon-band-lo r fn2-ribbon-band))
          (hi (fn2-ribbon-band-hi r fn2-ribbon-band))
          (run (fn2-ribbon-solve-rows slots slots base end seed fn2-ribbon-band)))
     (implies (and (natp base) (natp s) (natp slots) (natp end) (< s slots) (< r end)
                   (or (and (equal lo 0) (equal hi 0)) (logbitp 0 lo))
                   (equal (mv-nth 0 run) :ok))
              (equal (fn2-ribbon-equation-at s lo hi (fn2-ribbon-band-suffix base end (mv-nth 1 run)))
                     0)))
   :hints (("Goal"
            :use ((:instance fn2-ribbon-solved-row-dot (n slots) (i slots))
                  (:instance fn2-ribbon-dot-evaluates-equation-at
                   (lo (fn2-ribbon-band-lo (+ base s) fn2-ribbon-band))
                   (hi (fn2-ribbon-band-hi (+ base s) fn2-ribbon-band))
                   (fn2-ribbon-band
                    (mv-nth 1 (fn2-ribbon-solve-rows slots slots base end seed fn2-ribbon-band)))))
            :in-theory (disable fn2-ribbon-band-suffix)))))

(local
 (defthm fn2-ribbon-solved-system
   (let ((run (fn2-ribbon-solve-rows slots slots base end seed fn2-ribbon-band)))
     (implies (and (natp base) (natp slots) (natp end) (<= (+ base slots) end)
                   (natp n) (<= n slots) (fn2-ribbon-pivots-p n base fn2-ribbon-band)
                   (equal (mv-nth 0 run) :ok))
              (fn2-ribbon-band-satisfied-p
               n base (fn2-ribbon-band-suffix base end (mv-nth 1 run)) fn2-ribbon-band)))
   :hints (("Goal" :induct (fn2-ribbon-pivots-p n base fn2-ribbon-band)
            :in-theory (disable fn2-ribbon-band-suffix))
           ("Subgoal *1/2" :use ((:instance fn2-ribbon-solved-row-equation (s (1- n))))))))

(local
 (defthm fn2-ribbon-pivots-after-install
   (implies (and (natp s) (natp base) (natp n) (logbitp 0 lo)
                 (fn2-ribbon-pivots-p n base fn2-ribbon-band))
            (fn2-ribbon-pivots-p n base (fn2-ribbon-band-put (+ base s) (lo lo) (hi hi))))
   :hints (("Goal" :induct (fn2-ribbon-pivots-p n base fn2-ribbon-band)
            :in-theory (enable fn2-ribbon-band-lo fn2-ribbon-band-hi)))))

(local
 (defthm fn2-ribbon-pivots-after-insert
   (implies (and (natp base) (natp s) (natp slots) (fn2-ribbon-pivots-p slots base fn2-ribbon-band))
            (fn2-ribbon-pivots-p slots base
             (mv-nth 4 (fn2-ribbon-insert fuel s lo hi base slots fn2-ribbon-band))))
   :hints (("Goal" :induct (fn2-ribbon-insert fuel s lo hi base slots fn2-ribbon-band)
            :in-theory (e/d (fn2-ribbon-insert)
                            (fn2-ribbon-pivots-p fn2-ribbon-band-set-lo fn2-ribbon-band-set-hi))))))

(local
 (defthm fn2-ribbon-agree-implies-dot-readable
   (implies (fn2-ribbon-solution-bytes-agree-p
             k j r end s pslot pgen pk ps pg fn2-ribbon-band fn2-pool)
            (equal (mv-nth 0 (fn2-ribbon-dot k j r end lo hi acc fn2-ribbon-band)) :ok))
   :hints (("Goal" :induct (fn2-ribbon-dot k j r end lo hi acc fn2-ribbon-band)
            :in-theory
            (union-theories '(fn2-ribbon-dot fn2-ribbon-solution-bytes-agree-p
                              mv-nth (:e zp) car-cons cdr-cons)
                            (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-dot-result-pair
   (let ((v (fn2-ribbon-dot k j r end lo hi acc fn2-ribbon-band)))
     (equal (list (mv-nth 0 v) (mv-nth 1 v)) v))
   :hints (("Goal" :induct (fn2-ribbon-dot k j r end lo hi acc fn2-ribbon-band)
            :in-theory (enable fn2-ribbon-dot)))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-probe-dot-of-satisfied-equation
   (implies (and (natp s) (natp base) (natp end)
                 (fn2-ribbon-solution-bytes-agree-p 64 0 (+ base s) end s pslot pgen pk ps pg
                                                     fn2-ribbon-band fn2-pool)
                 (equal (fn2-ribbon-equation-at s lo hi
                           (fn2-ribbon-band-suffix base end fn2-ribbon-band)) 0))
            (equal (fn2-ribbon-probe-dot 64 0 s lo hi 0 pslot pgen pk ps pg fn2-pool)
                   '(:ok 0)))
   :hints (("Goal"
            :use ((:instance fn2-ribbon-dot-result-pair (k 64) (j 0) (r (+ base s)) (acc 0))
                  (:instance fn2-ribbon-probe-dot-agrees-with-band (k 64) (j 0) (r (+ base s)) (acc 0))
                  fn2-ribbon-dot-evaluates-equation-at)
            :in-theory (disable fn2-ribbon-solution-bytes-agree-p fn2-ribbon-band-suffix
                                fn2-ribbon-probe-dot-agrees-with-band)))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-insert-solve-probe-dot
   (let* ((ins (fn2-ribbon-insert fuel s lo hi base slots fn2-ribbon-band))
          (installed (mv-nth 4 ins))
          (solve (fn2-ribbon-solve-rows slots slots base end seed installed))
          (solved (mv-nth 1 solve)))
     (implies (and (natp base) (natp slots) (natp s) (natp end)
                   (<= (+ base slots) end)
                   (fn2-ribbon-pivots-p slots base fn2-ribbon-band)
                   (member-eq (mv-nth 0 ins) '(:ok :redundant))
                   (equal (mv-nth 0 solve) :ok)
                   (fn2-ribbon-solution-bytes-agree-p 64 0 (+ base s) end s pslot pgen pk ps pg
                                                       solved fn2-pool))
              (equal (fn2-ribbon-probe-dot 64 0 s lo hi 0 pslot pgen pk ps pg fn2-pool)
                     '(:ok 0))))
   :hints (("Goal"
            :use ((:instance fn2-ribbon-insert-solution-set
                   (z (fn2-ribbon-band-suffix base end
                       (mv-nth 1 (fn2-ribbon-solve-rows slots slots base end seed
                                  (mv-nth 4 (fn2-ribbon-insert fuel s lo hi base slots fn2-ribbon-band)))))))
                  (:instance fn2-ribbon-solved-system (n slots)
                   (fn2-ribbon-band (mv-nth 4 (fn2-ribbon-insert fuel s lo hi base slots fn2-ribbon-band))))
                  (:instance fn2-ribbon-probe-dot-of-satisfied-equation
                   (fn2-ribbon-band
                    (mv-nth 1 (fn2-ribbon-solve-rows slots slots base end seed
                               (mv-nth 4 (fn2-ribbon-insert fuel s lo hi base slots fn2-ribbon-band)))))))
            :in-theory (disable fn2-ribbon-solved-system fn2-ribbon-pivots-p
                                fn2-ribbon-band-suffix fn2-ribbon-solution-bytes-agree-p
                                fn2-ribbon-band-satisfied-p)))
   :rule-classes nil))

; Successful emission establishes the byte agreement required by the probe.
(defthm fn2-ribbon-read-after-write
   (let* ((wr (fn2-pool-write slot gen i v pk ps pg fn2-pool))
          (prior (fn2-pool-read slot gen j pk ps pg fn2-pool)))
     (implies (and (natp (fn2-pool-base slot fn2-pool)) (natp j)
                   (equal (mv-nth 0 wr) :ok)
                   (or (equal i j) (equal (mv-nth 0 prior) :ok)))
              (equal (fn2-pool-read slot gen j pk ps pg (mv-nth 1 wr))
                     (if (equal i j) (list :ok v) prior))))
   :hints (("Goal" :in-theory
            (enable fn2-pool-write fn2-pool-read fn2-pool-workspace-code
                    fn2-pool-readable-code fn2-pool-handle-code fn2-pool-ownerp
                    fn2-pool-set-fill update-fn2-pool-fill$ai update-fn2-pool-datai))))

(local
 (defthm fn2-ribbon-pool-base-after-write
   (equal (fn2-pool-base slot (mv-nth 1 (fn2-pool-write slot gen i v pk ps pg fn2-pool)))
          (fn2-pool-base slot fn2-pool))
   :hints (("Goal" :in-theory (e/d (fn2-pool-write fn2-pool-set-fill update-fn2-pool-fill$ai
                                              update-fn2-pool-datai fn2-pool-base)
                                   (fn2-pool-workspace-code))))))

(defthm fn2-ribbon-emit-reads
   (let ((wr (fn2-ribbon-emit-bytes n i base slot gen off pk ps pg fn2-ribbon-band fn2-pool))
         (prior (fn2-pool-read slot gen (+ off p) pk ps pg fn2-pool)))
     (implies (and (natp n) (natp i) (natp base) (natp off) (natp p)
                   (natp (fn2-pool-base slot fn2-pool))
                   (< p (+ i n)) (or (<= i p) (equal (mv-nth 0 prior) :ok))
                   (equal (mv-nth 0 wr) :ok))
              (equal (fn2-pool-read slot gen (+ off p) pk ps pg (mv-nth 1 wr))
                     (if (< p i) prior (list :ok (fn2-ribbon-band-z (+ base p) fn2-ribbon-band))))))
   :hints (("Goal" :induct (fn2-ribbon-emit-bytes n i base slot gen off pk ps pg fn2-ribbon-band fn2-pool)
            :in-theory (e/d (fn2-ribbon-emit-bytes)
                            (fn2-pool-read fn2-pool-write fn2-pool-base fn2-ribbon-band-z)))))

(local
 (defthm fn2-ribbon-successful-write-byte
   (implies (equal (mv-nth 0 (fn2-pool-write slot gen i v pk ps pg fn2-pool)) :ok)
            (unsigned-byte-p 8 v))
   :hints (("Goal" :in-theory (e/d (fn2-pool-write) (fn2-pool-workspace-code unsigned-byte-p))))
   :rule-classes nil))

(defthm fn2-ribbon-emit-validates-row
   (implies (and (natp i) (natp n) (natp p) (<= i p) (< p (+ i n))
                 (equal (mv-nth 0 (fn2-ribbon-emit-bytes n i base slot gen off pk ps pg
                                                          fn2-ribbon-band fn2-pool)) :ok))
            (and (< (+ base p) (fn2-ribbon-band-rows fn2-ribbon-band))
                 (unsigned-byte-p 8 (fn2-ribbon-band-z (+ base p) fn2-ribbon-band))))
   :hints (("Goal" :induct (fn2-ribbon-emit-bytes n i base slot gen off pk ps pg fn2-ribbon-band fn2-pool)
            :in-theory (e/d (fn2-ribbon-emit-bytes)
                            (fn2-ribbon-band-z fn2-pool-write unsigned-byte-p)))
           ("Subgoal *1/2" :use ((:instance fn2-ribbon-successful-write-byte
                                  (i (+ off i)) (v (fn2-ribbon-band-z (+ base i) fn2-ribbon-band))))))
   :rule-classes nil)

(local
 (defun fn2-ribbon-span-induct (k j)
   (declare (xargs :measure (nfix k)))
   (if (zp k) j (fn2-ribbon-span-induct (1- k) (1+ j)))))

(local
 (defthm fn2-ribbon-emit-produces-solution-bytes
   (let ((wr (fn2-ribbon-emit-bytes slots 0 base slot gen *fn2-ribbon-base* pk ps pg
                                    fn2-ribbon-band fn2-pool)))
     (implies (and (natp k) (natp j) (natp s) (natp base) (natp slots)
                   (<= (+ s j k) slots) (natp (fn2-pool-base slot fn2-pool))
                   (equal (mv-nth 0 wr) :ok))
              (fn2-ribbon-solution-bytes-agree-p
               k j (+ base s) (+ base slots) s slot gen pk ps pg fn2-ribbon-band (mv-nth 1 wr))))
   :hints (("Goal" :induct (fn2-ribbon-span-induct k j)
            :in-theory (disable fn2-ribbon-band-z fn2-pool-read fn2-pool-base fn2-ribbon-emit-bytes))
           ("Subgoal *1/2" :use ((:instance fn2-ribbon-emit-validates-row
                                 (i 0) (n slots) (off *fn2-ribbon-base*) (p (+ s j)))
                                (:instance fn2-ribbon-emit-reads
                                 (i 0) (n slots) (off *fn2-ribbon-base*) (p (+ s j))))))))

(local
 (defthm fn2-ribbon-placement-fits
   (implies (and (natp slots) (<= 64 slots))
            (<= (+ 64 (car (fn2-ribbon-place h1 h2 slots))) slots))
   :hints (("Goal" :use ((:instance fn2-prng-mix3232-width-bound (h h1)))
            :in-theory (enable fn2-ribbon-place)
            :nonlinearp t))
   :rule-classes :linear))

(local
 (defthm fn2-ribbon-insert-solve-emit-probe
   (let* ((ins (fn2-ribbon-insert fuel s lo hi base slots fn2-ribbon-band))
          (installed (mv-nth 4 ins))
          (end (+ base slots))
          (solve (fn2-ribbon-solve-rows slots slots base end seed installed))
          (solved (mv-nth 1 solve))
          (emit (fn2-ribbon-emit-bytes slots 0 base slot gen *fn2-ribbon-base* pk ps pg solved fn2-pool)))
     (implies (and (natp base) (natp slots) (natp s) (<= (+ 64 s) slots)
                   (natp (fn2-pool-base slot fn2-pool))
                   (fn2-ribbon-pivots-p slots base fn2-ribbon-band)
                   (member-eq (mv-nth 0 ins) '(:ok :redundant))
                   (equal (mv-nth 0 solve) :ok) (equal (mv-nth 0 emit) :ok))
              (equal (fn2-ribbon-probe-dot 64 0 s lo hi 0 slot gen pk ps pg (mv-nth 1 emit))
                     '(:ok 0))))
   :hints (("Goal"
            :use ((:instance fn2-ribbon-insert-solve-probe-dot
                   (end (+ base slots)) (pslot slot) (pgen gen)
                   (fn2-pool
                    (mv-nth 1 (fn2-ribbon-emit-bytes slots 0 base slot gen *fn2-ribbon-base* pk ps pg
                               (mv-nth 1 (fn2-ribbon-solve-rows slots slots base (+ base slots) seed
                                          (mv-nth 4 (fn2-ribbon-insert fuel s lo hi base slots fn2-ribbon-band))))
                               fn2-pool)))))
            :in-theory (disable fn2-ribbon-pivots-p fn2-ribbon-solution-bytes-agree-p fn2-pool-base
                                fn2-ribbon-emit-bytes fn2-ribbon-probe-dot-agrees-with-band)))
   :rule-classes nil))

; A shift consumes a slot. Elimination at an occupied pivot clears the low bit.
(defun fn2-ribbon-row-fits-p (s lo hi slots)
   (unsigned-byte-p (nfix (- slots s)) (fn2-ribbon-row-mask lo hi)))

(defun fn2-ribbon-band-fits-p (n base slots fn2-ribbon-band)
   (declare (xargs :stobjs fn2-ribbon-band :measure (nfix n) :verify-guards nil))
   (if (zp n) t
     (let ((r (+ base (1- n))))
       (and (fn2-ribbon-row-fits-p (1- n) (fn2-ribbon-band-lo r fn2-ribbon-band)
                                   (fn2-ribbon-band-hi r fn2-ribbon-band) slots)
            (fn2-ribbon-band-fits-p (1- n) base slots fn2-ribbon-band)))))

(local
 (defthm fn2-ribbon-xor-fits
   (implies (and (fn2-ribbon-row-fits-p s lo hi slots) (fn2-ribbon-row-fits-p s a b slots))
            (fn2-ribbon-row-fits-p s (fn2-ribbon-xor32 lo a) (fn2-ribbon-xor32 hi b) slots))
   :hints (("Goal" :in-theory (disable fn2-ribbon-row-mask unsigned-byte-p)))))

(local
 (defthm fn2-ribbon-shift-fits
   (implies (and (natp slots) (natp s) (< s slots) (fn2-ribbon-row-fits-p s lo hi slots))
            (fn2-ribbon-row-fits-p (1+ s) (fn2-ribbon-shr1 lo hi) (fn2-ribbon-shr hi 1) slots))
   :hints (("Goal" :use ((:instance unsigned-byte-p** (bits (- slots s)) (x (fn2-ribbon-row-mask lo hi))))
            :in-theory (disable fn2-ribbon-row-mask unsigned-byte-p)))))

(local
 (defthm fn2-ribbon-band-row-fits
   (implies (and (fn2-ribbon-band-fits-p n base slots fn2-ribbon-band)
                 (natp n) (natp s) (< s n))
            (fn2-ribbon-row-fits-p s (fn2-ribbon-band-lo (+ base s) fn2-ribbon-band)
                                   (fn2-ribbon-band-hi (+ base s) fn2-ribbon-band) slots))
   :hints (("Goal" :induct (fn2-ribbon-band-fits-p n base slots fn2-ribbon-band)
            :in-theory (disable fn2-ribbon-row-fits-p)))))

(local
 (defthm fn2-ribbon-unpack-row-mask
   (implies (and (unsigned-byte-p 32 lo) (unsigned-byte-p 32 hi))
            (and (equal (loghead 32 (fn2-ribbon-row-mask lo hi)) lo)
                 (equal (logtail 32 (fn2-ribbon-row-mask lo hi)) hi)))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-row-mask-zero
   (implies (and (unsigned-byte-p 32 lo) (unsigned-byte-p 32 hi))
            (equal (equal (fn2-ribbon-row-mask lo hi) 0)
                   (and (equal lo 0) (equal hi 0))))
   :hints (("Goal" :use fn2-ribbon-unpack-row-mask :cases ((equal (fn2-ribbon-row-mask lo hi) 0))))))

(local
 (defthm fn2-ribbon-row-fits-at-end
   (implies (and (natp slots) (unsigned-byte-p 32 lo) (unsigned-byte-p 32 hi))
            (equal (fn2-ribbon-row-fits-p slots lo hi slots) (and (equal lo 0) (equal hi 0))))
   :hints (("Goal" :in-theory (disable fn2-ribbon-row-mask)))))

(local
 (defthm fn2-ribbon-elimination-clears-pivot
   (implies (and (logbitp 0 a) (logbitp 0 b))
            (not (logbitp 0 (fn2-ribbon-xor32 a b))))
   :hints (("Goal" :in-theory (enable fn2-ribbon-xor32)))))

(local
 (defthm fn2-ribbon-occupied-pivot-is-odd
   (implies (and (fn2-ribbon-pivots-p n base fn2-ribbon-band) (natp s) (natp n) (< s n)
                 (not (and (equal (fn2-ribbon-band-lo (+ base s) fn2-ribbon-band) 0)
                           (equal (fn2-ribbon-band-hi (+ base s) fn2-ribbon-band) 0))))
            (logbitp 0 (fn2-ribbon-band-lo (+ base s) fn2-ribbon-band)))
   :hints (("Goal" :induct (fn2-ribbon-pivots-p n base fn2-ribbon-band)))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-nonempty-row-start
   (implies (and (natp s) (natp slots) (<= s slots) (fn2-ribbon-row-fits-p s lo hi slots)
                 (unsigned-byte-p 32 lo) (unsigned-byte-p 32 hi)
                 (or (not (equal lo 0)) (not (equal hi 0))))
            (< s slots))
   :hints (("Goal" :cases ((equal s slots)) :in-theory (disable fn2-ribbon-row-fits-p unsigned-byte-p)))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-insert-terminates-in-band
   (implies (and (natp fuel) (natp s) (natp base) (natp slots) (<= s slots)
                 (<= (+ base slots) (fn2-ribbon-band-rows fn2-ribbon-band))
                 (unsigned-byte-p 32 lo) (unsigned-byte-p 32 hi)
                 (fn2-ribbon-row-fits-p s lo hi slots)
                 (fn2-ribbon-band-fits-p slots base slots fn2-ribbon-band)
                 (fn2-ribbon-pivots-p slots base fn2-ribbon-band)
                 (< (+ (* 2 (- slots s)) (if (logbitp 0 lo) 1 0)) fuel))
            (member-eq (mv-nth 0 (fn2-ribbon-insert fuel s lo hi base slots fn2-ribbon-band))
                       '(:ok :redundant)))
   :hints (("Goal" :induct (fn2-ribbon-insert fuel s lo hi base slots fn2-ribbon-band)
            :in-theory (e/d (fn2-ribbon-insert)
                            (unsigned-byte-p fn2-ribbon-row-fits-p fn2-ribbon-pivots-p
                             fn2-ribbon-band-fits-p)))
           ("Subgoal *1/3" :use fn2-ribbon-nonempty-row-start)
           ("Subgoal *1/4" :use fn2-ribbon-nonempty-row-start)
           ("Subgoal *1/6" :use ((:instance fn2-ribbon-occupied-pivot-is-odd (n slots)))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-fit-after-install
   (implies (and (natp s) (natp base) (natp n) (fn2-ribbon-row-fits-p s lo hi slots)
                 (fn2-ribbon-band-fits-p n base slots fn2-ribbon-band))
            (fn2-ribbon-band-fits-p n base slots (fn2-ribbon-band-put (+ base s) (lo lo) (hi hi))))
   :hints (("Goal" :induct (fn2-ribbon-band-fits-p n base slots fn2-ribbon-band)
            :in-theory (e/d (fn2-ribbon-band-lo fn2-ribbon-band-hi) (fn2-ribbon-row-fits-p))))))

(local
 (defthm fn2-ribbon-fit-after-insert
   (implies (and (natp base) (natp s) (natp slots) (<= s slots)
                 (unsigned-byte-p 32 lo) (unsigned-byte-p 32 hi)
                 (fn2-ribbon-row-fits-p s lo hi slots)
                 (fn2-ribbon-band-fits-p slots base slots fn2-ribbon-band))
            (fn2-ribbon-band-fits-p slots base slots
             (mv-nth 4 (fn2-ribbon-insert fuel s lo hi base slots fn2-ribbon-band))))
   :hints (("Goal" :induct (fn2-ribbon-insert fuel s lo hi base slots fn2-ribbon-band)
            :in-theory (e/d (fn2-ribbon-insert)
                            (fn2-ribbon-band-fits-p fn2-ribbon-row-fits-p
                             fn2-ribbon-band-set-lo fn2-ribbon-band-set-hi unsigned-byte-p)))
           ("Subgoal *1/3" :use fn2-ribbon-nonempty-row-start))))

(local
 (defthm fn2-ribbon-wide-band-fits
   (implies (and (natp s) (natp slots) (<= (+ s 64) slots))
            (fn2-ribbon-row-fits-p s lo hi slots))
   :hints (("Goal" :use fn2-ribbon-row-mask-width :in-theory (e/d* (ihsext-bounds-thms) (fn2-ribbon-row-mask fn2-ribbon-row-mask-width unsigned-byte-p))))))

(defthm fn2-ribbon-adapter-slot-bound
   (implies (and (posp n) (<= n 256))
            (and (<= 64 (fn2-ribbon-slots n)) (<= (fn2-ribbon-slots n) 335)))
   :hints (("Goal" :in-theory (enable fn2-ribbon-slots)))
   :rule-classes :linear)

(local
 (defthm fn2-ribbon-placed-insertion-completes
   (implies
    (and (natp base) (natp slots) (<= 64 slots) (<= slots 335)
         (unsigned-byte-p 32 h1) (unsigned-byte-p 32 h2)
         (<= (+ base slots) (fn2-ribbon-band-rows fn2-ribbon-band))
         (fn2-ribbon-band-fits-p slots base slots fn2-ribbon-band)
         (fn2-ribbon-pivots-p slots base fn2-ribbon-band))
    (mv-let (s lo hi) (fn2-ribbon-place h1 h2 slots)
      (member-eq (mv-nth 0 (fn2-ribbon-insert *fn2-ribbon-insert-steps* s lo hi base slots fn2-ribbon-band))
                 '(:ok :redundant))))
   :hints (("Goal" :use ((:instance fn2-ribbon-insert-terminates-in-band
                          (s (car (fn2-ribbon-place h1 h2 slots)))
                          (lo (mv-nth 1 (fn2-ribbon-place h1 h2 slots)))
                          (hi (mv-nth 2 (fn2-ribbon-place h1 h2 slots)))
                          (fuel *fn2-ribbon-insert-steps*)))
            :in-theory (e/d (mv-nth) (fn2-ribbon-row-fits-p fn2-ribbon-band-fits-p
                              fn2-ribbon-pivots-p unsigned-byte-p fn2-ribbon-insert))))
   :rule-classes nil))

; The clear initializes every pivot, and every fitted row can be solved.
(local
 (defthm fn2-ribbon-bit-of-truncated-word
   (implies (and (natp i) (natp width) (<= width i))
            (not (logbitp i (loghead width x))))
   :hints (("Goal" :in-theory (enable* logbitp-case-splits)))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-bit-above-width
   (implies (and (unsigned-byte-p size x) (natp size) (natp j) (<= size j))
            (not (logbitp j x)))
   :hints (("Goal" :use ((:instance loghead-identity (i x))
                         (:instance fn2-ribbon-bit-of-truncated-word (width size) (i j)))
            :in-theory (disable loghead-identity unsigned-byte-p)))))

(local
 (defthm fn2-ribbon-fit-coefficient-in-range
   (implies (and (natp s) (natp slots) (<= s slots) (natp j) (< j 64)
                 (fn2-ribbon-row-fits-p s lo hi slots)
                 (if (< j 32) (logbitp j lo) (logbitp (- j 32) hi)))
            (< (+ s j) slots))
   :hints (("Goal" :use ((:instance fn2-ribbon-bit-above-width
                          (size (- slots s)) (x (fn2-ribbon-row-mask lo hi))))
            :in-theory (e/d* (logbitp-case-splits) (unsigned-byte-p fn2-ribbon-bit-above-width))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-dot-fits
   (implies (and (natp k) (natp j) (<= (+ k j) 64)
                 (natp s) (natp base) (natp slots) (<= s slots)
                 (<= (+ base slots) (fn2-ribbon-band-rows fn2-ribbon-band))
                 (fn2-ribbon-row-fits-p s lo hi slots))
            (equal (mv-nth 0 (fn2-ribbon-dot k j (+ base s) (+ base slots) lo hi acc fn2-ribbon-band)) :ok))
   :hints (("Goal" :induct (fn2-ribbon-dot k j (+ base s) (+ base slots) lo hi acc fn2-ribbon-band)
            :in-theory (e/d (fn2-ribbon-dot) (fn2-ribbon-row-fits-p fn2-ribbon-band-z)))
           ("Subgoal *1/3" :use fn2-ribbon-fit-coefficient-in-range))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-set-z-preserves-fit
   (implies (and (natp base) (natp n) (natp x))
            (equal (fn2-ribbon-band-fits-p n base slots (fn2-ribbon-band-set-z x v fn2-ribbon-band))
                   (fn2-ribbon-band-fits-p n base slots fn2-ribbon-band)))
   :hints (("Goal" :induct (fn2-ribbon-band-fits-p n base slots fn2-ribbon-band)
            :in-theory (disable fn2-ribbon-band-set-z fn2-ribbon-row-fits-p)))))

(local
 (defthm fn2-ribbon-fitted-pivot-tail-readable
   (implies (and (natp base) (natp slots) (natp i) (< 0 i) (<= i slots)
                 (<= (+ base slots) (fn2-ribbon-band-rows fn2-ribbon-band))
                 (fn2-ribbon-band-fits-p slots base slots fn2-ribbon-band))
            (let* ((r (+ base (1- i))) (lo (fn2-ribbon-band-lo r fn2-ribbon-band))
                   (hi (fn2-ribbon-band-hi r fn2-ribbon-band)))
              (equal (mv-nth 0 (fn2-ribbon-dot 63 1 r (+ base slots) lo hi 0 fn2-ribbon-band)) :ok)))
   :hints (("Goal"
            :use ((:instance fn2-ribbon-dot-fits (s (1- i)) (k 63) (j 1) (acc 0)
                   (lo (fn2-ribbon-band-lo (+ base (1- i)) fn2-ribbon-band))
                   (hi (fn2-ribbon-band-hi (+ base (1- i)) fn2-ribbon-band)))
                  (:instance fn2-ribbon-band-row-fits (s (1- i)) (n slots)))
            :in-theory (disable fn2-ribbon-row-fits-p fn2-ribbon-band-fits-p)))))

(local
 (defthm fn2-ribbon-solve-completes
   (implies (and (natp n) (natp i) (<= n i) (natp base) (natp slots)
                 (<= i slots) (unsigned-byte-p 32 slots)
                 (<= (+ base slots) (fn2-ribbon-band-rows fn2-ribbon-band))
                 (fn2-ribbon-band-fits-p slots base slots fn2-ribbon-band))
            (equal (mv-nth 0 (fn2-ribbon-solve-rows n i base (+ base slots) seed fn2-ribbon-band)) :ok))
   :hints (("Goal" :induct (fn2-ribbon-solve-rows n i base (+ base slots) seed fn2-ribbon-band)
            :in-theory (e/d (fn2-ribbon-solve-rows)
                            (fn2-ribbon-band-set-z fn2-ribbon-band-fits-p fn2-ribbon-dot)))
           ("Subgoal *1/4" :use fn2-ribbon-fitted-pivot-tail-readable))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-clear-row-count
   (equal (fn2-ribbon-band-rows (fn2-ribbon-band-put r (lo 0) (hi 0) (z 0)))
          (fn2-ribbon-band-rows fn2-ribbon-band))
   :hints (("Goal" :in-theory (enable fn2-ribbon-band-rows fn2-ribbon-band-set-lo fn2-ribbon-band-set-hi
                                      fn2-ribbon-band-set-z update-fn2-ribbon-band-lo$ai
                                      update-fn2-ribbon-band-hi$ai update-fn2-ribbon-band-z$ai)))))

(defthm fn2-ribbon-clear-completes
   (implies (and (natp n) (natp i) (natp base) (<= (+ base i n) (fn2-ribbon-band-rows fn2-ribbon-band)))
            (equal (mv-nth 0 (fn2-ribbon-clear-rows n i base fn2-ribbon-band)) :ok))
   :hints (("Goal" :induct (fn2-ribbon-clear-rows n i base fn2-ribbon-band)
            :in-theory (e/d (fn2-ribbon-clear-rows) (fn2-ribbon-band-set-lo fn2-ribbon-band-set-hi
                                                     fn2-ribbon-band-set-z)))))

(local
 (defthm fn2-ribbon-clear-one-row
   (implies (and (natp r) (natp x))
            (let ((band (fn2-ribbon-band-put r (lo 0) (hi 0) (z 0))))
              (and (equal (fn2-ribbon-band-lo x band)
                          (if (equal x r) 0 (fn2-ribbon-band-lo x fn2-ribbon-band)))
                   (equal (fn2-ribbon-band-hi x band)
                          (if (equal x r) 0 (fn2-ribbon-band-hi x fn2-ribbon-band))))))
   :hints (("Goal" :in-theory (enable fn2-ribbon-band-lo fn2-ribbon-band-hi
                              fn2-ribbon-band-set-lo fn2-ribbon-band-set-hi fn2-ribbon-band-set-z
                              update-fn2-ribbon-band-lo$ai update-fn2-ribbon-band-hi$ai update-fn2-ribbon-band-z$ai)))))

(local
 (defthm fn2-ribbon-clear-reads
   (let* ((run (fn2-ribbon-clear-rows n i base fn2-ribbon-band)) (after (mv-nth 1 run)))
     (implies (and (natp n) (natp i) (natp p) (natp base) (equal (mv-nth 0 run) :ok))
              (and (equal (fn2-ribbon-band-lo (+ base p) after)
                          (if (and (<= i p) (< p (+ i n))) 0 (fn2-ribbon-band-lo (+ base p) fn2-ribbon-band)))
                   (equal (fn2-ribbon-band-hi (+ base p) after)
                          (if (and (<= i p) (< p (+ i n))) 0 (fn2-ribbon-band-hi (+ base p) fn2-ribbon-band))))))
   :hints (("Goal" :induct (fn2-ribbon-clear-rows n i base fn2-ribbon-band)
            :in-theory (e/d (fn2-ribbon-clear-rows)
                            (fn2-ribbon-band-set-lo fn2-ribbon-band-set-hi fn2-ribbon-band-set-z))))))

(defun fn2-ribbon-row-induct (n)
   (declare (xargs :measure (nfix n)))
   (if (zp n) nil (cons n (fn2-ribbon-row-induct (1- n)))))

(defthm fn2-ribbon-cleared-band-invariants
   (let ((after (mv-nth 1 (fn2-ribbon-clear-rows slots 0 base fn2-ribbon-band))))
     (implies (and (natp n) (natp slots) (natp base) (<= n slots)
                   (<= (+ base slots) (fn2-ribbon-band-rows fn2-ribbon-band)))
              (and (fn2-ribbon-band-fits-p n base slots after)
                   (fn2-ribbon-pivots-p n base after))))
   :hints (("Goal" :induct (fn2-ribbon-row-induct n)
            :in-theory (disable fn2-ribbon-clear-rows))
           ("Subgoal *1/2" :use ((:instance fn2-ribbon-clear-reads
                                  (i 0) (p (1- n)) (n slots))))))

; Both the add and the query hash the octets loaded in their own arena.
(defun fn2-ribbon-arena-p (slot gen pk ps pg off cap fn2-pool)
   (declare (xargs :stobjs fn2-pool :verify-guards nil))
   (and (natp off) (natp cap) (<= off cap)
        (equal (fn2-pool-workspace-code slot gen pk ps pg fn2-pool) :ok)
        (natp (fn2-pool-base slot fn2-pool))
        (<= cap (fn2-pool-cap slot fn2-pool))
        (<= off (fn2-pool-fill slot fn2-pool))
        (<= (+ (fn2-pool-base slot fn2-pool) cap) (fn2-pool-data-length fn2-pool))))

(defthm fn2-ribbon-arena-write-progress
   (let ((wr (fn2-pool-write slot gen off v pk ps pg fn2-pool)))
     (implies (and (fn2-ribbon-arena-p slot gen pk ps pg off cap fn2-pool)
                   (< off cap) (unsigned-byte-p 8 v))
              (and (equal (mv-nth 0 wr) :ok)
                   (fn2-ribbon-arena-p slot gen pk ps pg (+ 1 off) cap (mv-nth 1 wr)))))
   :hints (("Goal" :in-theory
            (enable fn2-pool-write fn2-pool-workspace-code fn2-pool-handle-code fn2-pool-ownerp
                    fn2-pool-set-fill update-fn2-pool-fill$ai update-fn2-pool-datai))))

(local
 (defthm fn2-ribbon-arena-load-progress
   (let ((wr (fn2-run-load-bytes bytes slot gen off pk ps pg fn2-pool)))
     (implies (and (fn2-ribbon-arena-p slot gen pk ps pg off cap fn2-pool)
                   (natp off) (<= (+ off (len bytes)) cap) (fn2-ribbon-bytesp bytes))
              (and (equal (mv-nth 0 wr) :ok)
                   (fn2-ribbon-arena-p slot gen pk ps pg (+ off (len bytes)) cap (mv-nth 1 wr)))))
   :hints (("Goal" :induct (fn2-run-load-bytes bytes slot gen off pk ps pg fn2-pool)
            :in-theory (e/d (fn2-run-load-bytes)
                            (fn2-pool-write fn2-ribbon-arena-p unsigned-byte-p))))))

(local
 (defthm fn2-ribbon-load-byte-at
   (let ((wr (fn2-run-load-bytes bytes slot gen off pk ps pg fn2-pool))
         (prior (fn2-pool-read slot gen p pk ps pg fn2-pool)))
     (implies (and (natp off) (natp p) (natp (fn2-pool-base slot fn2-pool))
                   (< p (+ off (len bytes))) (or (<= off p) (equal (mv-nth 0 prior) :ok))
                   (equal (mv-nth 0 wr) :ok))
              (equal (fn2-pool-read slot gen p pk ps pg (mv-nth 1 wr))
                     (if (< p off) prior (list :ok (nth (- p off) bytes))))))
   :hints (("Goal" :induct (fn2-run-load-bytes bytes slot gen off pk ps pg fn2-pool)
            :in-theory (e/d (fn2-run-load-bytes) (fn2-pool-read fn2-pool-write fn2-pool-base))))))

(defun fn2-ribbon-bytes-at-p (bytes slot gen off pk ps pg fn2-pool)
   (declare (xargs :stobjs fn2-pool :verify-guards nil))
   (if (atom bytes) t
     (mv-let (code byte) (fn2-pool-read slot gen off pk ps pg fn2-pool)
       (and (eq code :ok) (equal byte (car bytes))
            (fn2-ribbon-bytes-at-p (cdr bytes) slot gen (1+ off) pk ps pg fn2-pool)))))

(local
 (defun fn2-ribbon-key-suffix-induct (n end)
   (declare (xargs :measure (nfix (- end n))))
   (if (zp (- end n)) n (fn2-ribbon-key-suffix-induct (1+ n) end))))

(local
 (defthm fn2-ribbon-nthcdr-key
   (implies (natp n)
            (and (equal (consp (nthcdr n bytes)) (< n (len bytes)))
                 (equal (car (nthcdr n bytes)) (nth n bytes))))
   :hints (("Goal" :induct (nthcdr n bytes)) ("Subgoal *1/1" :expand (len bytes)))))

(defthm fn2-ribbon-loaded-prefix-matches
   (let ((wr (fn2-run-load-bytes bytes slot gen off pk ps pg fn2-pool)))
     (implies (and (natp off) (natp n) (<= n (len bytes))
                   (natp (fn2-pool-base slot fn2-pool)) (equal (mv-nth 0 wr) :ok))
              (fn2-ribbon-bytes-at-p (nthcdr n bytes) slot gen (+ off n) pk ps pg (mv-nth 1 wr))))
   :hints (("Goal" :induct (fn2-ribbon-key-suffix-induct n (len bytes))
            :expand ((:free (pool) (fn2-ribbon-bytes-at-p (nthcdr n bytes) slot gen (+ off n) pk ps pg pool)))
            :in-theory (disable fn2-run-load-bytes fn2-pool-read fn2-pool-base nthcdr fn2-ribbon-nthcdr-successor))
           ("Subgoal *1/2"
            :use ((:instance fn2-ribbon-load-byte-at (p (+ off n)))
                  (:instance fn2-ribbon-nthcdr-successor (s n) (z bytes))))))

(defun fn2-ribbon-key-hash-stream (bytes h)
   (if (atom bytes) h
     (fn2-ribbon-key-hash-stream (cdr bytes) (fn2-fnv-step h (car bytes)))))

(local
 (defun fn2-ribbon-key-hash-induct (bytes h1 h2 off)
   (if (atom bytes) (list h1 h2 off)
     (fn2-ribbon-key-hash-induct (cdr bytes) (fn2-fnv-step h1 (car bytes))
                                 (fn2-fnv-step h2 (car bytes)) (1+ off)))))

(local
 (defthm fn2-ribbon-hash-loop-of-key
   (implies (and (fn2-ribbon-bytes-at-p bytes slot gen off pk ps pg fn2-pool)
                 (fn2-ribbon-bytesp bytes))
            (equal (fn2-ribbon-hash-loop (len bytes) slot gen off h1 h2 pk ps pg fn2-pool)
                   (list :ok (fn2-ribbon-key-hash-stream bytes h1)
                             (fn2-ribbon-key-hash-stream bytes h2))))
   :hints (("Goal" :induct (fn2-ribbon-key-hash-induct bytes h1 h2 off)
            :in-theory (e/d (fn2-ribbon-hash-loop) (fn2-fnv-step fn2-pool-read unsigned-byte-p))))))

(defun fn2-ribbon-key-hash (bytes seed)
   (list :ok
         (fn2-ribbon-key-hash-stream bytes (fn2-ribbon-xor32 *fn2-fnv-offset-basis* seed))
         (fn2-ribbon-key-hash-stream bytes (fn2-ribbon-xor32 *fn2-fnv-offset-basis*
                           (fn2-prng-mix32 (fn2-ribbon-xor32 seed #x9e3779b9))))))

(local
 (defthm fn2-ribbon-hash-of-loaded-key
   (implies (and (fn2-ribbon-bytes-at-p bytes slot gen off pk ps pg fn2-pool)
                 (fn2-ribbon-bytesp bytes))
            (equal (fn2-ribbon-hash (len bytes) slot gen off seed pk ps pg fn2-pool)
                   (fn2-ribbon-key-hash bytes seed)))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-hash)
                                   (fn2-ribbon-bytes-at-p fn2-ribbon-bytesp fn2-ribbon-key-hash-stream))))))

(defmacro fn2-ribbon-key-load (bytes row slot gen off)
   `(fn2-run-load-values *fn2-rba-key-layout* (list ,bytes) ,row ,slot ,gen ,off 9 0 1 fn2-fields fn2-pool))

(defthm fn2-ribbon-key-reference
   (let* ((load (fn2-ribbon-key-load bytes row slot gen off))
          (fields (mv-nth 2 load)))
     (implies (natp row)
              (and (equal (mv-nth 0 load) (mv-nth 0 (fn2-run-load-bytes bytes slot gen off 9 0 1 fn2-pool)))
                   (equal (mv-nth 1 load) (+ (nfix off) (len bytes)))
                   (equal (mv-nth 3 load) (mv-nth 1 (fn2-run-load-bytes bytes slot gen off 9 0 1 fn2-pool)))
                   (equal (fn2-fields-ref-slot row fields) slot)
                   (equal (fn2-fields-ref-gen row fields) gen)
                   (equal (fn2-fields-ref-off row fields) off)
                   (equal (fn2-fields-ref-len row fields) (len bytes))
                   (equal (fn2-fields-rows fields) (fn2-fields-rows fn2-fields)))))
   :hints (("Goal" :in-theory (e/d (fn2-run-load-values fn2-run-load-ref fn2-fields-rows)
                                   (fn2-run-load-bytes)))))

(defthm fn2-ribbon-arena-rewind
   (implies (and (fn2-ribbon-arena-p slot gen pk ps pg off cap fn2-pool) (natp new) (<= new off))
            (fn2-ribbon-arena-p slot gen pk ps pg new cap fn2-pool))
   :rule-classes nil)

(defthm fn2-ribbon-arena-base-natural
   (implies (fn2-ribbon-arena-p slot gen pk ps pg off cap fn2-pool)
            (natp (fn2-pool-base slot fn2-pool)))
   :rule-classes nil)

(defthm fn2-ribbon-key-load-in-arena
   (let* ((load (fn2-ribbon-key-load bytes row slot gen off))
          (pool (mv-nth 3 load)) (next (+ off (len bytes))))
     (implies (and (natp row) (natp off) (<= off 32768) (<= (len bytes) 250)
                   (fn2-ribbon-bytesp bytes) (fn2-ribbon-arena-p slot gen 9 0 1 off 65536 fn2-pool))
              (and (equal (mv-nth 0 load) :ok)
                   (fn2-ribbon-bytes-at-p bytes slot gen off 9 0 1 pool)
                   (fn2-ribbon-arena-p slot gen 9 0 1 (if (< 32768 next) 0 next) 65536 pool))))
   :hints (("Goal"
            :use ((:instance fn2-ribbon-arena-base-natural (cap 65536) (pk 9) (ps 0) (pg 1))
                  (:instance fn2-ribbon-loaded-prefix-matches (n 0) (pk 9) (ps 0) (pg 1))
                  (:instance fn2-ribbon-arena-load-progress (cap 65536) (pk 9) (ps 0) (pg 1))
                  (:instance fn2-ribbon-arena-rewind (new 0) (cap 65536) (pk 9) (ps 0) (pg 1)
                   (off (+ off (len bytes))) (fn2-pool (mv-nth 1 (fn2-run-load-bytes bytes slot gen off 9 0 1 fn2-pool)))))
            :in-theory (disable fn2-ribbon-arena-p fn2-ribbon-bytes-at-p fn2-ribbon-bytesp fn2-run-load-bytes
                                fn2-run-load-values fn2-pool-base))))

; The real add loop installs the conjunction of the equations of its input keys.
(defun fn2-ribbon-band-ready-p (slots fn2-ribbon-band)
   (declare (xargs :stobjs fn2-ribbon-band :verify-guards nil))
   (and (natp slots) (<= 64 slots) (<= slots 335)
        (<= slots (fn2-ribbon-band-rows fn2-ribbon-band))
        (fn2-ribbon-band-fits-p slots 0 slots fn2-ribbon-band)
        (fn2-ribbon-pivots-p slots 0 fn2-ribbon-band)))

(defun fn2-ribbon-adding-p (remaining slots seed fn2-ribbon-builds)
   (declare (xargs :stobjs fn2-ribbon-builds :verify-guards nil))
   (and (< 0 (fn2-ribbon-builds-rows fn2-ribbon-builds))
        (equal (fn2-ribbon-builds-phase 0 fn2-ribbon-builds) *fn2-ribbon-phase-adding*)
        (equal (fn2-ribbon-builds-pending 0 fn2-ribbon-builds) 0)
        (equal (fn2-ribbon-builds-base 0 fn2-ribbon-builds) 0)
        (equal (fn2-ribbon-builds-slots 0 fn2-ribbon-builds) slots)
        (equal (fn2-ribbon-builds-seed 0 fn2-ribbon-builds) seed)
        (unsigned-byte-p 32 seed)
        (natp remaining) (natp (fn2-ribbon-builds-added 0 fn2-ribbon-builds))
        (equal (+ remaining (fn2-ribbon-builds-added 0 fn2-ribbon-builds))
               (fn2-ribbon-builds-keys 0 fn2-ribbon-builds))
        (<= (fn2-ribbon-builds-keys 0 fn2-ribbon-builds) 256)))

(local
 (defthm fn2-ribbon-increment-add-count
   (implies (and (posp remaining) (fn2-ribbon-adding-p remaining slots seed fn2-ribbon-builds))
            (fn2-ribbon-adding-p (1- remaining) slots seed
             (fn2-ribbon-builds-set-added 0 (+ 1 (fn2-ribbon-builds-added 0 fn2-ribbon-builds))
                                          fn2-ribbon-builds)))
   :hints (("Goal" :in-theory (enable fn2-ribbon-builds-set-added update-fn2-ribbon-builds-added$ai)))))

(local
 (defthm fn2-ribbon-insertion-row-count
   (equal (fn2-ribbon-band-rows (mv-nth 4 (fn2-ribbon-insert fuel s lo hi base slots fn2-ribbon-band)))
          (fn2-ribbon-band-rows fn2-ribbon-band))
   :hints (("Goal" :induct (fn2-ribbon-insert fuel s lo hi base slots fn2-ribbon-band)
            :in-theory (enable fn2-ribbon-insert fn2-ribbon-band-rows fn2-ribbon-band-set-lo
                               update-fn2-ribbon-band-lo$ai fn2-ribbon-band-set-hi update-fn2-ribbon-band-hi$ai)))))

(local
 (defthm fn2-ribbon-stream-width
   (implies (unsigned-byte-p 32 h) (unsigned-byte-p 32 (fn2-ribbon-key-hash-stream bytes h)))
   :hints (("Goal" :induct (fn2-ribbon-key-hash-stream bytes h)
            :in-theory (disable unsigned-byte-p fn2-fnv-step)))))

(local
 (defthm fn2-ribbon-key-hash-widths
   (and (unsigned-byte-p 32 (mv-nth 1 (fn2-ribbon-key-hash bytes seed)))
        (unsigned-byte-p 32 (mv-nth 2 (fn2-ribbon-key-hash bytes seed))))
   :hints (("Goal" :in-theory (disable fn2-ribbon-key-hash-stream unsigned-byte-p)))))

(defun fn2-ribbon-key-placement (bytes slots seed)
   (let ((h (fn2-ribbon-key-hash bytes seed)))
     (mv-list 3 (fn2-ribbon-place (mv-nth 1 h) (mv-nth 2 h) slots))))

(defmacro fn2-ribbon-insert-key (bytes slots seed)
   `(let ((p (fn2-ribbon-key-placement ,bytes ,slots ,seed)))
      (fn2-ribbon-insert *fn2-ribbon-insert-steps* (car p) (mv-nth 1 p) (mv-nth 2 p)
                         0 ,slots fn2-ribbon-band)))

(defun fn2-ribbon-key-equation (bytes slots seed z)
   (let ((p (fn2-ribbon-key-placement bytes slots seed)))
     (fn2-ribbon-equation-at (car p) (mv-nth 1 p) (mv-nth 2 p) z)))

(local
 (defthm fn2-ribbon-key-insertion-contract
   (let* ((ins (fn2-ribbon-insert-key bytes slots seed)) (after (mv-nth 4 ins)))
     (implies (fn2-ribbon-band-ready-p slots fn2-ribbon-band)
              (and (member-eq (mv-nth 0 ins) '(:ok :redundant))
                   (fn2-ribbon-band-ready-p slots after)
                   (iff (fn2-ribbon-band-satisfied-p slots 0 z after)
                        (and (fn2-ribbon-band-satisfied-p slots 0 z fn2-ribbon-band)
                             (equal (fn2-ribbon-key-equation bytes slots seed z) 0))))))
   :hints (("Goal"
            :use ((:instance fn2-ribbon-placed-insertion-completes (base 0)
                   (h1 (mv-nth 1 (fn2-ribbon-key-hash bytes seed)))
                   (h2 (mv-nth 2 (fn2-ribbon-key-hash bytes seed))))
                  (:instance fn2-ribbon-insert-solution-set (fuel *fn2-ribbon-insert-steps*) (base 0)
                   (s (car (fn2-ribbon-key-placement bytes slots seed)))
                   (lo (mv-nth 1 (fn2-ribbon-key-placement bytes slots seed)))
                   (hi (mv-nth 2 (fn2-ribbon-key-placement bytes slots seed)))))
            :in-theory (e/d (mv-nth) (fn2-ribbon-key-hash fn2-ribbon-band-fits-p fn2-ribbon-row-fits-p
                          fn2-ribbon-pivots-p fn2-ribbon-band-satisfied-p unsigned-byte-p))))
   :rule-classes nil))

(local
 (deftheory fn2-ribbon-build-readers
   '(fn2-ribbon-builds-rows fn2-ribbon-builds-phase fn2-ribbon-builds-pending
     fn2-ribbon-builds-base fn2-ribbon-builds-slots fn2-ribbon-builds-keys
     fn2-ribbon-builds-seed fn2-ribbon-builds-added fn2-ribbon-builds-set-added
     fn2-ribbon-band-rows fn2-fields-rows fn2-fields-ref-len fn2-fields-ref-off
     fn2-fields-ref-gen fn2-fields-ref-slot)))

(local (in-theory (set-difference-theories (current-theory :here) (theory 'fn2-ribbon-build-readers))))

(local
 (defthm fn2-ribbon-hash-after-key-load
   (implies (and (natp row) (natp off) (<= off 32768) (<= (len bytes) 250) (fn2-ribbon-bytesp bytes)
                 (fn2-ribbon-arena-p slot gen 9 0 1 off 65536 fn2-pool))
            (equal (fn2-ribbon-hash (len bytes) slot gen off seed 9 0 1
                                    (mv-nth 3 (fn2-ribbon-key-load bytes row slot gen off)))
                   (fn2-ribbon-key-hash bytes seed)))
   :hints (("Goal" :use (fn2-ribbon-key-load-in-arena
                         (:instance fn2-ribbon-hash-of-loaded-key (pk 9) (ps 0) (pg 1)
                          (fn2-pool (mv-nth 3 (fn2-ribbon-key-load bytes row slot gen off)))))
            :in-theory (disable fn2-ribbon-bytes-at-p fn2-ribbon-arena-p fn2-ribbon-bytesp fn2-ribbon-key-hash
                                fn2-run-load-values fn2-ribbon-key-reference fn2-ribbon-key-load-in-arena)))))


(local
 (defthm fn2-ribbon-key-insertion-status
   (implies (fn2-ribbon-band-ready-p slots fn2-ribbon-band)
            (member-eq (mv-nth 0 (fn2-ribbon-insert-key bytes slots seed)) '(:ok :redundant)))
   :hints (("Goal" :use fn2-ribbon-key-insertion-contract
            :in-theory (union-theories '(iff) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-key-hash-status
   (equal (mv-nth 0 (fn2-ribbon-key-hash bytes seed)) :ok)))

(local
 (defthm fn2-ribbon-place-first-result
   (equal (mv-nth 0 (fn2-ribbon-place h1 h2 slots)) (car (fn2-ribbon-place h1 h2 slots)))
   :hints (("Goal" :in-theory (enable mv-nth)))))

(defthm fn2-ribbon-add-loaded-key
   (let* ((load (fn2-ribbon-key-load bytes 300 slot gen off))
          (result (fn2-ribbon-add 0 300 9 0 1 fn2-ribbon-builds fn2-ribbon-band
                                  (mv-nth 2 load) (mv-nth 3 load))))
     (implies (and (fn2-ribbon-adding-p remaining slots seed fn2-ribbon-builds)
                   (posp remaining) (fn2-ribbon-band-ready-p slots fn2-ribbon-band)
                   (< 300 (fn2-fields-rows fn2-fields)) (fn2-ribbon-bytesp bytes)
                   (<= (len bytes) 250) (natp off) (<= off 32768)
                   (fn2-ribbon-arena-p slot gen 9 0 1 off 65536 fn2-pool))
              (equal result
                     (list :ok (fn2-ribbon-builds-set-added 0 (1+ (fn2-ribbon-builds-added 0 fn2-ribbon-builds))
                                                           fn2-ribbon-builds)
                           (mv-nth 4 (fn2-ribbon-insert-key bytes slots seed))))))
   :hints (("Goal"
            :use (fn2-ribbon-key-insertion-status (:instance fn2-ribbon-hash-after-key-load (row 300)))
            :in-theory (e/d (fn2-ribbon-add fn2-ribbon-key-placement)
                            (fn2-ribbon-bytes-at-p fn2-ribbon-bytesp fn2-ribbon-arena-p fn2-ribbon-key-hash
                             fn2-ribbon-key-load-in-arena fn2-ribbon-hash-after-key-load fn2-ribbon-hash-of-loaded-key
                             fn2-ribbon-band-fits-p fn2-ribbon-pivots-p fn2-ribbon-key-equation
                             fn2-ribbon-band-satisfied-p fn2-run-load-values fn2-run-load-bytes))))
   :rule-classes nil)

(defmacro fn2-ribbon-adapter-add (key slot gen off)
   `(let ((load (fn2-ribbon-key-load ,key 300 ,slot ,gen ,off)))
      (fn2-ribbon-add 0 300 9 0 1 fn2-ribbon-builds fn2-ribbon-band (mv-nth 2 load) (mv-nth 3 load))))

(defthm fn2-ribbon-adapter-adds-one-equation
   (let ((result (fn2-ribbon-adapter-add bytes slot gen off)))
     (implies (and (fn2-ribbon-adding-p remaining slots seed fn2-ribbon-builds)
                   (posp remaining) (fn2-ribbon-band-ready-p slots fn2-ribbon-band)
                   (< 300 (fn2-fields-rows fn2-fields)) (fn2-ribbon-bytesp bytes)
                   (<= (len bytes) 250) (natp off) (<= off 32768)
                   (fn2-ribbon-arena-p slot gen 9 0 1 off 65536 fn2-pool))
              (and (equal (mv-nth 0 result) :ok)
                   (fn2-ribbon-adding-p (1- remaining) slots seed (mv-nth 1 result))
                   (fn2-ribbon-band-ready-p slots (mv-nth 2 result))
                   (iff (fn2-ribbon-band-satisfied-p slots 0 z (mv-nth 2 result))
                        (and (fn2-ribbon-band-satisfied-p slots 0 z fn2-ribbon-band)
                             (equal (fn2-ribbon-key-equation bytes slots seed z) 0))))))
   :hints (("Goal" :use (fn2-ribbon-add-loaded-key fn2-ribbon-key-insertion-contract)
            :in-theory (union-theories
             '(fn2-ribbon-increment-add-count mv-nth-of-cons car-cons cdr-cons
               (:e zp) (:e binary-+) (:e consp) (:e equal))
             (theory 'minimal-theory))))
   :rule-classes nil)

(defun fn2-ribbon-key-equations-p (keys slots seed z)
   (if (atom keys) t
     (and (equal (fn2-ribbon-key-equation (car keys) slots seed z) 0)
          (fn2-ribbon-key-equations-p (cdr keys) slots seed z))))

(local
 (defthm fn2-ribbon-load-fields-and-next-offset
   (let ((load (fn2-ribbon-key-load bytes 300 slot gen off)))
     (and (equal (fn2-fields-rows (mv-nth 2 load)) (fn2-fields-rows fn2-fields))
          (equal (mv-nth 1 load) (+ (nfix off) (len bytes)))))
   :hints (("Goal" :use ((:instance fn2-ribbon-key-reference (row 300)))
            :in-theory (disable fn2-run-load-values fn2-ribbon-key-reference)))))

(fn2-rba-defun fn2-ribbon-adds-induct (keys slot gen off)
   (if (atom keys) (fn2-rba-mv nil)
     (b* (((mv & next fn2-fields fn2-pool)
           (fn2-ribbon-key-load (car keys) 300 slot gen off))
          ((mv & fn2-ribbon-builds fn2-ribbon-band)
           (fn2-ribbon-add 0 300 9 0 1 fn2-ribbon-builds fn2-ribbon-band fn2-fields fn2-pool)))
       (fn2-rba-call fn2-ribbon-adds-induct (cdr keys) slot gen (if (< 32768 next) 0 next)))))

(defthm fn2-ribbon-adds-key-equations
   (let ((result (fn2-rba-call fn2-rba-adds keys slot gen off)))
     (implies (and (fn2-ribbon-keysp keys)
                   (fn2-ribbon-adding-p (len keys) slots seed fn2-ribbon-builds)
                   (fn2-ribbon-band-ready-p slots fn2-ribbon-band)
                   (< 300 (fn2-fields-rows fn2-fields)) (natp off) (<= off 32768)
                   (fn2-ribbon-arena-p slot gen 9 0 1 off 65536 fn2-pool))
              (and (equal (mv-nth 0 result) :ok)
                   (fn2-ribbon-adding-p 0 slots seed (mv-nth 1 result))
                   (fn2-ribbon-band-ready-p slots (mv-nth 2 result))
                   (iff (fn2-ribbon-band-satisfied-p slots 0 z (mv-nth 2 result))
                        (and (fn2-ribbon-band-satisfied-p slots 0 z fn2-ribbon-band)
                             (fn2-ribbon-key-equations-p keys slots seed z))))))
   :hints (("Goal"
            :induct (fn2-rba-call fn2-ribbon-adds-induct keys slot gen off)
            :in-theory (e/d (fn2-rba-adds)
                         (fn2-ribbon-adding-p fn2-ribbon-band-ready-p fn2-ribbon-arena-p
                          fn2-ribbon-key-placement fn2-ribbon-key-equation fn2-ribbon-band-satisfied-p
                          fn2-ribbon-bytes-at-p fn2-ribbon-bytesp fn2-run-load-values fn2-run-load-bytes
                          fn2-ribbon-add fn2-rba-drive fn2-ribbon-key-reference
                          fn2-ribbon-emit-reads fn2-ribbon-probe-dot))
            :expand ((fn2-rba-call fn2-rba-adds keys slot gen off) (len keys) (fn2-ribbon-keysp keys) (fn2-ribbon-key-equations-p keys slots seed z)))
           ("Subgoal *1/2"
            :use ((:instance fn2-ribbon-adapter-adds-one-equation (bytes (car keys)) (remaining (len keys)))
                  (:instance fn2-ribbon-key-load-in-arena (bytes (car keys)) (row 300)))))
   :rule-classes nil)

; The adapter's full key list constrains the solved bytes read by the probe.
(local
 (defthm fn2-ribbon-member-equation
   (implies (and (fn2-ribbon-key-equations-p keys slots seed z) (member-equal key keys))
            (equal (fn2-ribbon-key-equation key slots seed z) 0))
   :hints (("Goal" :induct (fn2-ribbon-key-equations-p keys slots seed z)
            :in-theory (disable fn2-ribbon-key-equation)))))

(local
 (defthm fn2-ribbon-ready-band-solution
   (let ((solve (fn2-ribbon-solve-rows slots slots 0 slots seed fn2-ribbon-band)))
     (implies (fn2-ribbon-band-ready-p slots fn2-ribbon-band)
              (and (equal (mv-nth 0 solve) :ok)
                   (fn2-ribbon-band-satisfied-p slots 0
                    (fn2-ribbon-band-suffix 0 slots (mv-nth 1 solve)) fn2-ribbon-band))))
   :hints (("Goal" :use ((:instance fn2-ribbon-solve-completes (i slots) (n slots) (base 0))
                         (:instance fn2-ribbon-solved-system (end slots) (n slots) (base 0)))
            :in-theory (disable fn2-ribbon-band-fits-p fn2-ribbon-pivots-p
                                fn2-ribbon-band-satisfied-p fn2-ribbon-band-suffix fn2-ribbon-solved-system)))
   :rule-classes nil))

(defthm fn2-ribbon-adds-and-solve-satisfy-all-keys
   (let* ((added (fn2-rba-call fn2-rba-adds keys slot gen off))
          (band (mv-nth 2 added))
          (solve (fn2-ribbon-solve-rows slots slots 0 slots seed band))
          (z (fn2-ribbon-band-suffix 0 slots (mv-nth 1 solve))))
     (implies (and (fn2-ribbon-keysp keys)
                   (fn2-ribbon-adding-p (len keys) slots seed fn2-ribbon-builds)
                   (fn2-ribbon-band-ready-p slots fn2-ribbon-band)
                   (< 300 (fn2-fields-rows fn2-fields)) (natp off) (<= off 32768)
                   (fn2-ribbon-arena-p slot gen 9 0 1 off 65536 fn2-pool))
              (and (equal (mv-nth 0 added) :ok)
                   (equal (mv-nth 0 solve) :ok)
                   (fn2-ribbon-key-equations-p keys slots seed z))))
   :hints (("Goal"
            :use ((:instance fn2-ribbon-adds-key-equations
                   (z (fn2-ribbon-band-suffix 0 slots (mv-nth 1 (fn2-ribbon-solve-rows slots slots 0 slots seed
                       (mv-nth 2 (fn2-rba-call fn2-rba-adds keys slot gen off)))))))
                  (:instance fn2-ribbon-ready-band-solution
                   (fn2-ribbon-band (mv-nth 2 (fn2-rba-call fn2-rba-adds keys slot gen off)))))
            :in-theory (union-theories '(iff) (theory 'minimal-theory))))
   :rule-classes nil)

(local
 (defthm fn2-ribbon-probe-dot-evaluates-row
   (implies (and (natp s) (natp end)
                 (fn2-ribbon-solution-bytes-agree-p 64 0 s end s pslot pgen pk ps pg fn2-ribbon-band fn2-pool))
            (equal (fn2-ribbon-probe-dot 64 0 s lo hi 0 pslot pgen pk ps pg fn2-pool)
                   (list :ok (fn2-ribbon-equation-at s lo hi (fn2-ribbon-band-suffix 0 end fn2-ribbon-band)))))
   :hints (("Goal" :use ((:instance fn2-ribbon-dot-result-pair (k 64) (j 0) (r s) (acc 0))
                         (:instance fn2-ribbon-probe-dot-agrees-with-band (k 64) (j 0) (r s) (acc 0))
                         (:instance fn2-ribbon-dot-evaluates-equation-at (base 0)))
            :in-theory (disable fn2-ribbon-probe-dot-agrees-with-band fn2-ribbon-solution-bytes-agree-p
                                fn2-ribbon-band-suffix)))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-probe-dot-evaluates-key
   (let* ((p (fn2-ribbon-key-placement bytes slots seed)) (s (car p)) (lo (mv-nth 1 p)) (hi (mv-nth 2 p)))
     (implies (and (natp slots) (natp s)
                   (fn2-ribbon-solution-bytes-agree-p 64 0 s slots s pslot pgen pk ps pg fn2-ribbon-band fn2-pool))
              (equal (fn2-ribbon-probe-dot 64 0 s lo hi 0 pslot pgen pk ps pg fn2-pool)
                     (list :ok (fn2-ribbon-key-equation bytes slots seed
                                 (fn2-ribbon-band-suffix 0 slots fn2-ribbon-band))))))
   :hints (("Goal" :use ((:instance fn2-ribbon-probe-dot-evaluates-row
                           (s (car (fn2-ribbon-key-placement bytes slots seed)))
                           (lo (mv-nth 1 (fn2-ribbon-key-placement bytes slots seed)))
                           (hi (mv-nth 2 (fn2-ribbon-key-placement bytes slots seed)))
                           (end slots)))
            :in-theory (e/d (fn2-ribbon-key-equation) (fn2-ribbon-key-placement
                       fn2-ribbon-solution-bytes-agree-p fn2-ribbon-band-suffix))))
   :rule-classes nil))

(local
 (defun-nx fn2-ribbon-query-header-p (hb pslot pgen slots seed fields pool)
   (let* ((header (fn2-ribbon-read-header pslot pgen hb 9 0 1 fields pool))
          (decoded (mv-nth 1 header)) (c (+ hb *fn2-run-c-header-fields*)))
     (and (equal (mv-nth 0 header) :ok)
          (equal (fn2-fields-value (+ c *fn2-ribbon-header-field-seed*) decoded) seed)
          (equal (fn2-fields-value (+ c *fn2-ribbon-header-field-slots*) decoded) slots)))))

(local
 (defthm fn2-ribbon-probe-reads-equation
   (let* ((load (fn2-ribbon-key-load bytes 301 slot gen off))
          (fields (mv-nth 2 load)) (pool (mv-nth 3 load))
          (s (car (fn2-ribbon-key-placement bytes slots seed))))
     (implies (and (natp slots) (unsigned-byte-p 32 seed)
                   (< 301 (fn2-fields-rows fn2-fields)) (fn2-ribbon-bytesp bytes) (<= (len bytes) 250)
                   (natp off) (<= off 32768) (fn2-ribbon-arena-p slot gen 9 0 1 off 65536 fn2-pool)
                   (fn2-ribbon-query-header-p 200 pslot pgen slots seed fields pool)
                   (fn2-ribbon-solution-bytes-agree-p 64 0 s slots s pslot pgen 9 0 1 fn2-ribbon-band pool))
              (equal (mv-nth 0 (fn2-ribbon-probe pslot pgen 200 301 9 0 1 9 0 1 fields pool))
                     (if (equal (fn2-ribbon-key-equation bytes slots seed
                                 (fn2-ribbon-band-suffix 0 slots fn2-ribbon-band)) 0) :maybe :absent))))
   :hints (("Goal"
            :use ((:instance fn2-ribbon-probe-dot-evaluates-key (pk 9) (ps 0) (pg 1)
                   (fn2-pool (mv-nth 3 (fn2-ribbon-key-load bytes 301 slot gen off))))
                  (:instance fn2-ribbon-hash-after-key-load (row 301)))
            :in-theory (e/d (fn2-ribbon-probe fn2-ribbon-key-placement)
                            (fn2-ribbon-key-equation fn2-ribbon-band-suffix fn2-ribbon-solution-bytes-agree-p
                             fn2-ribbon-key-hash fn2-ribbon-arena-p fn2-ribbon-bytesp fn2-fields-value
                             fn2-ribbon-read-header fn2-run-load-values fn2-run-load-bytes))))
   :rule-classes nil))

; Page sealing and checking preserve the serialized solution in the pool.
(local
 (defmacro fn2-ribbon-page-frame (name op first-args index disabled &key induct)
   (let ((call (append (list op) first-args
                       '(fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))))
     `(defthm ,name
        (equal (mv-nth ,index ,call) fn2-pool)
        :hints (("Goal" ,@(and induct (list :induct call))
                 :in-theory (e/d (,op) ,disabled)))))))

(local
 (fn2-ribbon-page-frame fn2-ribbon-fc-byte-page-pool fn2-fc-byte
   (row :page sealp slot gen off len base pk ps pg) 3
   (fn2-b3-byte fn2-b3-finalize fn2-b3-read fn2-fc-check-byte fn2-fc-digest-byte fn2-fc-context-hash-word fn2-pool-write)))

(local
 (fn2-ribbon-page-frame fn2-ribbon-fc-advance-page-pool fn2-fc-advance
   (fuel row :page sealp slot gen off len base pk ps pg) 4 (fn2-fc-byte fn2-fc-page-span)))

(local
 (fn2-ribbon-page-frame fn2-ribbon-fc-run-bytes-page-pool fn2-fc-run-bytes
   (fuel row :page sealp slot gen off len base pk ps pg) 3 (fn2-fc-advance) :induct t))

(local
 (fn2-ribbon-page-frame fn2-ribbon-fc-step-page-pool fn2-fc-step
   (row :page sealp slot gen off len base pk ps pg budget) 4
   (fn2-fc-run-bytes fn2-fc-decoded fn2-fc-decode-step fn2-fc-start fn2-b3-init fn2-layout-range-code)))

(local
 (fn2-ribbon-page-frame fn2-ribbon-format-run-page-pool fn2-format-run
   (:page sealp row slot gen off len base pk ps pg budget) 4 (fn2-fc-step fn2-fc-reset)))

(local
 (fn2-ribbon-page-frame fn2-ribbon-format-drive-page-pool fn2-format-drive
   (fuel row :page sealp slot gen off len base pk ps pg budget) 4 (fn2-format-run) :induct t))

(defthm fn2-ribbon-rba-check-preserves-page
   (equal (mv-nth 6 (fn2-rba-call fn2-rba-check pslot pgen)) fn2-pool)
   :hints (("Goal" :in-theory (e/d (fn2-rba-check) (fn2-format-drive)))))

(local
 (defthm fn2-ribbon-run-seal-preserves-page
   (equal (mv-nth 5 (fn2-run-seal-step w row hrow budget fn2-run-writers fn2-fc fn2-fc-context
                                       fn2-b3 fn2-fields fn2-pool fn2-digests)) fn2-pool)
   :hints (("Goal" :in-theory (e/d (fn2-run-seal-step)
                                    (fn2-format-run fn2-digest-rowp fn2-b3-ready fn2-fields-rows))))))

(defthm fn2-ribbon-seal-preserves-page
   (equal (mv-nth 6 (fn2-ribbon-seal f budget fn2-ribbon-builds fn2-run-writers fn2-fc fn2-fc-context
                                     fn2-b3 fn2-fields fn2-pool fn2-digests)) fn2-pool)
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-seal) (fn2-run-seal-step)))))

; At the adapter budget, finishing the build solves the band in one step.
(defun fn2-ribbon-solving-p (slots seed fn2-ribbon-builds)
   (declare (xargs :stobjs fn2-ribbon-builds :verify-guards nil))
   (and (< 0 (fn2-ribbon-builds-rows fn2-ribbon-builds))
        (equal (fn2-ribbon-builds-phase 0 fn2-ribbon-builds) *fn2-ribbon-phase-solving*)
        (equal (fn2-ribbon-builds-i 0 fn2-ribbon-builds) slots)
        (equal (fn2-ribbon-builds-slots 0 fn2-ribbon-builds) slots)
        (equal (fn2-ribbon-builds-base 0 fn2-ribbon-builds) 0)
        (equal (fn2-ribbon-builds-seed 0 fn2-ribbon-builds) seed) (unsigned-byte-p 32 seed)))

(defthm fn2-ribbon-finish-starts-solve
   (implies (fn2-ribbon-adding-p 0 slots seed fn2-ribbon-builds)
            (let ((finish (fn2-ribbon-finish 0 fn2-ribbon-builds)))
              (and (equal (mv-nth 0 finish) :ok)
                   (fn2-ribbon-solving-p slots seed (mv-nth 1 finish)))))
   :hints (("Goal" :in-theory (enable fn2-ribbon-finish fn2-ribbon-builds-phase fn2-ribbon-builds-slots
                         fn2-ribbon-builds-base fn2-ribbon-builds-seed fn2-ribbon-builds-rows
                         fn2-ribbon-builds-set-phase fn2-ribbon-builds-set-i
                         update-fn2-ribbon-builds-phase$ai update-fn2-ribbon-builds-i$ai))))

(defthm fn2-ribbon-adapter-solve-step
   (implies (and (fn2-ribbon-solving-p slots seed fn2-ribbon-builds)
                 (fn2-ribbon-band-ready-p slots fn2-ribbon-band))
            (let ((step (fn2-ribbon-solve-step 0 4096 fn2-ribbon-builds fn2-ribbon-band)))
              (and (equal (mv-nth 0 step) :more)
                   (equal (fn2-ribbon-builds-phase 0 (mv-nth 1 step)) *fn2-ribbon-phase-emitting*)
                   (equal (mv-nth 2 step) (mv-nth 1 (fn2-ribbon-solve-rows slots slots 0 slots seed fn2-ribbon-band))))))
   :hints (("Goal" :use fn2-ribbon-ready-band-solution
            :in-theory (e/d (fn2-ribbon-solve-step fn2-ribbon-builds-phase fn2-ribbon-builds-set-phase
                             fn2-ribbon-builds-set-i update-fn2-ribbon-builds-phase$ai update-fn2-ribbon-builds-i$ai)
                     (fn2-ribbon-builds-i fn2-ribbon-solve-rows fn2-ribbon-band-fits-p fn2-ribbon-pivots-p
                      fn2-ribbon-band-satisfied-p fn2-ribbon-band-suffix)))))

(local
 (defthm fn2-ribbon-solved-byte-width
   (implies (and (fn2-ribbon-bandp fn2-ribbon-band) (fn2-ribbon-band-wfp fn2-ribbon-band)
                 (natp i) (< i (fn2-ribbon-band-rows fn2-ribbon-band)))
            (unsigned-byte-p 8 (fn2-ribbon-band-z i fn2-ribbon-band)))
   :hints (("Goal" :use (fn2-ribbon-band-z-natp fn2-ribbon-band-z-bound)
            :in-theory (disable fn2-ribbon-bandp fn2-ribbon-band-wfp fn2-ribbon-band-z)))))

(defthm fn2-ribbon-emit-to-workspace
   (let ((emit (fn2-ribbon-emit-bytes n i base slot gen off pk ps pg fn2-ribbon-band fn2-pool)))
     (implies (and (natp base) (natp n) (natp i) (natp off)
                   (fn2-ribbon-bandp fn2-ribbon-band) (fn2-ribbon-band-wfp fn2-ribbon-band)
                   (<= (+ base i n) (fn2-ribbon-band-rows fn2-ribbon-band))
                   (<= (+ off i n) cap)
                   (fn2-ribbon-arena-p slot gen pk ps pg (+ off i) cap fn2-pool))
              (and (equal (mv-nth 0 emit) :ok)
                   (fn2-ribbon-arena-p slot gen pk ps pg (+ off i n) cap (mv-nth 1 emit)))))
   :hints (("Goal" :induct (fn2-ribbon-emit-bytes n i base slot gen off pk ps pg fn2-ribbon-band fn2-pool)
            :in-theory (e/d (fn2-ribbon-emit-bytes)
                            (fn2-ribbon-arena-p fn2-pool-write fn2-ribbon-bandp fn2-ribbon-band-wfp
                             fn2-ribbon-band-z unsigned-byte-p)))
           ("Subgoal *1/3" :use ((:instance fn2-ribbon-arena-write-progress
                                 (off (+ off i)) (v (fn2-ribbon-band-z (+ base i) fn2-ribbon-band)))))
           ("Subgoal *1/2" :use ((:instance fn2-ribbon-arena-write-progress
                                 (off (+ off i)) (v (fn2-ribbon-band-z (+ base i) fn2-ribbon-band)))))))

; The writer zeroes the reserved header and the trailing page padding in place.
(defthm fn2-ribbon-zero-arena
   (let ((wr (fn2-run-zero n slot gen pos pk ps pg fn2-pool)))
     (implies (and (natp n) (natp pos) (<= (+ pos n) cap)
                   (fn2-ribbon-arena-p slot gen pk ps pg pos cap fn2-pool))
              (and (equal (mv-nth 0 wr) :ok)
                   (fn2-ribbon-arena-p slot gen pk ps pg (+ pos n) cap (mv-nth 1 wr)))))
   :hints (("Goal" :induct (fn2-run-zero n slot gen pos pk ps pg fn2-pool)
            :in-theory (e/d (fn2-run-zero) (fn2-pool-write fn2-ribbon-arena-p)))
           ("Subgoal *1/3" :use ((:instance fn2-ribbon-arena-write-progress (off pos) (v 0))))
           ("Subgoal *1/2" :use ((:instance fn2-ribbon-arena-write-progress (off pos) (v 0))))))

(defthm fn2-ribbon-read-through-padding
   (let ((wr (fn2-run-zero n slot gen pos pk ps pg fn2-pool))
         (prior (fn2-pool-read slot gen i pk ps pg fn2-pool)))
     (implies (and (natp n) (natp pos) (natp i) (natp (fn2-pool-base slot fn2-pool))
                   (< i (+ pos n)) (or (<= pos i) (equal (mv-nth 0 prior) :ok))
                   (equal (mv-nth 0 wr) :ok))
              (equal (fn2-pool-read slot gen i pk ps pg (mv-nth 1 wr))
                     (if (< i pos) prior (list :ok 0)))))
   :hints (("Goal" :induct (fn2-run-zero n slot gen pos pk ps pg fn2-pool)
            :in-theory (e/d (fn2-run-zero) (fn2-pool-read fn2-pool-write fn2-pool-base)))))

(defun fn2-ribbon-padding-p (cursor pos slot gen fn2-run-writers fn2-pool)
   (declare (xargs :stobjs (fn2-run-writers fn2-pool) :verify-guards nil))
   (and (natp cursor) (natp pos) (<= (+ cursor pos) *fn2-run-page-size*)
        (equal (fn2-run-writers-phase 0 fn2-run-writers) *fn2-run-writer-phase-closing*)
        (equal (fn2-run-writers-restarts 0 fn2-run-writers) 0)
        (equal (fn2-run-writers-pos 0 fn2-run-writers) pos)
        (equal (fn2-run-writers-cursor 0 fn2-run-writers) cursor)
        (equal (fn2-run-writers-slot 0 fn2-run-writers) slot)
        (equal (fn2-run-writers-gen 0 fn2-run-writers) gen)
        (equal (fn2-run-writers-okind 0 fn2-run-writers) 9)
        (equal (fn2-run-writers-oslot 0 fn2-run-writers) 0)
        (equal (fn2-run-writers-ogen 0 fn2-run-writers) 1)
        (fn2-ribbon-arena-p slot gen 9 0 1 (+ cursor pos) *fn2-run-page-size* fn2-pool)))

(defthm fn2-ribbon-writer-advances-padding
   (let* ((wr (fn2-run-close-step 0 4096 fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
          (n (min 4096 (- *fn2-run-page-size* (+ cursor pos)))))
     (implies (and (fn2-ribbon-padding-p cursor pos slot gen fn2-run-writers fn2-pool)
                   (< (+ cursor pos) *fn2-run-page-size*))
              (and (equal (mv-nth 0 wr) :more)
                   (fn2-ribbon-padding-p cursor (+ pos n) slot gen (mv-nth 1 wr) (mv-nth 3 wr))
                   (equal (mv-nth 3 wr)
                          (mv-nth 1 (fn2-run-zero n slot gen (+ cursor pos) 9 0 1 fn2-pool))))))
   :hints (("Goal" :use ((:instance fn2-ribbon-zero-arena
                           (n (min 4096 (- *fn2-run-page-size* (+ cursor pos)))) (pos (+ cursor pos))
                           (pk 9) (ps 0) (pg 1) (cap *fn2-run-page-size*)))
            :in-theory (e/d (fn2-run-close-step fn2-run-writers-pos fn2-run-writers-phase fn2-run-writers-restarts
                             fn2-run-writers-cursor fn2-run-writers-slot fn2-run-writers-gen
                             fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen
                             fn2-run-writers-set-pos update-fn2-run-writers-pos$ai)
                            (nth update-nth fn2-run-writers-fields fn2-run-zero fn2-ribbon-arena-p fn2-run-write-restarts))))
   :rule-classes nil)

(defthm fn2-ribbon-writer-finishes-padding
   (let ((wr (fn2-run-close-step 0 4096 fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)))
     (implies (and (fn2-ribbon-padding-p cursor pos slot gen fn2-run-writers fn2-pool)
                   (equal (+ cursor pos) *fn2-run-page-size*))
              (and (equal (mv-nth 0 wr) :ok)
                   (equal (fn2-run-writers-phase 0 (mv-nth 1 wr)) *fn2-run-writer-phase-heading*)
                   (equal (mv-nth 2 wr) fn2-fields) (equal (mv-nth 3 wr) fn2-pool))))
   :hints (("Goal" :in-theory (e/d (fn2-run-close-step fn2-run-writers-phase fn2-run-writers-set-phase
                                     update-fn2-run-writers-phase$ai)
                                   (nth update-nth fn2-ribbon-arena-p fn2-run-zero fn2-run-write-restarts))))
   :rule-classes nil)

; A query-arena write preserves every readable byte of the preceding page.
(defun fn2-ribbon-page-before-arena-p (pslot slot fn2-pool)
   (declare (xargs :stobjs fn2-pool :verify-guards nil))
   (and (natp pslot) (natp slot) (not (equal pslot slot))
        (natp (fn2-pool-base pslot fn2-pool)) (natp (fn2-pool-base slot fn2-pool))
        (<= (+ (fn2-pool-base pslot fn2-pool) *fn2-run-page-size*) (fn2-pool-base slot fn2-pool))))

(local
 (defthm fn2-ribbon-page-read-across-arena-write
   (let ((after (mv-nth 1 (fn2-pool-write slot gen off byte 9 0 1 fn2-pool))))
     (implies (and (fn2-ribbon-page-before-arena-p pslot slot fn2-pool)
                   (natp off) (natp i) (< i *fn2-run-page-size*)
                   (equal (mv-nth 0 (fn2-pool-read pslot pgen i 9 0 1 fn2-pool)) :ok))
              (equal (fn2-pool-read pslot pgen i 9 0 1 after)
                     (fn2-pool-read pslot pgen i 9 0 1 fn2-pool))))
   :hints (("Goal" :in-theory (e/d (fn2-pool-write fn2-pool-read fn2-pool-readable-code
                               fn2-pool-handle-code fn2-pool-ownerp fn2-pool-set-fill
                               update-fn2-pool-fill$ai update-fn2-pool-datai)
                             (fn2-pool-workspace-code nth update-nth))))))

(defthm fn2-ribbon-bases-of-pool-write
   (equal (fn2-pool-base other (mv-nth 1 (fn2-pool-write slot gen off byte pk ps pg fn2-pool)))
          (fn2-pool-base other fn2-pool))
   :hints (("Goal" :in-theory (e/d (fn2-pool-base fn2-pool-write fn2-pool-set-fill
                              update-fn2-pool-fill$ai update-fn2-pool-datai)
                            (fn2-pool-workspace-code nth update-nth)))))

(defthm fn2-ribbon-bases-of-arena-load
   (equal (fn2-pool-base other (mv-nth 1 (fn2-run-load-bytes bytes slot gen off pk ps pg fn2-pool)))
          (fn2-pool-base other fn2-pool))
   :hints (("Goal" :induct (fn2-run-load-bytes bytes slot gen off pk ps pg fn2-pool)
            :in-theory (e/d (fn2-run-load-bytes) (fn2-pool-base fn2-pool-write)))))

(local
 (defthm fn2-ribbon-page-read-across-arena-load
   (let ((after (mv-nth 1 (fn2-run-load-bytes bytes slot gen off 9 0 1 fn2-pool))))
     (implies (and (fn2-ribbon-page-before-arena-p pslot slot fn2-pool)
                   (natp off) (natp i) (< i *fn2-run-page-size*)
                   (equal (mv-nth 0 (fn2-pool-read pslot pgen i 9 0 1 fn2-pool)) :ok))
              (equal (fn2-pool-read pslot pgen i 9 0 1 after)
                     (fn2-pool-read pslot pgen i 9 0 1 fn2-pool))))
   :hints (("Goal" :induct (fn2-run-load-bytes bytes slot gen off 9 0 1 fn2-pool)
            :in-theory (e/d (fn2-run-load-bytes) (fn2-pool-base fn2-pool-write fn2-pool-read)))
           ("Subgoal *1/3" :use ((:instance fn2-ribbon-page-read-across-arena-write (byte (car bytes))))))))

(defun fn2-ribbon-solution-page-p (n pslot pgen fn2-ribbon-band fn2-pool)
   (declare (xargs :stobjs (fn2-ribbon-band fn2-pool) :measure (nfix n) :verify-guards nil))
   (if (zp n) t
     (b* ((i (1- n)) (z (fn2-ribbon-band-z i fn2-ribbon-band))
            ((mv code byte) (fn2-pool-read pslot pgen (+ *fn2-ribbon-base* i) 9 0 1 fn2-pool)))
       (and (< i (fn2-ribbon-band-rows fn2-ribbon-band)) (unsigned-byte-p 8 z)
            (equal code :ok) (equal byte z)
            (fn2-ribbon-solution-page-p i pslot pgen fn2-ribbon-band fn2-pool)))))

(local
 (defthm fn2-ribbon-solution-page-at
   (let ((z (fn2-ribbon-band-z i fn2-ribbon-band))
         (read (fn2-pool-read pslot pgen (+ *fn2-ribbon-base* i) 9 0 1 fn2-pool)))
     (implies (and (fn2-ribbon-solution-page-p n pslot pgen fn2-ribbon-band fn2-pool)
                   (natp n) (natp i) (< i n))
              (and (< i (fn2-ribbon-band-rows fn2-ribbon-band)) (unsigned-byte-p 8 z)
                   (equal (mv-nth 0 read) :ok) (equal (mv-nth 1 read) z))))
   :hints (("Goal" :induct (fn2-ribbon-row-induct n)
            :in-theory (disable fn2-pool-read fn2-ribbon-band-z unsigned-byte-p)))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-solution-page-window
   (implies (and (fn2-ribbon-solution-page-p slots pslot pgen fn2-ribbon-band fn2-pool)
                 (natp k) (natp j) (natp start) (natp slots) (<= (+ start j k) slots))
            (fn2-ribbon-solution-bytes-agree-p k j start slots start pslot pgen 9 0 1 fn2-ribbon-band fn2-pool))
   :hints (("Goal" :induct (fn2-ribbon-span-induct k j)
            :in-theory (disable fn2-ribbon-solution-page-p fn2-pool-read fn2-ribbon-band-z unsigned-byte-p))
           ("Subgoal *1/2" :use ((:instance fn2-ribbon-solution-page-at (n slots) (i (+ start j))))))))

(local
 (defthm fn2-ribbon-load-keeps-solution-page
   (implies (and (fn2-ribbon-solution-page-p n pslot pgen fn2-ribbon-band fn2-pool)
                 (fn2-ribbon-page-before-arena-p pslot slot fn2-pool) (natp off)
                 (natp n) (<= (+ *fn2-ribbon-base* n) *fn2-run-page-size*))
            (fn2-ribbon-solution-page-p n pslot pgen fn2-ribbon-band
              (mv-nth 1 (fn2-run-load-bytes bytes slot gen off 9 0 1 fn2-pool))))
   :hints (("Goal" :induct (fn2-ribbon-row-induct n)
            :in-theory (disable fn2-ribbon-band-z fn2-pool-read fn2-run-load-bytes fn2-ribbon-page-before-arena-p unsigned-byte-p)))))

; Decoded header fields and solved page bytes determine the complete query loop.
(local
 (defthm fn2-ribbon-probe-fields-are-decoded-fields
   (let* ((load (fn2-ribbon-key-load bytes 301 slot gen off))
          (fields (mv-nth 2 load)) (pool (mv-nth 3 load)))
     (implies (and (< 301 (fn2-fields-rows fn2-fields)) (natp off) (<= (len bytes) 250))
              (equal (mv-nth 1 (fn2-ribbon-probe pslot pgen 200 301 9 0 1 9 0 1 fields pool))
                     (mv-nth 1 (fn2-ribbon-read-header pslot pgen 200 9 0 1 fields pool)))))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-probe)
                      (nth fn2-ribbon-read-header fn2-ribbon-hash fn2-ribbon-place fn2-ribbon-probe-dot
                       fn2-fields-value fn2-run-load-values fn2-run-load-bytes))))))

(local
 (defun-nx fn2-ribbon-query-headers-p (queries slot gen off pslot pgen slots seed fields pool)
   (if (atom queries) t
     (let* ((load (fn2-run-load-values *fn2-rba-key-layout* (list (car queries)) 301 slot gen off 9 0 1 fields pool))
            (after-fields (mv-nth 2 load)) (after-pool (mv-nth 3 load)) (next (mv-nth 1 load))
            (header (fn2-ribbon-read-header pslot pgen 200 9 0 1 after-fields after-pool)))
       (and (fn2-ribbon-query-header-p 200 pslot pgen slots seed after-fields after-pool)
            (fn2-ribbon-query-headers-p (cdr queries) slot gen (if (< 32768 next) 0 next)
                                       pslot pgen slots seed (mv-nth 1 header) after-pool))))))

(local
 (defthm fn2-ribbon-query-placement-bounds
   (implies (and (natp slots) (<= 64 slots))
            (let ((s (car (fn2-ribbon-key-placement bytes slots seed))))
              (and (natp s) (<= (+ 64 s) slots))))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-key-placement) (fn2-ribbon-key-hash fn2-ribbon-place))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-separation-after-key-load
   (equal (fn2-ribbon-page-before-arena-p pslot slot
            (mv-nth 3 (fn2-ribbon-key-load bytes 301 slot gen off)))
          (fn2-ribbon-page-before-arena-p pslot slot fn2-pool))
   :hints (("Goal" :in-theory (disable fn2-run-load-values fn2-run-load-bytes fn2-pool-base)))))

(local
 (defthm fn2-ribbon-load-and-probe
   (let* ((load (fn2-ribbon-key-load bytes 301 slot gen off))
          (fields (mv-nth 2 load)) (pool (mv-nth 3 load)) (next (mv-nth 1 load))
          (answer (fn2-ribbon-probe pslot pgen 200 301 9 0 1 9 0 1 fields pool)))
     (implies (and (natp slots) (<= 64 slots) (<= slots 335) (unsigned-byte-p 32 seed)
                   (fn2-ribbon-solution-page-p slots pslot pgen fn2-ribbon-band fn2-pool)
                   (fn2-ribbon-page-before-arena-p pslot slot fn2-pool)
                   (< 301 (fn2-fields-rows fn2-fields)) (fn2-ribbon-bytesp bytes) (<= (len bytes) 250)
                   (natp off) (<= off 32768) (fn2-ribbon-arena-p slot gen 9 0 1 off 65536 fn2-pool)
                   (fn2-ribbon-query-header-p 200 pslot pgen slots seed fields pool))
              (and (equal (mv-nth 0 load) :ok)
                   (equal (mv-nth 0 answer)
                          (if (equal (fn2-ribbon-key-equation bytes slots seed
                                      (fn2-ribbon-band-suffix 0 slots fn2-ribbon-band)) 0) :maybe :absent))
                   (equal (mv-nth 1 answer) (mv-nth 1 (fn2-ribbon-read-header pslot pgen 200 9 0 1 fields pool)))
                   (equal (fn2-fields-rows (mv-nth 1 answer)) (fn2-fields-rows fn2-fields))
                   (natp (if (< 32768 next) 0 next)) (<= (if (< 32768 next) 0 next) 32768)
                   (fn2-ribbon-arena-p slot gen 9 0 1 (if (< 32768 next) 0 next) 65536 pool)
                   (fn2-ribbon-page-before-arena-p pslot slot pool)
                   (fn2-ribbon-solution-page-p slots pslot pgen fn2-ribbon-band pool))))
   :hints (("Goal" :use (fn2-ribbon-query-placement-bounds fn2-ribbon-separation-after-key-load fn2-ribbon-probe-fields-are-decoded-fields fn2-ribbon-probe-reads-equation
                         (:instance fn2-ribbon-load-keeps-solution-page (n slots))
                         (:instance fn2-ribbon-key-load-in-arena (row 301))
                         (:instance fn2-ribbon-solution-page-window (k 64) (j 0)
                           (start (car (fn2-ribbon-key-placement bytes slots seed)))
                           (fn2-pool (mv-nth 3 (fn2-ribbon-key-load bytes 301 slot gen off)))))
            :in-theory (e/d ()
                            (nth fn2-ribbon-page-before-arena-p fn2-ribbon-key-placement fn2-ribbon-separation-after-key-load fn2-ribbon-probe fn2-ribbon-read-header fn2-ribbon-query-header-p
                              fn2-ribbon-solution-page-p fn2-ribbon-solution-bytes-agree-p fn2-ribbon-key-hash
                              fn2-ribbon-arena-p fn2-ribbon-key-equation fn2-ribbon-band-suffix
                              fn2-fields-rows fn2-pool-base fn2-ribbon-bytesp fn2-run-load-values fn2-run-load-bytes))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-query-loop-sound
   (implies (and (fn2-ribbon-keysp queries) (natp slots) (<= 64 slots) (<= slots 335)
                 (unsigned-byte-p 32 seed) (natp off) (<= off 32768)
                 (< 301 (fn2-fields-rows fn2-fields))
                 (fn2-ribbon-page-before-arena-p pslot slot fn2-pool)
                 (fn2-ribbon-arena-p slot gen 9 0 1 off 65536 fn2-pool)
                 (fn2-ribbon-solution-page-p slots pslot pgen fn2-ribbon-band fn2-pool)
                 (fn2-ribbon-key-equations-p keys slots seed (fn2-ribbon-band-suffix 0 slots fn2-ribbon-band))
                 (fn2-ribbon-query-headers-p queries slot gen off pslot pgen slots seed fn2-fields fn2-pool))
            (fn2-ribbon-answers-sound keys queries
               (mv-nth 0 (fn2-rba-call fn2-rba-probes queries slot gen off pslot pgen))))
   :hints (("Goal" :induct (fn2-ribbon-query-headers-p queries slot gen off pslot pgen slots seed fn2-fields fn2-pool)
            :in-theory (union-theories '(fn2-rba-probes fn2-ribbon-query-headers-p fn2-ribbon-keysp
                           fn2-ribbon-answers-sound iff mv-nth-of-cons car-cons cdr-cons atom not
                           (:e equal) (:e zp) (:e binary-+) (:e mv-nth) (:e consp) (:e not))
                         (theory 'minimal-theory)))
           ("Subgoal *1/3" :use ((:instance fn2-ribbon-load-and-probe (bytes (car queries)))
                                 (:instance fn2-ribbon-member-equation (key (car queries))
                                  (z (fn2-ribbon-band-suffix 0 slots fn2-ribbon-band)))))
           ("Subgoal *1/2" :use ((:instance fn2-ribbon-load-and-probe (bytes (car queries)))
                                 (:instance fn2-ribbon-member-equation (key (car queries))
                                  (z (fn2-ribbon-band-suffix 0 slots fn2-ribbon-band))))))
   :rule-classes nil))

; Both generated header decoders expose the scalar values read from their slice of page bytes.
(local
 (defthm fn2-ribbon-save-keeps-field-value
   (equal (fn2-fields-value i (fn2-codec-save base phase pos acc high size ref payload next fn2-fields))
          (fn2-fields-value i fn2-fields))
   :hints (("Goal" :in-theory (e/d (fn2-codec-save fn2-fields-value)
                                    (nth update-nth unsigned-byte-p))))))

(local
 (defthm fn2-ribbon-store-field-value
   (implies (and (natp i) (natp watch) (< i (fn2-fields-rows fn2-fields)) (unsigned-byte-p 60 v)
                 (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen))
            (equal (fn2-fields-value watch (fn2-layout-store i v slot gen 0 0 0 fn2-fields))
                   (if (equal i watch) v (fn2-fields-value watch fn2-fields))))
   :hints (("Goal" :in-theory (e/d (fn2-layout-store fn2-fields-value) (nth update-nth unsigned-byte-p))))))

(local
 (defmacro fn2-ribbon-scalar-header-proof (name)
   (let ((path (fn2-codec-symbol name "-SCALAR-BYTES-P"))
         (walk (fn2-codec-symbol name "-SCALAR-INDUCT"))
         (scan (fn2-codec-symbol name "-SCAN")) (bytefn (fn2-codec-symbol name "-BYTE"))
         (indexfn (fn2-codec-symbol name "-FIELD-INDEX")) (nextfn (fn2-codec-symbol name "-NEXT-PHASE"))
         (emptyfn (fn2-codec-symbol name "-EMPTY-P")) (done (fn2-codec-phase name 'done)))
     `(progn
       (defun ,path (bytes vals phase pos acc hi)
         (declare (xargs :verify-guards nil))
         (if (atom bytes) (equal phase ,done)
           (b* (((unless (and (natp phase) (< phase ,done) (equal (,indexfn phase) phase)
                              (equal (,nextfn phase) (1+ phase)) (not (,emptyfn phase))
                              (unsigned-byte-p 8 (car bytes)))) nil)
                ((mv code v high size payload) (,bytefn phase pos acc hi 0 0 (car bytes))))
             (and (natp v) (natp high) (equal size 0) (equal payload 0)
                  (if (eq code :done)
                      (and (unsigned-byte-p 60 v) (equal (nth phase vals) v)
                           (,path (cdr bytes) vals (1+ phase) 0 0 0))
                    (and (eq code :part)
                         (,path (cdr bytes) vals phase (1+ pos) v high)))))))
       (defun ,walk (bytes fuel base phase pos acc hi next slot gen fn2-fields)
         (declare (irrelevant fuel next) (xargs :stobjs fn2-fields :verify-guards nil))
         (if (atom bytes) fn2-fields
           (mv-let (code v high size payload) (,bytefn phase pos acc hi 0 0 (car bytes))
             (declare (ignore size payload))
             (if (eq code :done)
                 (let ((fn2-fields (fn2-layout-store (+ base phase) v slot gen 0 0 0 fn2-fields)))
                   (,walk (cdr bytes) (1- fuel) base (1+ phase) 0 0 0 (1+ next) slot gen fn2-fields))
               (,walk (cdr bytes) (1- fuel) base phase (1+ pos) v high (1+ next) slot gen fn2-fields)))))
       (defthm ,(fn2-codec-symbol name "-SCANS-SCALAR-BYTES")
         (let ((result (,scan fuel base phase pos acc hi 0 0 0 next slot gen end 9 0 1 fn2-fields fn2-pool)))
           (implies (and (,path bytes vals phase pos acc hi)
                         (fn2-ribbon-bytes-at-p bytes slot gen next 9 0 1 fn2-pool)
                         (natp base) (<= (+ base ,done) (fn2-fields-rows fn2-fields))
                         (natp fuel) (<= (len bytes) fuel) (natp next) (<= (+ next (len bytes)) end)
                         (natp watch) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen))
                    (and (equal (mv-nth 0 result) :ok)
                         (equal (mv-nth 1 result) (+ next (len bytes)))
                         (equal (fn2-fields-value watch (mv-nth 2 result))
                                (if (and (<= (+ base phase) watch) (< watch (+ base ,done)))
                                    (nth (- watch base) vals) (fn2-fields-value watch fn2-fields))))))
         :hints (("Goal" :induct (,walk bytes fuel base phase pos acc hi next slot gen fn2-fields)
                  :expand ((,scan fuel base ,done pos acc hi 0 0 0 next slot gen end 9 0 1 fn2-fields fn2-pool)
                           (,scan fuel base phase pos acc hi 0 0 0 next slot gen end 9 0 1 fn2-fields fn2-pool)
                           (,path bytes vals phase pos acc hi) (fn2-ribbon-bytes-at-p bytes slot gen next 9 0 1 fn2-pool))
                  :in-theory (e/d ()
                         (,scan ,path fn2-ribbon-bytes-at-p nth unsigned-byte-p fn2-layout-store fn2-codec-save fn2-fields-value fn2-fields-rows
                          fn2-pool-read ,bytefn ,indexfn ,nextfn ,emptyfn))))
         :rule-classes nil)))))

(local (fn2-ribbon-scalar-header-proof fn2-format-page-header))

(local (fn2-ribbon-scalar-header-proof fn2-ribbon-header))

(local
 (defthm fn2-ribbon-initial-decode-registers
   (let ((fields (fn2-codec-save base 0 0 0 0 0 0 0 0 fn2-fields)))
     (implies (and (natp base) (< base (fn2-fields-rows fn2-fields)))
              (and (equal (fn2-fields-decode-phase base fields) 0) (equal (fn2-fields-decode-next base fields) 0)
                   (equal (fn2-fields-decode-pos base fields) 0) (equal (fn2-fields-decode-acc base fields) 0)
                   (equal (fn2-fields-decode-high base fields) 0) (equal (fn2-fields-decode-size base fields) 0)
                   (equal (fn2-fields-decode-ref base fields) 0) (equal (fn2-fields-decode-payload base fields) 0))))
   :hints (("Goal" :in-theory (e/d (fn2-codec-save fn2-fields-decode-phase fn2-fields-decode-next
                              fn2-fields-decode-pos fn2-fields-decode-acc fn2-fields-decode-high fn2-fields-decode-size
                              fn2-fields-decode-ref fn2-fields-decode-payload)
                             (nth update-nth fn2-fields-rows))))))

(local
 (defmacro fn2-ribbon-scalar-readback (name)
   (let ((decode (fn2-codec-symbol name "-DECODE")) (step (fn2-codec-symbol name "-DECODE-STEP"))
         (start (fn2-codec-symbol name "-START")) (scan (fn2-codec-symbol name "-SCAN"))
         (path (fn2-codec-symbol name "-SCALAR-BYTES-P")) (done (fn2-codec-phase name 'done)))
     `(defthm ,(fn2-codec-symbol name "-DECODES-SCALAR-BYTES")
        (let ((result (,decode base slot gen off end 9 0 1 fn2-fields fn2-pool)))
          (implies (and (,path bytes vals 0 0 0 0) (fn2-ribbon-bytes-at-p bytes slot gen off 9 0 1 fn2-pool)
                        (equal (fn2-layout-range-code slot gen off end nil 9 0 1 fn2-pool) :ok)
                        (natp base) (<= (+ base ,done) (fn2-fields-rows fn2-fields))
                        (unsigned-byte-p 32 off) (unsigned-byte-p 32 end) (<= (+ off (len bytes)) end)
                        (<= (len bytes) *fn2-codec-decode-fuel*)
                        (natp watch) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen))
                   (and (equal (mv-nth 0 result) :ok) (equal (mv-nth 1 result) (+ off (len bytes)))
                        (equal (fn2-fields-value watch (mv-nth 2 result))
                               (if (and (<= base watch) (< watch (+ base ,done)))
                                   (nth (- watch base) vals) (fn2-fields-value watch fn2-fields))))))
        :hints (("Goal" :use ((:instance ,(fn2-codec-symbol name "-SCANS-SCALAR-BYTES")
                    (phase 0) (pos 0) (acc 0) (hi 0) (next off) (fuel *fn2-codec-decode-fuel*)
                    (fn2-fields (,start base fn2-fields))))
                 :in-theory (e/d (,decode ,step ,start)
                    (,scan ,path fn2-ribbon-bytes-at-p fn2-layout-range-code fn2-codec-save
                     nth fn2-fields-rows fn2-fields-value fn2-fields-decode-phase fn2-fields-decode-next
                     fn2-fields-decode-pos fn2-fields-decode-acc fn2-fields-decode-high fn2-fields-decode-size
                     fn2-fields-decode-ref fn2-fields-decode-payload))))
        :rule-classes nil))))

(local (fn2-ribbon-scalar-readback fn2-format-page-header))

(local (fn2-ribbon-scalar-readback fn2-ribbon-header))

; Only the admitted key count varies in the two serialized headers.
(defun fn2-ribbon-page-values (n)
   (list *fn2-format-page-magic* *fn2-format-version* *page-kind-partitioned-filter* 1 1 5 2 3
         *fn2-run-header-area* (+ (- *fn2-ribbon-base* *fn2-run-header-area*) (fn2-ribbon-slots n))))

(defun fn2-ribbon-filter-values (n)
   (list 1 7 (fn2-ribbon-seed 7) n (fn2-ribbon-slots n) *fn2-ribbon-width* *fn2-ribbon-bits*))

(local
 (defun fn2-ribbon-header-models-p (n)
   (let* ((b (fn2-ribbon-page-values n)) (c (fn2-ribbon-filter-values n))
          (bb (fn2-layout-octets *fn2-format-page-header* b)) (cb (fn2-layout-octets *fn2-ribbon-header* c)))
     (and (fn2-format-page-header-scalar-bytes-p bb b 0 0 0 0) (<= (len bb) *fn2-run-header-area*)
          (fn2-ribbon-header-scalar-bytes-p cb c 0 0 0 0) (<= (+ *fn2-run-header-area* (len cb)) *fn2-ribbon-base*)))))

(local
 (defun fn2-ribbon-headers-through (limit)
   (if (zp limit) t
     (and (fn2-ribbon-header-models-p limit) (fn2-ribbon-headers-through (1- limit))))))

(local
 (defthm fn2-ribbon-headers-at-key-count
   (implies (and (fn2-ribbon-headers-through limit) (posp n) (natp limit) (<= n limit))
            (fn2-ribbon-header-models-p n))
   :hints (("Goal" :induct (fn2-ribbon-row-induct limit) :in-theory (disable fn2-ribbon-header-models-p)))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-header-models-for-admitted-key-counts
   (implies (and (posp n) (<= n 256)) (fn2-ribbon-header-models-p n))
   :hints (("Goal" :use ((:instance fn2-ribbon-headers-at-key-count (limit 256)))
            :in-theory (disable fn2-ribbon-header-models-p fn2-ribbon-headers-through)))
   :rule-classes nil))

(defun fn2-ribbon-physical-headers-p (n slot gen fn2-pool)
   (declare (xargs :stobjs fn2-pool :verify-guards nil))
   (and (equal (fn2-layout-range-code slot gen 0 *fn2-run-header-area* nil 9 0 1 fn2-pool) :ok)
        (equal (fn2-layout-range-code slot gen *fn2-run-header-area* *fn2-ribbon-base* nil 9 0 1 fn2-pool) :ok)
        (fn2-ribbon-bytes-at-p (fn2-layout-octets *fn2-format-page-header* (fn2-ribbon-page-values n))
                               slot gen 0 9 0 1 fn2-pool)
        (fn2-ribbon-bytes-at-p (fn2-layout-octets *fn2-ribbon-header* (fn2-ribbon-filter-values n))
                               slot gen *fn2-run-header-area* 9 0 1 fn2-pool)))

(local
 (defmacro fn2-ribbon-header-fields (name vals off end)
   (let* ((layout (fn2-codec-constant name "")) (decode (fn2-codec-symbol name "-DECODE"))
         (count (fn2-codec-phase name 'done)) (bytes `(fn2-layout-octets ,layout (,vals n))))
     `(defthm ,(fn2-codec-symbol name "-READS-RIBBON-FIELDS")
        (let ((result (,decode base slot gen ,off ,end 9 0 1 fn2-fields fn2-pool)))
          (implies (and (posp n) (<= n 256) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                        (natp base) (natp watch) (<= (+ base ,count) (fn2-fields-rows fn2-fields))
                        (fn2-ribbon-physical-headers-p n slot gen fn2-pool))
                   (and (equal (mv-nth 0 result) :ok)
                        (equal (mv-nth 1 result) (+ ,off (len ,bytes)))
                        (equal (fn2-fields-value watch (mv-nth 2 result))
                               (if (and (<= base watch) (< watch (+ base ,count)))
                                   (nth (- watch base) (,vals n)) (fn2-fields-value watch fn2-fields))))))
        :hints (("Goal" :use (fn2-ribbon-header-models-for-admitted-key-counts
                                (:instance ,(fn2-codec-symbol name "-DECODES-SCALAR-BYTES")
                                 (off ,off) (end ,end) (bytes ,bytes) (vals (,vals n))))
                 :in-theory (disable ,decode fn2-ribbon-page-values fn2-ribbon-filter-values
                      fn2-ribbon-header-scalar-bytes-p fn2-format-page-header-scalar-bytes-p
                      len nth fn2-layout-range-code fn2-layout-octets fn2-ribbon-bytes-at-p fn2-fields-value fn2-fields-rows)))
        :rule-classes nil))))

(local (fn2-ribbon-header-fields fn2-format-page-header fn2-ribbon-page-values 0 *fn2-run-header-area*))

(local (fn2-ribbon-header-fields fn2-ribbon-header fn2-ribbon-filter-values *fn2-run-header-area* *fn2-ribbon-base*))

(local
 (defmacro fn2-ribbon-decoded-page-fields (base slot gen)
   `(mv-nth 2 (fn2-format-page-header-decode ,base ,slot ,gen 0 *fn2-run-header-area* 9 0 1 fn2-fields fn2-pool))))

(local
 (defthm fn2-ribbon-fields-after-both-headers
   (let* ((b (fn2-format-page-header-decode 200 slot gen 0 *fn2-run-header-area* 9 0 1 fn2-fields fn2-pool))
          (c (fn2-ribbon-header-decode 210 slot gen *fn2-run-header-area* *fn2-ribbon-base* 9 0 1 (mv-nth 2 b) fn2-pool)))
     (implies (and (posp n) (<= n 256) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                   (< 301 (fn2-fields-rows fn2-fields)) (natp watch)
                   (fn2-ribbon-physical-headers-p n slot gen fn2-pool))
              (and (equal (mv-nth 0 b) :ok) (equal (mv-nth 0 c) :ok)
                   (equal (fn2-fields-value watch (mv-nth 2 c))
                          (cond ((and (<= 210 watch) (< watch 217)) (nth (- watch 210) (fn2-ribbon-filter-values n)))
                                ((and (<= 200 watch) (< watch 210)) (nth (- watch 200) (fn2-ribbon-page-values n)))
                                (t (fn2-fields-value watch fn2-fields)))))))
   :hints (("Goal" :use ((:instance fn2-format-page-header-reads-ribbon-fields (base 200))
                         (:instance fn2-ribbon-header-reads-ribbon-fields (base 210)
                           (fn2-fields (fn2-ribbon-decoded-page-fields 200 slot gen))))
            :in-theory (disable fn2-ribbon-physical-headers-p fn2-format-page-header-decode fn2-ribbon-header-decode
                                fn2-ribbon-filter-values fn2-ribbon-page-values fn2-layout-octets fn2-fields-value
                                fn2-fields-rows nth)))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-read-physical-headers
   (implies (and (posp n) (<= n 256) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                 (< 301 (fn2-fields-rows fn2-fields))
                 (fn2-ribbon-physical-headers-p n slot gen fn2-pool))
            (fn2-ribbon-query-header-p 200 slot gen (fn2-ribbon-slots n) (fn2-ribbon-seed 7) fn2-fields fn2-pool))
   :hints (("Goal" :use ((:instance fn2-ribbon-fields-after-both-headers (watch 200))
                         (:instance fn2-ribbon-fields-after-both-headers (watch 202))
                         (:instance fn2-ribbon-fields-after-both-headers (watch 208))
                         (:instance fn2-ribbon-fields-after-both-headers (watch 209))
                         (:instance fn2-ribbon-fields-after-both-headers (watch 212))
                         (:instance fn2-ribbon-fields-after-both-headers (watch 214))
                         (:instance fn2-ribbon-fields-after-both-headers (watch 215))
                         (:instance fn2-ribbon-fields-after-both-headers (watch 216)))
            :in-theory (e/d (fn2-ribbon-query-header-p fn2-ribbon-read-header)
                         (fn2-ribbon-physical-headers-p fn2-ribbon-slots fn2-layout-octets fn2-fields-value fn2-fields-rows
                          fn2-format-page-header-decode fn2-ribbon-header-decode))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-page-range-after-arena-write
   (implies (and (natp pslot) (natp slot) (not (equal pslot slot))
                 (equal (fn2-layout-range-code pslot pgen start end nil 9 0 1 fn2-pool) :ok))
            (equal (fn2-layout-range-code pslot pgen start end nil 9 0 1
                     (mv-nth 1 (fn2-pool-write slot gen off byte 9 0 1 fn2-pool))) :ok))
   :hints (("Goal" :in-theory (e/d (fn2-layout-range-code fn2-pool-write fn2-pool-readable-code
                          fn2-pool-handle-code fn2-pool-ownerp fn2-pool-slot-fill fn2-pool-slot-base
                          fn2-pool-capacity-bytes fn2-pool-set-fill update-fn2-pool-fill$ai update-fn2-pool-datai)
                        (nth update-nth unsigned-byte-p fn2-pool-workspace-code))))))

(local
 (defthm fn2-ribbon-page-range-after-arena-load
   (implies (and (natp pslot) (natp slot) (not (equal pslot slot))
                 (equal (fn2-layout-range-code pslot pgen start end nil 9 0 1 fn2-pool) :ok))
            (equal (fn2-layout-range-code pslot pgen start end nil 9 0 1
                     (mv-nth 1 (fn2-run-load-bytes bytes slot gen off 9 0 1 fn2-pool))) :ok))
   :hints (("Goal" :induct (fn2-run-load-bytes bytes slot gen off 9 0 1 fn2-pool)
            :in-theory (e/d (fn2-run-load-bytes) (fn2-pool-write fn2-layout-range-code))))))

(local
 (defthm fn2-ribbon-header-bytes-after-arena-load
   (implies (and (fn2-ribbon-bytes-at-p header pslot pgen start 9 0 1 fn2-pool)
                 (natp start) (<= (+ start (len header)) *fn2-run-page-size*)
                 (fn2-ribbon-page-before-arena-p pslot slot fn2-pool) (natp off))
            (fn2-ribbon-bytes-at-p header pslot pgen start 9 0 1
               (mv-nth 1 (fn2-run-load-bytes bytes slot gen off 9 0 1 fn2-pool))))
   :hints (("Goal" :induct (fn2-ribbon-bytes-at-p header pslot pgen start 9 0 1 fn2-pool)
            :in-theory (disable fn2-ribbon-page-before-arena-p fn2-run-load-bytes fn2-pool-read)))))

(local
 (defthm fn2-ribbon-key-load-keeps-physical-headers
   (implies (and (posp n) (<= n 256) (natp off)
                 (fn2-ribbon-page-before-arena-p pslot slot fn2-pool)
                 (fn2-ribbon-physical-headers-p n pslot pgen fn2-pool))
            (fn2-ribbon-physical-headers-p n pslot pgen (mv-nth 3 (fn2-ribbon-key-load bytes 301 slot gen off))))
   :hints (("Goal"
            :use (fn2-ribbon-header-models-for-admitted-key-counts
                  (:instance fn2-ribbon-header-bytes-after-arena-load (start 0)
                    (header (fn2-layout-octets *fn2-format-page-header* (fn2-ribbon-page-values n))))
                  (:instance fn2-ribbon-header-bytes-after-arena-load (start *fn2-run-header-area*)
                    (header (fn2-layout-octets *fn2-ribbon-header* (fn2-ribbon-filter-values n)))))
            :in-theory (disable fn2-ribbon-bytes-at-p fn2-ribbon-filter-values fn2-ribbon-page-values
                 fn2-layout-range-code fn2-layout-octets fn2-fields-rows fn2-run-load-values fn2-run-load-bytes
                 fn2-ribbon-header-scalar-bytes-p fn2-format-page-header-scalar-bytes-p fn2-pool-base len)))
   :rule-classes nil))

(local
 (defun-nx fn2-ribbon-query-state-induct (queries slot gen off pslot pgen fields pool)
   (if (atom queries) nil
     (let* ((load (fn2-run-load-values *fn2-rba-key-layout* (list (car queries)) 301 slot gen off 9 0 1 fields pool))
            (next (mv-nth 1 load)) (after-pool (mv-nth 3 load))
            (header (fn2-ribbon-read-header pslot pgen 200 9 0 1 (mv-nth 2 load) after-pool)))
       (cons (mv-nth 0 header) (fn2-ribbon-query-state-induct (cdr queries) slot gen (if (< 32768 next) 0 next)
                                pslot pgen (mv-nth 1 header) after-pool))))))

(local
 (defthm fn2-ribbon-all-queries-decode-physical-headers
   (implies (and (posp n) (<= n 256) (unsigned-byte-p 32 pslot) (unsigned-byte-p 60 pgen)
                 (< 301 (fn2-fields-rows fn2-fields)) (natp off)
                 (fn2-ribbon-page-before-arena-p pslot slot fn2-pool)
                 (fn2-ribbon-physical-headers-p n pslot pgen fn2-pool))
            (fn2-ribbon-query-headers-p queries slot gen off pslot pgen (fn2-ribbon-slots n) (fn2-ribbon-seed 7) fn2-fields fn2-pool))
   :hints (("Goal" :induct (fn2-ribbon-query-state-induct queries slot gen off pslot pgen fn2-fields fn2-pool)
            :in-theory (disable nth fn2-ribbon-query-header-p fn2-ribbon-slots fn2-ribbon-physical-headers-p
                                fn2-ribbon-page-before-arena-p fn2-fields-rows fn2-ribbon-read-header
                                fn2-run-load-values fn2-run-load-bytes))
           ("Subgoal *1/2"
            :use ((:instance fn2-ribbon-separation-after-key-load (bytes (car queries)))
                  (:instance fn2-ribbon-key-load-keeps-physical-headers (bytes (car queries)))
                  (:instance fn2-ribbon-read-physical-headers (slot pslot) (gen pgen)
                    (fn2-fields (mv-nth 2 (fn2-ribbon-key-load (car queries) 301 slot gen off)))
                    (fn2-pool (mv-nth 3 (fn2-ribbon-key-load (car queries) 301 slot gen off)))))))
   :rule-classes nil))

(defthm fn2-ribbon-probes-on-serialized-solution
   (let ((n (len keys)) (slots (fn2-ribbon-slots (len keys))) (seed (fn2-ribbon-seed 7)))
     (implies (and (posp n) (<= n 256) (fn2-ribbon-keysp queries)
                   (unsigned-byte-p 32 pslot) (unsigned-byte-p 60 pgen)
                   (< 301 (fn2-fields-rows fn2-fields)) (natp off) (<= off 32768)
                   (fn2-ribbon-page-before-arena-p pslot slot fn2-pool)
                   (fn2-ribbon-arena-p slot gen 9 0 1 off 65536 fn2-pool)
                   (fn2-ribbon-physical-headers-p n pslot pgen fn2-pool)
                   (fn2-ribbon-solution-page-p slots pslot pgen fn2-ribbon-band fn2-pool)
                   (fn2-ribbon-key-equations-p keys slots seed (fn2-ribbon-band-suffix 0 slots fn2-ribbon-band)))
              (fn2-ribbon-answers-sound keys queries
                 (mv-nth 0 (fn2-rba-call fn2-rba-probes queries slot gen off pslot pgen)))))
   :hints (("Goal" :use ((:instance fn2-ribbon-all-queries-decode-physical-headers (n (len keys)))
                         (:instance fn2-ribbon-query-loop-sound (slots (fn2-ribbon-slots (len keys)))
                                                               (seed (fn2-ribbon-seed 7))))
            :in-theory (disable fn2-ribbon-slots fn2-rba-probes fn2-ribbon-answers-sound fn2-ribbon-key-equations-p
              fn2-ribbon-band-suffix fn2-ribbon-physical-headers-p fn2-ribbon-solution-page-p fn2-ribbon-arena-p
              fn2-ribbon-page-before-arena-p fn2-ribbon-query-headers-p fn2-ribbon-keysp fn2-fields-rows)))
   :rule-classes nil)

; The independent checker decodes with the entire page as its input range.
(defthm fn2-ribbon-checker-decodes-serialized-page
  (let ((step (fn2-fc-decode-step :page 0 slot gen 0 65536 9 0 1 4096 (fn2-fc-start :page 0 fn2-fields) fn2-pool)))
    (implies (and (posp n) (<= n 256) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                   (< 301 (fn2-fields-rows fn2-fields)) (natp watch) (< watch 10)
                   (fn2-ribbon-physical-headers-p n slot gen fn2-pool)
                   (equal (fn2-layout-range-code slot gen 0 65536 nil 9 0 1 fn2-pool) :ok))
             (and (equal (mv-nth 0 step) :ok) (natp (mv-nth 1 step)) (<= (mv-nth 1 step) *fn2-run-header-area*)
                  (equal (fn2-fields-value watch (mv-nth 2 step)) (nth watch (fn2-ribbon-page-values n))))))
  :hints (("Goal" :use (fn2-ribbon-header-models-for-admitted-key-counts
                  (:instance fn2-format-page-header-scans-scalar-bytes
                    (bytes (fn2-layout-octets *fn2-format-page-header* (fn2-ribbon-page-values n)))
                    (vals (fn2-ribbon-page-values n)) (fuel 4096) (base 0) (phase 0) (pos 0) (acc 0) (hi 0)
                    (next 0) (end 65536) (fn2-fields (fn2-format-page-header-start 0 fn2-fields))))
           :in-theory (e/d (fn2-fc-decode-step fn2-fc-start fn2-format-page-header-decode-step fn2-format-page-header-start)
                         (fn2-format-page-header-scan fn2-ribbon-page-values fn2-ribbon-filter-values
                          fn2-ribbon-header-scalar-bytes-p fn2-format-page-header-scalar-bytes-p fn2-codec-save
                          fn2-layout-octets fn2-ribbon-bytes-at-p len nth fn2-layout-range-code fn2-fields-value fn2-fields-rows
                          fn2-fields-decode-phase fn2-fields-decode-next fn2-fields-decode-pos fn2-fields-decode-acc
                          fn2-fields-decode-high fn2-fields-decode-size fn2-fields-decode-ref fn2-fields-decode-payload))))
  :rule-classes nil)
