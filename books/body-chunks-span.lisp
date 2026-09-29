; fn: appending a span of the octet buffer to a held body (lane chunked-body,
; row B6; books/body-chunks.lisp).
;
; books/wire-scan.lisp takes a run of ordinary octets inside a line in one
; step.  In article mode the run goes into the body's store
; (books/body-chunks.lisp) straight from the buffer: `fn-bchs-push-span'
; packs the span a block at a time (divide and conquer within a block) and
; never builds a list of it.
;
; KEYSTONE fn-bchs-push-span-is-push-list (no hypothesis): the span append
; IS the per-octet append over the span's octets, for every store -- so the
; scan stays EQUAL to the per-byte fold.  When the store's tail is not well
; formed (never, on a store the wire built) the span append falls back to
; the per-octet step; the test is constant work (fn-bch-tail-okp).

(in-package "ACL2")
(include-book "body-chunks")
(include-book "octets-stobj")
(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "std/lists/append" :dir :system))

; The octets [I, K) of the buffer, first first (the specification; no host
; path executes it).
(defun fn-bchs-slice (i k fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp k) (<= i k)
                              (<= k (fn-octets-len fn-octets)))
                  :measure (nfix (- k i))))
  (if (and (natp i) (natp k) (< i k))
      (cons (fn-octets-get i fn-octets) (fn-bchs-slice (+ 1 i) k fn-octets))
    nil))

(defthm fn-bchs-slice-true-listp
  (true-listp (fn-bchs-slice i k fn-octets))
  :rule-classes :type-prescription)

(defthm fn-bchs-len-of-slice
  (equal (len (fn-bchs-slice i k fn-octets))
         (if (and (natp i) (natp k) (< i k)) (- k i) 0)))

(defthm fn-bchs-slice-empty
  (implies (not (and (natp i) (natp k) (< i k)))
           (equal (fn-bchs-slice i k fn-octets) nil)))

(defthm fn-bchs-slice-split
  (implies (and (natp i) (natp j) (natp k) (<= i j) (<= j k))
           (equal (fn-bchs-slice i k fn-octets)
                  (append (fn-bchs-slice i j fn-octets)
                          (fn-bchs-slice j k fn-octets))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bchs-slice i j fn-octets))))

(defthm fn-bchs-slice-snoc
  (implies (and (natp i) (natp j) (< i j))
           (equal (fn-bchs-slice i j fn-octets)
                  (append (fn-bchs-slice i (- j 1) fn-octets)
                          (list (fn-octets-get (- j 1) fn-octets)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bchs-slice-split (j (- j 1)) (k j))))))

; -----------------------------------------------------------------------------
; Packing a span.  A few octets by a loop from the last one down (fixnum
; arithmetic below 8 octets); more by halves.

(defun fn-bchs-pack-down (i j acc fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp j) (<= i j)
                              (<= j (fn-octets-len fn-octets))
                              (natp acc))
                  :measure (nfix (- j i))))
  (if (and (natp i) (natp j) (< i j))
      (fn-bchs-pack-down i (- j 1)
                         (+ (fn-bch-byte (fn-octets-get (- j 1) fn-octets)) (* 256 (nfix acc)))
                         fn-octets)
    (nfix acc)))

(defthm fn-bchs-pack-down-is-pack
  (implies (and (natp i) (natp j) (<= i j) (posp acc))
           (equal (fn-bchs-pack-down i j acc fn-octets)
                  (+ (fn-bch-pack (fn-bchs-slice i j fn-octets))
                     (* (fn-bch-pow (- j i)) (- acc 1)))))
  :hints (("Goal" :induct (fn-bchs-pack-down i j acc fn-octets)
                  :in-theory (disable fn-bchs-slice fn-bch-pack fn-bch-byte
                                      fn-bch-pack-of-append fn-bch-pow-of-plus
                                      fn-bch-pow-of-1+))
          ("Subgoal *1/1" :use ((:instance fn-bchs-slice-snoc)
                                (:instance fn-bch-pack-of-append
                                           (xs (fn-bchs-slice i (- j 1) fn-octets))
                                           (ys (list (fn-octets-get (- j 1) fn-octets))))
                                (:instance fn-bch-pow-of-1+ (k (- j (+ 1 i)))))
                          :nonlinearp t)))

(defthm fn-bchs-pack-down-natp
  (natp (fn-bchs-pack-down i j acc fn-octets))
  :rule-classes :type-prescription)

(defun fn-bchs-mid (i k)
  (declare (xargs :guard (and (natp i) (natp k) (<= i k))))
  (+ i (nfix (floor (- k i) 2))))

(defthm fn-bchs-mid-natp
  (implies (and (natp i) (natp k))
           (natp (fn-bchs-mid i k)))
  :rule-classes :type-prescription)

(defthm fn-bchs-mid-bounds
  (implies (and (natp i) (natp k) (< (+ 1 i) k))
           (and (< i (fn-bchs-mid i k))
                (< (fn-bchs-mid i k) k)))
  :rule-classes :linear)

(in-theory (disable fn-bchs-mid))

; By halves: depth log2 of the span; each level one shift and one addition.
(defun fn-bchs-pack-span (i k fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp k) (<= i k)
                              (<= k (fn-octets-len fn-octets)))
                  :measure (nfix (- k i))
                  :verify-guards nil))
  (if (or (not (natp i)) (not (natp k)) (<= (- k i) 7))
      (fn-bchs-pack-down i k 1 fn-octets)
    (let ((m (fn-bchs-mid i k)))
      (+ (fn-bchs-pack-span i m fn-octets)
         (fn-bch-shift (- (fn-bchs-pack-span m k fn-octets) 1) (- m i))))))

(defthm fn-bchs-pack-span-is-pack
  (implies (and (natp i) (natp k) (<= i k))
           (equal (fn-bchs-pack-span i k fn-octets)
                  (fn-bch-pack (fn-bchs-slice i k fn-octets))))
  :hints (("Goal" :induct (fn-bchs-pack-span i k fn-octets)
                  :in-theory (disable fn-bchs-slice fn-bch-pack fn-bch-pack-of-append))
          ("Subgoal *1/2" :use ((:instance fn-bchs-slice-split (j (fn-bchs-mid i k)))
                                (:instance fn-bch-pack-of-append
                                           (xs (fn-bchs-slice i (fn-bchs-mid i k) fn-octets))
                                           (ys (fn-bchs-slice (fn-bchs-mid i k) k fn-octets)))))))

(defthm fn-bchs-pack-span-posp
  (implies (and (natp i) (natp k) (<= i k))
           (posp (fn-bchs-pack-span i k fn-octets)))
  :rule-classes :type-prescription)

(verify-guards fn-bchs-pack-span)

; -----------------------------------------------------------------------------
; Appending the span [I, K) to the store S: fill the tail, then whole blocks
; packed straight from the buffer, then the new tail.

(defun fn-bchs-push-span (s i k fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp k) (<= i k)
                              (<= k (fn-octets-len fn-octets)))
                  :measure (nfix (- k i))
                  :verify-guards nil))
  (cond ((not (and (natp i) (natp k) (< i k))) s)
        ((fn-bch-tail-okp s)
         (let* ((tl (fn-bch-tail-len s))
                (m (min k (+ i (- *fn-bch-block* tl))))
                (tail (+ (fn-bch-tail s)
                         (fn-bch-shift (- (fn-bchs-pack-span i m fn-octets) 1) tl))))
           (if (< (+ tl (- m i)) *fn-bch-block*)
               (fn-bch-make (fn-bch-count s) (+ tl (- m i)) tail (fn-bch-blocks s))
             (fn-bchs-push-span (fn-bch-make (+ 1 (fn-bch-count s)) 0 1
                                             (cons tail (fn-bch-blocks s)))
                                m k fn-octets))))
        (t (fn-bchs-push-span (fn-bch-push s (fn-octets-get i fn-octets))
                              (+ 1 i) k fn-octets))))

(local
 (defthm fn-bchs-pack-of-tail-append
   (implies (fn-bch-tail-ok-logic s)
            (equal (fn-bch-pack (append (fn-bch-unpack (fn-bch-tail s)) ys))
                   (+ (fn-bch-tail s)
                      (* (fn-bch-pow (fn-bch-tail-len s)) (- (fn-bch-pack ys) 1)))))
   :hints (("Goal" :use ((:instance fn-bch-pack-of-append
                                    (xs (fn-bch-unpack (fn-bch-tail s)))))
                   :in-theory (disable fn-bch-pack-of-append)))))

(local
 (defthm fn-bchs-fast-step
   (implies (and (fn-bch-tail-okp s)
                 (natp i) (natp m) (natp k) (< i m) (<= m k)
                 (<= (+ (fn-bch-tail-len s) (- m i)) *fn-bch-block*))
            (equal (fn-bch-push-list s (fn-bchs-slice i m fn-octets))
                   (let ((tail (+ (fn-bch-tail s)
                                  (* (fn-bch-pow (fn-bch-tail-len s))
                                     (- (fn-bch-pack (fn-bchs-slice i m fn-octets)) 1)))))
                     (if (< (+ (fn-bch-tail-len s) (- m i)) *fn-bch-block*)
                         (fn-bch-make (fn-bch-count s) (+ (fn-bch-tail-len s) (- m i))
                                      tail (fn-bch-blocks s))
                       (fn-bch-make (+ 1 (fn-bch-count s)) 0 1
                                    (cons tail (fn-bch-blocks s)))))))
   :hints (("Goal" :use ((:instance fn-bch-push-list-fills-the-tail
                                    (xs (fn-bchs-slice i m fn-octets))))
                   :in-theory (disable fn-bch-push-list-fills-the-tail fn-bch-pack-of-append
                                       fn-bchs-slice fn-bch-push-list)))))

; KEYSTONE: the span append is the per-octet append of the span's octets,
; for every store.
(defthm fn-bchs-push-span-is-push-list
  (equal (fn-bchs-push-span s i k fn-octets)
         (fn-bch-push-list s (fn-bchs-slice i k fn-octets)))
  :hints (("Goal" :induct (fn-bchs-push-span s i k fn-octets)
                  :in-theory (disable fn-bchs-slice fn-bchs-fast-step))
          ("Subgoal *1/4" :expand ((fn-bchs-slice i k fn-octets)))
          ("Subgoal *1/3" :use ((:instance fn-bchs-slice-split
                                           (j (min k (+ i (- *fn-bch-block* (fn-bch-tail-len s))))))
                                (:instance fn-bchs-fast-step
                                           (m (min k (+ i (- *fn-bch-block* (fn-bch-tail-len s))))))))
          ("Subgoal *1/2" :use ((:instance fn-bchs-slice-split
                                           (j (min k (+ i (- *fn-bch-block* (fn-bch-tail-len s))))))
                                (:instance fn-bchs-fast-step
                                           (m (min k (+ i (- *fn-bch-block* (fn-bch-tail-len s))))))))))

(verify-guards fn-bchs-push-span)
