; fn prototype (lane proto-adt-2, 2026-09-27): the building blocks of the
; ADT snapshot byte format (books/proto/adt-bytes.lisp), each with its
; round-trip lemma.  NOT on a served path; no host calls it.
;
;   adt-le / adt-unle            one little-endian fixed-width natural
;   adt-le-list / adt-unle-list  a column of them
;   adt-transpose / adt-untranspose  rows of cells <-> columns of cells
;   adt-pad / adt-body / adt-starts  regions laid out on whole pages

(in-package "ACL2")
(include-book "adt-lib")
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

(local (in-theory (disable nth update-nth nthcdr take)))

(defconst *adt-page* 16384)        ; octets per page: 2048 LE u64 words
(defconst *adt-u64-limit* 18446744073709551616)

(local
 (defthm adt-nthcdr-len-append
   (equal (nthcdr (len x) (append x y)) y)
   :hints (("Goal" :in-theory (enable nthcdr) :induct (len x)))))

(local
 (defthm adt-take-len-append
   (implies (true-listp x) (equal (take (len x) (append x y)) x))
   :hints (("Goal" :in-theory (enable take) :induct (len x)))))

(defthm adt-nthcdr-of-append-len
  (implies (equal n (len x))
           (equal (nthcdr n (append x y)) y)))

(defthm adt-take-of-append-len
  (implies (and (equal n (len x)) (true-listp x))
           (equal (take n (append x y)) x)))

(defthm adt-nthcdr-of-append-more
  (implies (and (natp n) (<= (len x) n))
           (equal (nthcdr n (append x y)) (nthcdr (- n (len x)) y)))
  :hints (("Goal" :in-theory (enable nthcdr) :induct (nthcdr n x))))

(defthm adt-take-of-append-less
  (implies (and (natp n) (<= n (len x)))
           (equal (take n (append x y)) (take n x)))
  :hints (("Goal" :in-theory (enable take) :induct (take n x))))

(defthm adt-nthcdr-of-append-less
  (implies (and (natp n) (<= n (len x)))
           (equal (nthcdr n (append x y)) (append (nthcdr n x) y)))
  :hints (("Goal" :in-theory (enable nthcdr) :induct (nthcdr n x))))

; -----------------------------------------------------------------------------
; A. One natural, W octets, least significant first.

(defun adt-le (w x)
  (declare (xargs :guard (and (natp w) (natp x))))
  (if (zp w)
      nil
    (cons (mod (nfix x) 256) (adt-le (1- w) (floor (nfix x) 256)))))

(defun adt-unle (w b)
  (declare (xargs :guard (and (natp w) (true-listp b))))
  (if (zp w)
      0
    (+ (nfix (car b)) (* 256 (adt-unle (1- w) (cdr b))))))

(defthm adt-len-le
  (equal (len (adt-le w x)) (nfix w)))

(defthm adt-true-listp-le
  (true-listp (adt-le w x))
  :rule-classes :type-prescription)

(defthm adt-octetsp-le
  (adt-octetsp (adt-le w x)))

(local
 (defthm adt-floor-256-bound
   (implies (and (natp x) (posp w) (< x (expt 2 (* 8 w))))
            (< (floor x 256) (expt 2 (* 8 (1- w)))))
   :hints (("Goal" :in-theory (enable expt)
            :use ((:instance floor-bounded-by-/ (x x) (y 256)))))))

(defthm adt-unle-le
  (implies (and (natp x) (natp w) (< x (expt 2 (* 8 w))))
           (equal (adt-unle w (append (adt-le w x) rest)) x))
  :hints (("Goal" :induct (adt-le w x) :in-theory (enable expt))))

(defthm adt-natp-unle
  (natp (adt-unle w b))
  :rule-classes :type-prescription)

; -----------------------------------------------------------------------------
; B. A column: N naturals, W octets each.

(defun adt-le-list (w xs)
  (declare (xargs :guard (and (natp w) (nat-listp xs))))
  (if (atom xs) nil (append (adt-le w (car xs)) (adt-le-list w (cdr xs)))))

(defun adt-unle-list (w n b)
  (declare (xargs :guard (and (natp w) (natp n) (true-listp b))))
  (if (zp n) nil (cons (adt-unle w b) (adt-unle-list w (1- n) (nthcdr w b)))))

(defun adt-all-below (xs lim)
  (declare (xargs :guard t))
  (if (atom xs) t (and (natp (car xs)) (< (car xs) (nfix lim)) (adt-all-below (cdr xs) lim))))

(defthm adt-len-le-list
  (equal (len (adt-le-list w xs)) (* (nfix w) (len xs))))

(defthm adt-octetsp-le-list
  (adt-octetsp (adt-le-list w xs)))

(defthm adt-true-listp-le-list
  (true-listp (adt-le-list w xs))
  :rule-classes :type-prescription)

(defthm adt-nthcdr-le-all
  (implies (natp w) (equal (nthcdr w (adt-le w x)) nil))
  :hints (("Goal" :in-theory (enable nthcdr))))

(local
 (defthm adt-append-assoc-local
   (equal (append (append a b) c) (append a (append b c)))))

(defthm adt-unle-list-le-list
  (implies (and (natp w) (adt-all-below xs (expt 2 (* 8 w))) (true-listp xs))
           (equal (adt-unle-list w (len xs) (append (adt-le-list w xs) rest)) xs))
  :hints (("Goal" :induct (adt-le-list w xs))))

; -----------------------------------------------------------------------------
; C. Transposition: rows of M cells <-> M columns.

(defun adt-transpose (m rows)
  (declare (xargs :verify-guards nil))
  (if (zp m) nil (cons (adt-cars rows) (adt-transpose (1- m) (adt-cdrs rows)))))

(defun adt-heads (cols)
  (declare (xargs :verify-guards nil))
  (if (atom cols) nil (cons (car (car cols)) (adt-heads (cdr cols)))))

(defun adt-tails (cols)
  (declare (xargs :verify-guards nil))
  (if (atom cols) nil (cons (cdr (car cols)) (adt-tails (cdr cols)))))

(defun adt-untranspose (n cols)
  (declare (xargs :verify-guards nil))
  (if (zp n) nil (cons (adt-heads cols) (adt-untranspose (1- n) (adt-tails cols)))))

(defun adt-rows-of-len (m rows)
  (declare (xargs :guard t))
  (if (atom rows) (null rows)
    (and (true-listp (car rows)) (equal (len (car rows)) (nfix m))
         (adt-rows-of-len m (cdr rows)))))

(local
 (defun adt-tr-induct (m rows)
   (if (zp m) (list m rows) (adt-tr-induct (1- m) (adt-cdrs rows)))))

(defthm adt-rows-of-len-cdrs
  (implies (and (adt-rows-of-len m rows) (posp m))
           (adt-rows-of-len (1- m) (adt-cdrs rows))))

(defthm adt-heads-transpose
  (implies (and (consp rows) (adt-rows-of-len m rows))
           (equal (adt-heads (adt-transpose m rows)) (car rows)))
  :hints (("Goal" :induct (adt-tr-induct m rows))))

(defthm adt-tails-transpose
  (equal (adt-tails (adt-transpose m rows)) (adt-transpose m (cdr rows)))
  :hints (("Goal" :induct (adt-tr-induct m rows))))

(defthm adt-untranspose-transpose
  (implies (and (adt-rows-of-len m rows) (equal n (len rows)))
           (equal (adt-untranspose n (adt-transpose m rows)) rows)))

(defthm adt-len-transpose
  (equal (len (adt-transpose m rows)) (nfix m)))

(defthm adt-true-listp-transpose
  (true-listp (adt-transpose m rows))
  :rule-classes :type-prescription)

(local
 (defun adt-rm-induct (r m rows)
   (if (or (zp r) (zp m)) (list r m rows) (adt-rm-induct (1- r) (1- m) (adt-cdrs rows)))))

(defthm adt-len-cars-of-transpose
  (implies (and (natp r) (< r (nfix m)))
           (equal (len (nth r (adt-transpose m rows))) (len rows)))
  :hints (("Goal" :in-theory (enable nth) :induct (adt-rm-induct r m rows)
           :expand ((adt-transpose m rows)))))

; -----------------------------------------------------------------------------
; D. Regions on pages.  A region of U octets takes (adt-cap U) pages: none
; when empty, else the least power of two at least ceiling(U / page), so a
; region's pages move only when its size doubles (an append dirties the
; tail pages of each region, not every page after it).

(defun adt-pow2-at-least (k acc)
  (declare (xargs :guard (and (natp k) (posp acc))
                  :measure (nfix (- (nfix k) (nfix acc)))))
  (if (or (not (posp acc)) (<= (nfix k) acc)) (max 1 (nfix acc)) (adt-pow2-at-least k (* 2 acc))))

(defun adt-cap (u)
  (declare (xargs :guard (natp u)))
  (if (zp u) 0 (adt-pow2-at-least (ceiling u *adt-page*) 1)))

(defthm adt-pow2-at-least-bound
  (implies (and (natp k) (posp acc)) (<= k (adt-pow2-at-least k acc)))
  :rule-classes :linear)

(defthm adt-natp-pow2-at-least
  (posp (adt-pow2-at-least k acc))
  :rule-classes :type-prescription)

(defthm adt-cap-covers
  (implies (natp u) (<= u (* *adt-page* (adt-cap u))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance adt-pow2-at-least-bound (k (ceiling u *adt-page*)) (acc 1))))))

(defthm adt-natp-cap
  (natp (adt-cap u))
  :rule-classes :type-prescription)

(defun adt-zeros (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons 0 (adt-zeros (1- n)))))

(defthm adt-len-zeros (equal (len (adt-zeros n)) (nfix n)))

(defthm adt-octetsp-zeros (adt-octetsp (adt-zeros n)))

; A region padded to its pages.
(defun adt-pad (b)
  (declare (xargs :guard (true-listp b)))
  (append b (adt-zeros (- (* *adt-page* (adt-cap (len b))) (len b)))))

(defthm adt-len-pad
  (equal (len (adt-pad b)) (* *adt-page* (adt-cap (len b)))))

(defthm adt-octetsp-pad
  (implies (adt-octetsp b) (adt-octetsp (adt-pad b))))

(defthm adt-octetsp-append
  (implies (and (adt-octetsp x) (adt-octetsp y)) (adt-octetsp (append x y))))

(defun adt-all-octetsp (regs)
  (declare (xargs :guard t))
  (if (atom regs) t (and (adt-octetsp (car regs)) (adt-all-octetsp (cdr regs)))))

(defun adt-body (regs)
  (declare (xargs :guard (true-list-listp regs)))
  (if (atom regs) nil (append (adt-pad (car regs)) (adt-body (cdr regs)))))

(defthm adt-true-listp-body
  (true-listp (adt-body regs))
  :rule-classes :type-prescription)

(defthm adt-octetsp-body
  (implies (adt-all-octetsp regs) (adt-octetsp (adt-body regs)))
  :hints (("Goal" :in-theory (enable adt-all-octetsp))))

; Page index of each region's first page, from START.
(defun adt-starts (regs start)
  (declare (xargs :guard (and (true-list-listp regs) (natp start))))
  (if (atom regs) nil
    (cons (nfix start) (adt-starts (cdr regs) (+ (nfix start) (adt-cap (len (car regs))))))))

(defun adt-lens (regs)
  (declare (xargs :guard (true-list-listp regs)))
  (if (atom regs) nil (cons (len (car regs)) (adt-lens (cdr regs)))))

(defun adt-end (regs start)
  (declare (xargs :guard (and (true-list-listp regs) (natp start))))
  (if (atom regs) (nfix start) (adt-end (cdr regs) (+ (nfix start) (adt-cap (len (car regs)))))))

(defthm adt-len-body
  (implies (natp start)
           (equal (+ (* *adt-page* start) (len (adt-body regs)))
                  (* *adt-page* (adt-end regs start)))))

(defthm adt-starts-facts
  (implies (natp start)
           (and (implies (consp regs) (equal (nth 0 (adt-starts regs start)) start))
                (implies (and (posp r) (consp regs))
                         (equal (nth r (adt-starts regs start))
                                (nth (1- r) (adt-starts (cdr regs) (+ start (adt-cap (len (car regs))))))))))
  :hints (("Goal" :in-theory (enable nth))))

(local
 (defun adt-region-induct (r regs start)
   (if (or (zp r) (atom regs))
       (list r regs start)
     (adt-region-induct (1- r) (cdr regs) (+ (nfix start) (adt-cap (len (car regs))))))))

(defthm adt-starts-lower-bound
  (implies (and (natp start) (natp r) (< r (len regs)))
           (<= start (nth r (adt-starts regs start))))
  :rule-classes :linear
  :hints (("Goal" :induct (adt-region-induct r regs start) :in-theory (disable adt-starts))))

(defthm adt-car-starts
  (implies (consp regs) (equal (car (adt-starts regs start)) (nfix start))))

(defthm adt-cdr-starts
  (implies (consp regs)
           (equal (cdr (adt-starts regs start))
                  (adt-starts (cdr regs) (+ (nfix start) (adt-cap (len (car regs))))))))

(local
 (defthm adt-nth-posp-open
   (implies (posp r) (equal (nth r x) (nth (1- r) (cdr x))))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defun adt-region-induct2 (r regs start prefix)
   (if (or (zp r) (atom regs))
       (list r regs start prefix)
     (adt-region-induct2 (1- r) (cdr regs) (+ (nfix start) (adt-cap (len (car regs))))
                         (append prefix (adt-pad (car regs)))))))

(local
 (defthm adt-append-assoc-local2
   (equal (append (append a b) c) (append a (append b c)))))

(defthm adt-take-len-self
  (implies (true-listp x) (equal (take (len x) x) x))
  :hints (("Goal" :in-theory (enable take))))

(defthm adt-nthcdr-len-self
  (implies (true-listp x) (equal (nthcdr (len x) x) nil))
  :hints (("Goal" :in-theory (enable nthcdr))))

(local
 (defthm adt-nth-0-local
   (equal (nth 0 x) (car x))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm adt-region-base
   (implies (true-listp reg)
            (equal (take (len reg) (append (adt-pad reg) rest)) reg))
   :hints (("Goal" :in-theory (enable adt-pad)))))

; Region R is at page (nth r starts) of any image whose body follows a
; prefix of START pages.
(defthm adt-region-of-image
  (implies (and (natp r) (< r (len regs)) (natp start) (true-list-listp regs)
                (true-listp prefix) (equal (len prefix) (* *adt-page* start)))
           (equal (take (len (nth r regs))
                        (nthcdr (* *adt-page* (nth r (adt-starts regs start)))
                                (append prefix (adt-body regs))))
                  (nth r regs)))
  :hints (("Goal" :induct (adt-region-induct2 r regs start prefix)
           :in-theory (disable adt-pad adt-starts)
           :expand ((adt-body regs)))))
