; POST prepare context, version 2: encoding, prefix decoding, and the
; approved Section C round-trip and resource bounds.
(in-package "ACL2")
(include-book "post-acceptance-bound")
(include-book "cbor")
(set-verify-guards-eagerness 1)

; Keep the packet's predicate byte-identical without including the machine.
(defconst *fn-pctx-sufhead-max* 9)
(defconst *fn-ptx-sufhead-max* *fn-pctx-sufhead-max*)
(defconst *fn-pctx-max*
  (+ 1 8 (* 4 6) (* 3 (fn-adm-acc-out-max)) *fn-pctx-sufhead-max*))

(defun fn-pctx-p (ctx)
  (and (true-listp ctx) (equal (len ctx) 7)
       (natp (nth 0 ctx)) (< (nth 0 ctx) (expt 2 64))
       (fn-cbor-octet-listp (nth 1 ctx)) (<= (len (nth 1 ctx)) (fn-adm-acc-out-max))
       (fn-cbor-octet-listp (nth 2 ctx)) (<= (len (nth 2 ctx)) (fn-adm-acc-out-max))
       (natp (nth 3 ctx)) (< (nth 3 ctx) (expt 2 32))
       (fn-cbor-octet-listp (nth 4 ctx)) (<= (len (nth 4 ctx)) *fn-ptx-sufhead-max*)
       (fn-cbor-octet-listp (nth 5 ctx)) (<= (len (nth 5 ctx)) (fn-adm-acc-out-max))
       (natp (nth 6 ctx)) (< (nth 6 ctx) (expt 2 32))))
(verify-guards fn-pctx-p)

; Total access and concatenation also accept dotted lists and atoms.
(defun fn-pctx-get (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (if (consp x)
      (if (zp (nfix n)) (car x) (fn-pctx-get (1- (nfix n)) (cdr x)))
    nil))

(defun fn-pctx-cat (x y)
  (declare (xargs :guard t))
  (if (consp x) (cons (car x) (fn-pctx-cat (cdr x) y)) y))

(defun fn-pctx-octets (x)
  (declare (xargs :guard t))
  (if (fn-cbor-octet-listp x) x nil))

; Fixed-width unsigned integers: nfix followed by low-width projection.
(defun fn-pctx-uint-be (n width)
  (declare (xargs :guard t :measure (nfix width)))
  (if (zp (nfix width))
      nil
    (cons (logand 255 (ash (nfix n) (- (* 8 (1- (nfix width))))))
          (fn-pctx-uint-be n (1- (nfix width))))))

(defun fn-pctx-encode-field (x)
  (declare (xargs :guard t))
  (let ((octets (fn-pctx-octets x)))
    (fn-pctx-cat (fn-pctx-uint-be (len octets) 4) octets)))

(defun fn-pctx-encode (ctx)
  (declare (xargs :guard t))
  (cons 2
        (fn-pctx-cat
         (fn-pctx-uint-be (fn-pctx-get 0 ctx) 8)
         (fn-pctx-cat
          (fn-pctx-encode-field (fn-pctx-get 1 ctx))
          (fn-pctx-cat
           (fn-pctx-encode-field (fn-pctx-get 2 ctx))
           (fn-pctx-cat
            (fn-pctx-uint-be (fn-pctx-get 3 ctx) 4)
            (fn-pctx-cat
             (fn-pctx-encode-field (fn-pctx-get 4 ctx))
             (fn-pctx-cat (fn-pctx-encode-field (fn-pctx-get 5 ctx))
                          (fn-pctx-uint-be (fn-pctx-get 6 ctx) 4)))))))))

; Read exactly n octets, leaving the suffix untouched, even when it is
; not an octet list.  No length scan of the suffix is needed.
(defun fn-pctx-read-octets (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (cond ((zp (nfix n)) (list t nil x))
        ((and (consp x) (fn-cbor-octetp (car x)))
         (let ((d (fn-pctx-read-octets (1- (nfix n)) (cdr x))))
           (if (fn-pctx-get 0 d)
               (list t (cons (car x) (fn-pctx-get 1 d)) (fn-pctx-get 2 d))
             (list nil nil nil))))
        (t (list nil nil nil))))

(defun fn-pctx-octets-uint (x acc)
  (declare (xargs :guard t))
  (if (consp x)
      (fn-pctx-octets-uint (cdr x) (+ (* 256 (nfix acc)) (nfix (car x))))
    (nfix acc)))

(defun fn-pctx-read-uint (width x)
  (declare (xargs :guard t))
  (let ((d (fn-pctx-read-octets width x)))
    (if (fn-pctx-get 0 d)
        (list t (fn-pctx-octets-uint (fn-pctx-get 1 d) 0) (fn-pctx-get 2 d))
      (list nil nil nil))))

; Refuse an excessive advertised length before consuming or allocating
; its field.  A short field or a non-octet in the consumed prefix fails.
(defun fn-pctx-read-field (x bound)
  (declare (xargs :guard t))
  (let* ((d (fn-pctx-read-uint 4 x))
         (n (nfix (fn-pctx-get 1 d))))
    (if (and (fn-pctx-get 0 d) (<= n (nfix bound)))
        (fn-pctx-read-octets n (fn-pctx-get 2 d))
      (list nil nil nil))))

(defun fn-pctx-decode (x)
  (declare (xargs :guard t))
  (if (and (consp x) (equal (car x) 2))
      (let* ((tx (fn-pctx-read-uint 8 (cdr x)))
             (pre (fn-pctx-read-field (fn-pctx-get 2 tx) (fn-adm-acc-out-max)))
             (ins (fn-pctx-read-field (fn-pctx-get 2 pre) (fn-adm-acc-out-max)))
             (ioff (fn-pctx-read-uint 4 (fn-pctx-get 2 ins)))
             (sh (fn-pctx-read-field (fn-pctx-get 2 ioff) *fn-pctx-sufhead-max*))
             (st (fn-pctx-read-field (fn-pctx-get 2 sh) (fn-adm-acc-out-max)))
             (gl (fn-pctx-read-uint 4 (fn-pctx-get 2 st)))
             (ctx (list (fn-pctx-get 1 tx) (fn-pctx-get 1 pre) (fn-pctx-get 1 ins)
                        (fn-pctx-get 1 ioff) (fn-pctx-get 1 sh) (fn-pctx-get 1 st) (fn-pctx-get 1 gl))))
        (if (and (fn-pctx-get 0 tx) (fn-pctx-get 0 pre) (fn-pctx-get 0 ins)
                 (fn-pctx-get 0 ioff) (fn-pctx-get 0 sh) (fn-pctx-get 0 st) (fn-pctx-get 0 gl)
                 (fn-pctx-p ctx))
            (list t ctx (+ 1 8 (* 4 6) (len (fn-pctx-get 1 pre))
                           (len (fn-pctx-get 1 ins)) (len (fn-pctx-get 1 sh))
                           (len (fn-pctx-get 1 st))))
          (list nil nil 0)))
    (list nil nil 0)))

; Section C proofs: structural consumption, scalar reconstruction, composition.
(local (include-book "ihs/logops-lemmas" :dir :system))

(local (defthm pctx-get-is-nth
  (implies (natp n) (equal (fn-pctx-get n x) (nth n x)))
  :hints (("Goal" :induct (fn-pctx-get n x) :in-theory (enable fn-pctx-get nth)))))

(local (defthm pctx-cat-is-append
  (equal (fn-pctx-cat x y) (append x y))
  :hints (("Goal" :induct (fn-pctx-cat x y) :in-theory (enable fn-pctx-cat)))))

(local (defthm pctx-uint-length
  (equal (len (fn-pctx-uint-be n width)) (nfix width))
  :hints (("Goal" :induct (fn-pctx-uint-be n width)
                  :in-theory (e/d (fn-pctx-uint-be) (ash logand))))))

(local (defthm pctx-encode-length
  (implies (fn-pctx-p ctx)
           (equal (len (fn-pctx-encode ctx))
                  (+ 33 (len (nth 1 ctx)) (len (nth 2 ctx))
                        (len (nth 4 ctx)) (len (nth 5 ctx)))))
  :hints (("Goal" :in-theory
           (e/d (fn-pctx-p fn-pctx-encode fn-pctx-encode-field fn-pctx-octets)
                (fn-pctx-uint-be fn-pctx-cat fn-pctx-get))))))

(local (defthm pctx-encode-bounded-proof
  (implies (fn-pctx-p ctx) (<= (len (fn-pctx-encode ctx)) *fn-pctx-max*))
  :hints (("Goal" :in-theory
           (e/d (fn-pctx-p) (fn-pctx-encode fn-pctx-encode-field fn-pctx-uint-be))))))

(local (defthm pctx-read-octets-shape
  (let ((d (fn-pctx-read-octets n x)))
    (implies (car d)
             (and (fn-cbor-octet-listp (cadr d))
                  (equal (len (cadr d)) (nfix n))
                  (equal (len x) (+ (nfix n) (len (caddr d)))))))
  :hints (("Goal" :induct (fn-pctx-read-octets n x)
                  :in-theory (enable fn-pctx-read-octets fn-cbor-octet-listp)))))

(local (defthm pctx-read-octets-round-trip
  (implies (fn-cbor-octet-listp xs)
           (equal (fn-pctx-read-octets (len xs) (append xs rest))
                  (list t xs rest)))
  :hints (("Goal" :induct (fn-pctx-cat xs rest)
                  :in-theory (enable fn-pctx-read-octets fn-cbor-octet-listp)))))

(local (defthm pctx-read-uint-length
  (implies (car (fn-pctx-read-uint width x))
           (equal (len x) (+ (nfix width) (len (caddr (fn-pctx-read-uint width x))))))
  :hints (("Goal" :in-theory (e/d (fn-pctx-read-uint) (fn-pctx-read-octets))
                  :use ((:instance pctx-read-octets-shape (n width)))))))

(local (defthm pctx-read-field-length
  (let ((d (fn-pctx-read-field x bound)))
    (implies (car d)
             (equal (len x) (+ 4 (len (cadr d)) (len (caddr d))))))
  :hints (("Goal" :in-theory (e/d (fn-pctx-read-field)
                                 (fn-pctx-read-uint fn-pctx-read-octets))
                  :use ((:instance pctx-read-uint-length (width 4))
                        (:instance pctx-read-octets-shape
                         (n (nfix (cadr (fn-pctx-read-uint 4 x))))
                         (x (caddr (fn-pctx-read-uint 4 x)))))))))

(local (defthm pctx-get-0
  (equal (fn-pctx-get 0 x) (car x))
  :hints (("Goal" :in-theory (e/d (fn-pctx-get) (pctx-get-is-nth))))))

(local (defthm pctx-get-1
  (equal (fn-pctx-get 1 x) (cadr x))
  :hints (("Goal" :in-theory (e/d (fn-pctx-get) (pctx-get-is-nth))))))

(local (defthm pctx-get-2
  (equal (fn-pctx-get 2 x) (caddr x))
  :hints (("Goal" :in-theory (e/d (fn-pctx-get) (pctx-get-is-nth))))))

(local (defthm pctx-spans-bounded
  (implies (fn-pctx-p (list tx pre ins ioff sh st glen))
           (<= (+ 33 (len pre) (len ins) (len sh) (len st)) *fn-pctx-max*))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-pctx-p)))))

(local (defthm pctx-decode-shape-proof
  (let ((d (fn-pctx-decode x)))
    (implies (car d)
             (and (fn-pctx-p (cadr d)) (natp (caddr d))
                  (<= (caddr d) (len x)) (<= (caddr d) *fn-pctx-max*))))
 :hints (("Goal" :in-theory (e/d (fn-pctx-decode) (fn-pctx-p fn-pctx-get fn-pctx-read-uint fn-pctx-read-field fn-pctx-read-octets pctx-read-uint-length pctx-read-field-length))
 :use ((:instance pctx-read-uint-length (width 8) (x (cdr x)))
(:instance pctx-read-field-length (x (caddr (fn-pctx-read-uint 8 (cdr x)))) (bound (fn-adm-acc-out-max)))
(:instance pctx-read-field-length (x (caddr (fn-pctx-read-field (caddr (fn-pctx-read-uint 8 (cdr x))) (fn-adm-acc-out-max)))) (bound (fn-adm-acc-out-max)))
(:instance pctx-read-uint-length (x (caddr (fn-pctx-read-field (caddr (fn-pctx-read-field (caddr (fn-pctx-read-uint 8 (cdr x))) (fn-adm-acc-out-max))) (fn-adm-acc-out-max)))) (width 4))
(:instance pctx-read-field-length (x (caddr (fn-pctx-read-uint 4 (caddr (fn-pctx-read-field (caddr (fn-pctx-read-field (caddr (fn-pctx-read-uint 8 (cdr x))) (fn-adm-acc-out-max))) (fn-adm-acc-out-max)))))) (bound *fn-pctx-sufhead-max*))
(:instance pctx-read-field-length (x (caddr (fn-pctx-read-field (caddr (fn-pctx-read-uint 4 (caddr (fn-pctx-read-field (caddr (fn-pctx-read-field (caddr (fn-pctx-read-uint 8 (cdr x))) (fn-adm-acc-out-max))) (fn-adm-acc-out-max))))) *fn-pctx-sufhead-max*))) (bound (fn-adm-acc-out-max)))
(:instance pctx-read-uint-length (width 4) (x (caddr (fn-pctx-read-field (caddr (fn-pctx-read-field (caddr (fn-pctx-read-uint 4 (caddr (fn-pctx-read-field (caddr (fn-pctx-read-field (caddr (fn-pctx-read-uint 8 (cdr x))) (fn-adm-acc-out-max))) (fn-adm-acc-out-max))))) *fn-pctx-sufhead-max*)) (fn-adm-acc-out-max))))))))))

(local (defthm pctx-encode-field-length
  (implies (fn-cbor-octet-listp x)
           (equal (len (fn-pctx-encode-field x)) (+ 4 (len x))))
  :hints (("Goal" :in-theory
           (e/d (fn-pctx-encode-field fn-pctx-octets)
                (fn-pctx-uint-be fn-pctx-cat))))))


; Arithmetic is scoped to the two fixed-width reconstruction proofs.
(local (encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
(defthm pctx-ash-is-logtail
  (implies (and (natp n) (natp k))
           (equal (ash n (- k)) (logtail k n)))
  :hints (("Goal" :in-theory (e/d (ash logtail expt2) (fn-bch-ash-right-is-floor-pow)))))

(defthm pctx-byte-is-loghead
  (implies (and (natp n) (natp k))
           (equal (logand 255 (ash n (- (* 8 k))))
                  (loghead 8 (logtail (* 8 k) n))))
  :hints (("Goal" :in-theory (disable ash loghead logtail logand binary-logand
                                    ash-to-floor fn-bch-ash-right-is-floor-pow logand-constant-mask)
                  :use ((:instance pctx-ash-is-logtail (k (* 8 k)))
                        (:instance logand-with-mask (mask 255) (size 8)
                                   (i (ash n (- (* 8 k)))))))))

(defthm pctx-loghead-split
  (implies (and (natp n) (natp k))
           (equal (+ (loghead (* 8 k) n)
                     (* (expt 2 (* 8 k)) (loghead 8 (logtail (* 8 k) n))))
                  (loghead (* 8 (+ 1 k)) n)))
  :hints (("Goal" :in-theory (e/d (logapp expt2)
                                 (loghead logtail loghead-logapp-loghead-logtail))
                  :use ((:instance loghead-logapp-loghead-logtail
                                   (size (* 8 k)) (size1 8) (i n))))))

(defthm pctx-uint-4-reconstruction
  (implies (and (natp n) (< n (expt 2 32)))
           (equal (fn-pctx-octets-uint (fn-pctx-uint-be n 4) 0) n))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
             '(fn-pctx-octets-uint fn-pctx-uint-be nfix natp
               unsigned-byte-p integer-range-p logtail-0-i ash-0
               loghead-identity loghead-loghead
               (:type-prescription loghead-type) (:type-prescription logtail-type)
               (:type-prescription nfix) car-cons cdr-cons
               (:executable-counterpart consp)
               (:executable-counterpart zp) (:executable-counterpart expt)
               normalize-addends normalize-factors-gather-exponents
               simplify-sums-equal
               |(* (* x y) z)| |(* x (+ y z))| |(* y (* x z))| |(* y x)|
               |(* 0 x)| |(* 1 x)| |(* c (* d x))|
               |(+ (+ x y) z)| |(+ 0 x)| |(+ y (+ x z))| |(+ y x)|
               |(+ c (+ d x))| |(+ x (- x))|))
           :expand ((fn-pctx-uint-be n 0)
                    (fn-pctx-uint-be n 1)
                    (fn-pctx-uint-be n 2)
                    (fn-pctx-uint-be n 3)
                    (fn-pctx-uint-be n 4)
                    (:free (acc) (fn-pctx-octets-uint (list (loghead 8 (logtail 24 n)) (loghead 8 (logtail 16 n)) (loghead 8 (logtail 8 n)) (loghead 8 n)) acc))
                    (:free (acc) (fn-pctx-octets-uint (list (loghead 8 (logtail 16 n)) (loghead 8 (logtail 8 n)) (loghead 8 n)) acc))
                    (:free (acc) (fn-pctx-octets-uint (list (loghead 8 (logtail 8 n)) (loghead 8 n)) acc))
                    (:free (acc) (fn-pctx-octets-uint (list (loghead 8 n)) acc))
                    (:free (acc) (fn-pctx-octets-uint nil acc)))
           :use ((:instance pctx-byte-is-loghead (k 0))
                 (:instance pctx-byte-is-loghead (k 1))
                 (:instance pctx-byte-is-loghead (k 2))
                 (:instance pctx-byte-is-loghead (k 3))
                 (:instance pctx-loghead-split (k 1))
                 (:instance pctx-loghead-split (k 2))
                 (:instance pctx-loghead-split (k 3))
                 (:instance loghead-identity (size 32) (i n))))))

(defthm pctx-uint-8-reconstruction
  (implies (and (natp n) (< n (expt 2 64)))
           (equal (fn-pctx-octets-uint (fn-pctx-uint-be n 8) 0) n))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
             '(fn-pctx-octets-uint fn-pctx-uint-be nfix natp
               unsigned-byte-p integer-range-p logtail-0-i ash-0
               loghead-identity loghead-loghead
               (:type-prescription loghead-type) (:type-prescription logtail-type)
               (:type-prescription nfix) car-cons cdr-cons
               (:executable-counterpart consp)
               (:executable-counterpart zp) (:executable-counterpart expt)
               normalize-addends normalize-factors-gather-exponents
               simplify-sums-equal
               |(* (* x y) z)| |(* x (+ y z))| |(* y (* x z))| |(* y x)|
               |(* 0 x)| |(* 1 x)| |(* c (* d x))|
               |(+ (+ x y) z)| |(+ 0 x)| |(+ y (+ x z))| |(+ y x)|
               |(+ c (+ d x))| |(+ x (- x))|))
           :expand ((fn-pctx-uint-be n 0) (fn-pctx-uint-be n 1) (fn-pctx-uint-be n 2) (fn-pctx-uint-be n 3) (fn-pctx-uint-be n 4) (fn-pctx-uint-be n 5) (fn-pctx-uint-be n 6) (fn-pctx-uint-be n 7) (fn-pctx-uint-be n 8)
                (:free (acc) (fn-pctx-octets-uint (list (loghead 8 (logtail 56 n)) (loghead 8 (logtail 48 n)) (loghead 8 (logtail 40 n)) (loghead 8 (logtail 32 n)) (loghead 8 (logtail 24 n)) (loghead 8 (logtail 16 n)) (loghead 8 (logtail 8 n)) (loghead 8 n)) acc))
                (:free (acc) (fn-pctx-octets-uint (list (loghead 8 (logtail 48 n)) (loghead 8 (logtail 40 n)) (loghead 8 (logtail 32 n)) (loghead 8 (logtail 24 n)) (loghead 8 (logtail 16 n)) (loghead 8 (logtail 8 n)) (loghead 8 n)) acc))
                (:free (acc) (fn-pctx-octets-uint (list (loghead 8 (logtail 40 n)) (loghead 8 (logtail 32 n)) (loghead 8 (logtail 24 n)) (loghead 8 (logtail 16 n)) (loghead 8 (logtail 8 n)) (loghead 8 n)) acc))
                (:free (acc) (fn-pctx-octets-uint (list (loghead 8 (logtail 32 n)) (loghead 8 (logtail 24 n)) (loghead 8 (logtail 16 n)) (loghead 8 (logtail 8 n)) (loghead 8 n)) acc))
                (:free (acc) (fn-pctx-octets-uint (list (loghead 8 (logtail 24 n)) (loghead 8 (logtail 16 n)) (loghead 8 (logtail 8 n)) (loghead 8 n)) acc))
                (:free (acc) (fn-pctx-octets-uint (list (loghead 8 (logtail 16 n)) (loghead 8 (logtail 8 n)) (loghead 8 n)) acc))
                (:free (acc) (fn-pctx-octets-uint (list (loghead 8 (logtail 8 n)) (loghead 8 n)) acc))
                (:free (acc) (fn-pctx-octets-uint (list (loghead 8 n)) acc))
                (:free (acc) (fn-pctx-octets-uint nil acc)))
           :use ((:instance pctx-byte-is-loghead (k 0)) (:instance pctx-byte-is-loghead (k 1)) (:instance pctx-byte-is-loghead (k 2)) (:instance pctx-byte-is-loghead (k 3)) (:instance pctx-byte-is-loghead (k 4)) (:instance pctx-byte-is-loghead (k 5)) (:instance pctx-byte-is-loghead (k 6)) (:instance pctx-byte-is-loghead (k 7)) (:instance pctx-loghead-split (k 1)) (:instance pctx-loghead-split (k 2)) (:instance pctx-loghead-split (k 3)) (:instance pctx-loghead-split (k 4)) (:instance pctx-loghead-split (k 5)) (:instance pctx-loghead-split (k 6)) (:instance pctx-loghead-split (k 7)) (:instance loghead-identity (size 64) (i n))))))
))

(local (defthm pctx-mask-octet
  (implies (integerp x) (fn-cbor-octetp (logand 255 x)))
  :hints (("Goal" :in-theory
           (e/d (fn-cbor-octetp unsigned-byte-p integer-range-p)
                (logand binary-logand logand-with-mask unsigned-byte-p-logand))
           :use ((:instance unsigned-byte-p-logand (size 8) (i 255) (j x)))))))

(local (defthm pctx-uint-octets
  (fn-cbor-octet-listp (fn-pctx-uint-be n width))
  :hints (("Goal" :induct (fn-pctx-uint-be n width)
                  :in-theory (e/d (fn-pctx-uint-be fn-cbor-octet-listp)
                                  (ash binary-logand fn-bch-ash-right-is-floor-pow
                                   logand logand-with-mask fn-cbor-octetp))))))

(local (defthm pctx-read-octets-prefix
  (implies (and (natp n) (fn-cbor-octet-listp xs) (equal n (len xs)))
           (equal (fn-pctx-read-octets n (append xs rest)) (list t xs rest)))
  :hints (("Goal" :in-theory (disable fn-pctx-read-octets)
                  :use (pctx-read-octets-round-trip)))))

(local (defthm pctx-read-uint-4-round-trip
  (implies (and (natp n) (< n (expt 2 32)))
           (equal (fn-pctx-read-uint 4 (append (fn-pctx-uint-be n 4) rest))
                  (list t n rest)))
  :hints (("Goal" :in-theory (e/d (fn-pctx-read-uint)
                                 (fn-pctx-read-octets fn-pctx-uint-be fn-pctx-octets-uint))))))

(local (defthm pctx-read-uint-8-round-trip
  (implies (and (natp n) (< n (expt 2 64)))
           (equal (fn-pctx-read-uint 8 (append (fn-pctx-uint-be n 8) rest))
                  (list t n rest)))
  :hints (("Goal" :in-theory (e/d (fn-pctx-read-uint)
                                 (fn-pctx-read-octets fn-pctx-uint-be fn-pctx-octets-uint))))))

(local (defthm pctx-append-associative
  (equal (append (append a b) c) (append a b c))
  :hints (("Goal" :induct (append a b) :in-theory (enable append)))))

(local (defthm pctx-read-field-round-trip
  (implies (and (fn-cbor-octet-listp xs) (< (len xs) (expt 2 32))
                (<= (len xs) (nfix bound)))
           (equal (fn-pctx-read-field (append (fn-pctx-encode-field xs) rest) bound)
                  (list t xs rest)))
  :hints (("Goal" :in-theory
           (e/d (fn-pctx-read-field fn-pctx-encode-field fn-pctx-octets)
                (fn-pctx-read-uint fn-pctx-uint-be fn-pctx-cat fn-pctx-read-octets
                 fn-cbor-octet-listp (:executable-counterpart fn-pctx-uint-be)))))))

(local (defthm pctx-seven-field-reconstruction
  (implies (and (true-listp ctx) (equal (len ctx) 7))
           (equal (list (nth 0 ctx) (nth 1 ctx) (nth 2 ctx)
                        (nth 3 ctx) (nth 4 ctx) (nth 5 ctx) (nth 6 ctx)) ctx))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable nth) :do-not-induct t
           :expand ((len ctx) (len (cdr ctx)) (len (cddr ctx))
                    (len (cdddr ctx)) (len (cddddr ctx))
                    (len (cdr (cddddr ctx))) (len (cddr (cddddr ctx))) (len (cdddr (cddddr ctx)))
                    (true-listp ctx) (true-listp (cdr ctx))
                    (true-listp (cddr ctx)) (true-listp (cdddr ctx))
                    (true-listp (cddddr ctx)) (true-listp (cdr (cddddr ctx)))
                    (true-listp (cddr (cddddr ctx))) (true-listp (cdddr (cddddr ctx))))))))

(local (defthm pctx-round-trip-proof
  (implies (fn-pctx-p ctx)
           (equal (fn-pctx-decode (append (fn-pctx-encode ctx) rest))
                  (list t ctx (len (fn-pctx-encode ctx)))))
  :hints (("Goal" :use (pctx-seven-field-reconstruction) :in-theory
           (e/d (fn-pctx-p fn-pctx-decode fn-pctx-encode nth)
                (fn-pctx-read-uint fn-pctx-read-field fn-pctx-read-octets
                 fn-pctx-uint-be fn-pctx-encode-field fn-pctx-cat fn-pctx-get
                 (:executable-counterpart fn-pctx-uint-be)
                 (:executable-counterpart fn-pctx-encode-field)))))))


; Approved statements, copied byte for byte from the packet.
(local (in-theory (disable fn-pctx-p fn-pctx-encode fn-pctx-decode pctx-encode-length)))
(defthm fn-pctx-round-trip
  (implies (fn-pctx-p ctx)
           (equal (fn-pctx-decode (append (fn-pctx-encode ctx) rest))
                  (list t ctx (len (fn-pctx-encode ctx))))))

(defthm fn-pctx-encode-bounded
  (implies (fn-pctx-p ctx) (<= (len (fn-pctx-encode ctx)) *fn-pctx-max*)))

(defthm fn-pctx-decode-shape
  (let ((d (fn-pctx-decode x)))
    (implies (car d)
             (and (fn-pctx-p (cadr d)) (natp (caddr d))
                  (<= (caddr d) (len x)) (<= (caddr d) *fn-pctx-max*)))))

(defthm fn-pctx-max-is-derived
  (equal *fn-pctx-max* 10359) :rule-classes nil)
