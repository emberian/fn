; fn: an article body held as fixed-size packed blocks (lane chunked-body,
; row B6 of COMPLETE-BEFORE-6.6.0, 2026-09-28; D27; D35 F8).
;
; While a connection is in article mode the wire retains what it has read of
; the body until the terminator.  As octet lists that is sixteen octets of
; heap per octet (a cons each) -- the term that made the article credit
; (books/heap-store-figure.lisp fn-heap-article-reserve-octets) 32 times the
; article.  This book is the compact form: the octets as a list of FULL
; BLOCKS of *fn-bch-block* octets and one partial TAIL, each block a PACKED
; NATURAL, one octet a byte:
;
;     (fn-bch-pack xs) = 256^|xs| + sum_i xs_i 256^i
;
; (the top "sentinel" digit keeps trailing zero octets).  A block of 512
; octets is a 65-digit bignum and a cons: about 1.03 octets of heap an octet,
; whatever the shape of the lines.
;
; THE STORE IS CANONICAL: it is a function of the octets alone
; (KEYSTONE fn-bch-wf-is-of-octets: a well-formed store is fn-bch-of its
; octets).  So the per-octet append (fn-bch-push, the logical step the byte
; machine takes) and any bulk append that yields a well-formed store with the
; same octets return EQUAL stores -- which is what lets books/wire-scan's
; span step stay EQUAL to the per-byte fold with the body in this form.
;
; KEYSTONES
;   fn-bch-unpack-of-pack        the codec round trip, for octet lists;
;   fn-bch-octets-of-push-list   the store's octets after appending XS are
;                                its octets and XS (the abstraction);
;   fn-bch-wf-is-of-octets       canonicity;
;   fn-bch-lines-of-join         the lines split back out of lines each
;                                followed by CR LF are those lines.
;
; Every executable here is guard-verified with guard t.  The per-octet
; append costs one block's copy (at most 65 digits); the codec's loops are
; divide and conquer within one block (depth log2 of *fn-bch-block*).

(in-package "ACL2")
(include-book "rev-onto")
(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "std/lists/revappend" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/append" :dir :system))

(defconst *fn-bch-block* 512)


; -----------------------------------------------------------------------------
; Octets and the packed natural.

(defun fn-bch-octetp (x)
  (declare (xargs :guard t))
  (and (natp x) (< x 256)))

(defun fn-bch-octetsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-bch-octetp (car xs))
           (fn-bch-octetsp (cdr xs)))
    (null xs)))

(defun fn-bch-byte (x)
  (declare (xargs :guard t))
  (if (fn-bch-octetp x) x 0))

(defthm fn-bch-byte-natp
  (natp (fn-bch-byte x))
  :rule-classes :type-prescription)

(defthm fn-bch-byte-bound
  (< (fn-bch-byte x) 256)
  :rule-classes :linear)

; The logical packing (a specification: no host path executes it; the
; executables below pack from a buffer span or by one octet).
(defun fn-bch-pack (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (+ (fn-bch-byte (car xs)) (* 256 (fn-bch-pack (cdr xs))))
    1))

(defun fn-bch-unpack (n)
  (declare (xargs :guard t :measure (nfix n)))
  (if (and (natp n) (<= 256 n))
      (cons (mod n 256) (fn-bch-unpack (floor n 256)))
    nil))

(defun fn-bch-packedp (n)
  (declare (xargs :guard t :measure (nfix n)))
  (and (natp n)
       (if (< n 256)
           (equal n 1)
         (fn-bch-packedp (floor n 256)))))

(defthm fn-bch-pack-posp
  (posp (fn-bch-pack xs))
  :rule-classes :type-prescription)

(defthm fn-bch-pack-of-consp-at-least-256
  (implies (consp xs) (<= 256 (fn-bch-pack xs)))
  :rule-classes :linear)

(defthm fn-bch-unpack-of-pack
  (implies (fn-bch-octetsp xs)
           (equal (fn-bch-unpack (fn-bch-pack xs)) xs)))

; Packing reads each element as an octet (fn-bch-byte), so it round-trips
; any list to its octets.
(defun fn-bch-bytes (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (cons (fn-bch-byte (car xs)) (fn-bch-bytes (cdr xs)))
    nil))

(defthm fn-bch-unpack-of-pack-is-bytes
  (equal (fn-bch-unpack (fn-bch-pack xs)) (fn-bch-bytes xs)))

(defthm fn-bch-bytes-when-octetsp
  (implies (fn-bch-octetsp xs) (equal (fn-bch-bytes xs) xs)))

(defthm fn-bch-pack-of-bytes
  (equal (fn-bch-pack (fn-bch-bytes xs)) (fn-bch-pack xs)))

(defthm fn-bch-bytes-of-append
  (equal (fn-bch-bytes (append xs ys))
         (append (fn-bch-bytes xs) (fn-bch-bytes ys))))

(defthm fn-bch-pack-of-cons-byte
  (equal (fn-bch-pack (cons (fn-bch-byte x) ys))
         (fn-bch-pack (cons x ys))))

(defthm fn-bch-pack-of-append-cons-byte
  (equal (fn-bch-pack (append a (cons (fn-bch-byte x) ys)))
         (fn-bch-pack (append a (cons x ys)))))

(defthm fn-bch-packedp-of-pack
  (fn-bch-packedp (fn-bch-pack xs)))

(defthm fn-bch-octetsp-of-unpack
  (fn-bch-octetsp (fn-bch-unpack n)))

(defthm fn-bch-pack-of-unpack
  (implies (fn-bch-packedp n)
           (equal (fn-bch-pack (fn-bch-unpack n)) n)))

; 256^K, by its own recursion so the arithmetic library's normalization of
; `expt' never meets it.
(defun fn-bch-pow (k)
  (declare (xargs :guard t))
  (if (and (natp k) (< 0 k)) (* 256 (fn-bch-pow (- k 1))) 1))

(defthm fn-bch-pow-posp
  (posp (fn-bch-pow k))
  :rule-classes :type-prescription)

(defthm fn-bch-pow-of-1+
  (implies (natp k) (equal (fn-bch-pow (+ 1 k)) (* 256 (fn-bch-pow k)))))

(defthm fn-bch-pow-of-plus
  (implies (and (natp j) (natp k))
           (equal (fn-bch-pow (+ j k)) (* (fn-bch-pow j) (fn-bch-pow k)))))

(in-theory (disable fn-bch-pow))

; The packing of a concatenation: the second part's digits shifted past the
; first's (the first's sentinel is replaced by the second's value).
(defthm fn-bch-pack-of-append
  (equal (fn-bch-pack (append xs ys))
         (+ (fn-bch-pack xs)
            (* (fn-bch-pow (len xs)) (- (fn-bch-pack ys) 1)))))

(defthm fn-bch-pack-of-singleton
  (equal (fn-bch-pack (list b)) (+ 256 (fn-bch-byte b))))

; -----------------------------------------------------------------------------
; The store: (COUNT TAIL-LEN TAIL . BLOCKS), BLOCKS the COUNT full blocks
; newest first, TAIL the packed partial block of TAIL-LEN octets.  The
; accessors are total (guard t) so the wire's scalar guard needs no new
; conjunct; a well-formed store (fn-bch-wfp) is what the theorems assume.

(defun fn-bch-make (count tail-len tail blocks)
  (declare (xargs :guard t))
  (cons count (cons tail-len (cons tail blocks))))

(defun fn-bch-count (s)
  (declare (xargs :guard t))
  (if (consp s) (nfix (car s)) 0))

(defun fn-bch-tail-len (s)
  (declare (xargs :guard t))
  (if (and (consp s) (consp (cdr s))) (nfix (cadr s)) 0))

(defun fn-bch-tail (s)
  (declare (xargs :guard t))
  (if (and (consp s) (consp (cdr s)) (consp (cddr s)) (posp (caddr s)))
      (caddr s)
    1))

(defun fn-bch-blocks (s)
  (declare (xargs :guard t))
  (if (and (consp s) (consp (cdr s)) (consp (cddr s)))
      (cdddr s)
    nil))

(defthm fn-bch-count-of-make
  (equal (fn-bch-count (fn-bch-make count tail-len tail blocks)) (nfix count)))
(defthm fn-bch-tail-len-of-make
  (equal (fn-bch-tail-len (fn-bch-make count tail-len tail blocks)) (nfix tail-len)))
(defthm fn-bch-tail-of-make
  (equal (fn-bch-tail (fn-bch-make count tail-len tail blocks))
         (if (posp tail) tail 1)))
(defthm fn-bch-blocks-of-make
  (equal (fn-bch-blocks (fn-bch-make count tail-len tail blocks)) blocks))

(defun fn-bch-empty ()
  (declare (xargs :guard t))
  (fn-bch-make 0 0 1 nil))

; The number of octets held: constant work.
(defun fn-bch-length (s)
  (declare (xargs :guard t))
  (+ (* *fn-bch-block* (fn-bch-count s)) (fn-bch-tail-len s)))

; Blocks well formed: each packed, of exactly *fn-bch-block* octets.
(defun fn-bch-blocksp (blocks)
  (declare (xargs :guard t))
  (if (consp blocks)
      (and (fn-bch-packedp (car blocks))
           (equal (len (fn-bch-unpack (car blocks))) *fn-bch-block*)
           (fn-bch-blocksp (cdr blocks)))
    (null blocks)))

(defun fn-bch-wfp (s)
  (declare (xargs :guard t))
  (and (consp s) (consp (cdr s)) (consp (cddr s))
       (natp (car s)) (natp (cadr s)) (posp (caddr s))
       (< (fn-bch-tail-len s) *fn-bch-block*)
       (fn-bch-packedp (fn-bch-tail s))
       (equal (len (fn-bch-unpack (fn-bch-tail s))) (fn-bch-tail-len s))
       (fn-bch-blocksp (fn-bch-blocks s))
       (equal (len (fn-bch-blocks s)) (fn-bch-count s))))

(defthm fn-bch-wfp-of-make
  (equal (fn-bch-wfp (fn-bch-make c k tail bl))
         (and (natp c) (natp k) (posp tail)
              (< k *fn-bch-block*)
              (fn-bch-packedp tail)
              (equal (len (fn-bch-unpack tail)) k)
              (fn-bch-blocksp bl)
              (equal (len bl) c))))

(defthm fn-bch-wfp-facts
  (implies (fn-bch-wfp s)
           (and (< (fn-bch-tail-len s) *fn-bch-block*)
                (fn-bch-packedp (fn-bch-tail s))
                (equal (len (fn-bch-unpack (fn-bch-tail s))) (fn-bch-tail-len s))
                (fn-bch-blocksp (fn-bch-blocks s))
                (equal (len (fn-bch-blocks s)) (fn-bch-count s)))))

(defthm fn-bch-wfp-tail-len-bound
  (implies (fn-bch-wfp s)
           (< (fn-bch-tail-len s) *fn-bch-block*))
  :rule-classes :linear)

(defthm fn-bch-make-of-accessors
  (implies (fn-bch-wfp s)
           (equal (fn-bch-make (fn-bch-count s) (fn-bch-tail-len s)
                               (fn-bch-tail s) (fn-bch-blocks s))
                  s)))

; The tail alone well formed (what the bulk append's fast path needs; it
; never reads the blocks).
(defun fn-bch-tail-ok-logic (s)
  (declare (xargs :guard t))
  (and (consp s) (consp (cdr s)) (consp (cddr s))
       (natp (car s)) (natp (cadr s)) (posp (caddr s))
       (< (fn-bch-tail-len s) *fn-bch-block*)
       (fn-bch-packedp (fn-bch-tail s))
       (equal (len (fn-bch-unpack (fn-bch-tail s))) (fn-bch-tail-len s))))

(defthm fn-bch-wfp-implies-tail-ok
  (implies (fn-bch-wfp s) (fn-bch-tail-ok-logic s))
  :hints (("Goal" :in-theory '(fn-bch-wfp fn-bch-tail-ok-logic))))

(defthm fn-bch-tail-ok-of-make
  (equal (fn-bch-tail-ok-logic (fn-bch-make c k tail bl))
         (and (natp c) (natp k) (posp tail)
              (< k *fn-bch-block*)
              (fn-bch-packedp tail)
              (equal (len (fn-bch-unpack tail)) k)))
  :hints (("Goal" :in-theory '(fn-bch-tail-ok-logic fn-bch-make fn-bch-tail fn-bch-tail-len
                               car-cons cdr-cons natp posp nfix
                               (:type-prescription fn-bch-packedp)))))

(defthm fn-bch-make-of-accessors-when-tail-ok
  (implies (fn-bch-tail-ok-logic s)
           (equal (fn-bch-make (fn-bch-count s) (fn-bch-tail-len s)
                               (fn-bch-tail s) (fn-bch-blocks s))
                  s))
  :hints (("Goal" :in-theory (enable fn-bch-make fn-bch-count fn-bch-tail-len fn-bch-tail
                                     fn-bch-blocks fn-bch-tail-ok-logic))))

(defthm fn-bch-tail-ok-tail-len-bound
  (implies (fn-bch-tail-ok-logic s)
           (< (fn-bch-tail-len s) *fn-bch-block*))
  :rule-classes :linear)

(defthm fn-bch-tail-ok-facts
  (implies (fn-bch-tail-ok-logic s)
           (and (< (fn-bch-tail-len s) *fn-bch-block*)
                (fn-bch-packedp (fn-bch-tail s))
                (equal (len (fn-bch-unpack (fn-bch-tail s))) (fn-bch-tail-len s)))))

(in-theory (disable fn-bch-make fn-bch-count fn-bch-tail-len fn-bch-tail
                    fn-bch-blocks fn-bch-wfp))
(in-theory (disable fn-bch-tail-ok-logic))

; The octets a store holds, oldest first (the abstraction).
(defun fn-bch-blocks-octets (blocks)
  (declare (xargs :guard t))
  (if (consp blocks)
      (append (fn-bch-blocks-octets (cdr blocks)) (fn-bch-unpack (car blocks)))
    nil))

(defun fn-bch-octets (s)
  (declare (xargs :guard t))
  (append (fn-bch-blocks-octets (fn-bch-blocks s))
          (fn-bch-unpack (fn-bch-tail s))))

; -----------------------------------------------------------------------------
; Appending one octet: the tail gains a digit under its sentinel; a full tail
; becomes the newest block.  Executes by a shift (one copy of the tail).

(local (defthm fn-bch-pow-is-expt
         (implies (natp k) (equal (fn-bch-pow k) (expt 256 k)))
         :hints (("Goal" :in-theory (enable fn-bch-pow)))))
(local (in-theory (disable fn-bch-pow-is-expt)))

(local (defthm fn-bch-ash-is-times-pow
         (implies (and (natp x) (natp k))
                  (equal (ash x (* 8 k)) (* x (fn-bch-pow k))))
         :hints (("Goal" :in-theory (enable fn-bch-pow-is-expt)))))

(defun fn-bch-digit (b k)
  (declare (xargs :guard (natp k)))
  (mbe :logic (* (+ 255 (fn-bch-byte b)) (fn-bch-pow k))
       :exec (ash (+ 255 (fn-bch-byte b)) (* 8 k))))

(defun fn-bch-push (s b)
  (declare (xargs :guard t))
  (let* ((k (fn-bch-tail-len s))
         (tail (+ (fn-bch-tail s) (fn-bch-digit b k))))
    (if (< (+ 1 k) *fn-bch-block*)
        (fn-bch-make (fn-bch-count s) (+ 1 k) tail (fn-bch-blocks s))
      (fn-bch-make (+ 1 (fn-bch-count s)) 0 1 (cons tail (fn-bch-blocks s))))))

(defun fn-bch-push-list (s xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (fn-bch-push-list (fn-bch-push s (car xs)) (cdr xs))
    s))

; The canonical store of XS.
(defun fn-bch-of (xs)
  (declare (xargs :guard t))
  (fn-bch-push-list (fn-bch-empty) xs))

; -----------------------------------------------------------------------------
; The append's meaning.

; The tail with one more digit is the packing of its octets and B.
(defthm fn-bch-tail-plus-digit-is-pack
  (implies (and (fn-bch-packedp tail)
                (equal (len (fn-bch-unpack tail)) k))
           (equal (+ tail (fn-bch-digit b k))
                  (fn-bch-pack (append (fn-bch-unpack tail) (list b)))))
  :hints (("Goal" :use ((:instance fn-bch-pack-of-append
                                   (xs (fn-bch-unpack tail)) (ys (list b))))
                  :in-theory (disable fn-bch-pack-of-append))))

(defthm fn-bch-len-of-unpack-of-pack
  (equal (len (fn-bch-unpack (fn-bch-pack xs))) (len xs)))

(defthm fn-bch-octetsp-of-append
  (implies (and (fn-bch-octetsp xs) (fn-bch-octetsp ys))
           (fn-bch-octetsp (append xs ys))))

(defthm fn-bch-octetsp-of-blocks-octets
  (fn-bch-octetsp (fn-bch-blocks-octets blocks)))

; Under a well-formed store the append is the packing of the tail's octets
; and B.
(defthm fn-bch-push-of-tail-ok
  (implies (fn-bch-tail-ok-logic s)
           (equal (fn-bch-push s b)
                  (let ((tail (fn-bch-pack (append (fn-bch-unpack (fn-bch-tail s)) (list b)))))
                    (if (< (+ 1 (fn-bch-tail-len s)) *fn-bch-block*)
                        (fn-bch-make (fn-bch-count s) (+ 1 (fn-bch-tail-len s)) tail (fn-bch-blocks s))
                      (fn-bch-make (+ 1 (fn-bch-count s)) 0 1 (cons tail (fn-bch-blocks s)))))))
  :hints (("Goal" :use ((:instance fn-bch-tail-plus-digit-is-pack
                                   (tail (fn-bch-tail s)) (k (fn-bch-tail-len s))))
                  :in-theory (disable fn-bch-tail-plus-digit-is-pack fn-bch-digit
                                      fn-bch-make fn-bch-tail fn-bch-tail-len
                                      fn-bch-count fn-bch-blocks fn-bch-pack-of-append))))

(defthm fn-bch-wfp-of-push
  (implies (fn-bch-wfp s)
           (fn-bch-wfp (fn-bch-push s b)))
  :hints (("Goal" :in-theory (disable fn-bch-push fn-bch-pack-of-append))))

(defthm fn-bch-octets-of-push
  (implies (and (fn-bch-wfp s) (fn-bch-octetp b))
           (equal (fn-bch-octets (fn-bch-push s b))
                  (append (fn-bch-octets s) (list b))))
  :hints (("Goal" :in-theory (disable fn-bch-push fn-bch-pack-of-append))))

(in-theory (disable fn-bch-push))

(defthm fn-bch-wfp-of-push-list
  (implies (fn-bch-wfp s)
           (fn-bch-wfp (fn-bch-push-list s xs)))
  :hints (("Goal" :induct (fn-bch-push-list s xs)
                  :in-theory (disable fn-bch-wfp fn-bch-push-of-tail-ok))))

; KEYSTONE (the abstraction): appending XS to a well-formed store appends XS
; to its octets.
(defthm fn-bch-octets-of-push-list
  (implies (and (fn-bch-wfp s) (fn-bch-octetsp xs))
           (equal (fn-bch-octets (fn-bch-push-list s xs))
                  (append (fn-bch-octets s) xs)))
  :hints (("Goal" :induct (fn-bch-push-list s xs)
                  :in-theory (disable fn-bch-wfp fn-bch-octets fn-bch-push-of-tail-ok))))

(defthm fn-bch-push-list-of-append
  (equal (fn-bch-push-list s (append xs ys))
         (fn-bch-push-list (fn-bch-push-list s xs) ys)))

(defthm fn-bch-wfp-of-empty
  (fn-bch-wfp (fn-bch-empty)))

(defthm fn-bch-octets-of-empty
  (equal (fn-bch-octets (fn-bch-empty)) nil))

(defthm fn-bch-octets-of-of
  (implies (fn-bch-octetsp xs)
           (equal (fn-bch-octets (fn-bch-of xs)) xs)))

(defthm fn-bch-wfp-of-of
  (fn-bch-wfp (fn-bch-of xs))
  :hints (("Goal" :in-theory (disable fn-bch-wfp))))

; -----------------------------------------------------------------------------
; Canonicity.

; Filling a well-formed tail with XS, at most up to one block.
(defthm fn-bch-push-list-fills-the-tail
   (implies (and (fn-bch-tail-ok-logic s)
                 (true-listp xs)
                 (<= (+ (fn-bch-tail-len s) (len xs)) *fn-bch-block*))
            (equal (fn-bch-push-list s xs)
                   (let ((tail (fn-bch-pack (append (fn-bch-unpack (fn-bch-tail s)) xs))))
                     (if (< (+ (fn-bch-tail-len s) (len xs)) *fn-bch-block*)
                         (fn-bch-make (fn-bch-count s) (+ (fn-bch-tail-len s) (len xs))
                                      tail (fn-bch-blocks s))
                       (fn-bch-make (+ 1 (fn-bch-count s)) 0 1
                                    (cons tail (fn-bch-blocks s)))))))
   :hints (("Goal" :induct (fn-bch-push-list s xs)
                   :in-theory (disable fn-bch-pack-of-append fn-bch-make fn-bch-wfp
                                       fn-bch-unpack fn-bch-pack fn-bch-byte))))

(local
 (defthm fn-bch-push-list-of-blocks-octets
   (implies (and (fn-bch-blocksp blocks))
            (equal (fn-bch-push-list (fn-bch-empty) (fn-bch-blocks-octets blocks))
                   (fn-bch-make (len blocks) 0 1 blocks)))
   :hints (("Goal" :induct (fn-bch-blocks-octets blocks)
                   :in-theory (disable fn-bch-make)))))

; KEYSTONE (canonicity): a well-formed store is the canonical store of its
; octets.
(defthm fn-bch-wf-is-of-octets
  (implies (fn-bch-wfp s)
           (equal (fn-bch-of (fn-bch-octets s)) s))
  :hints (("Goal" :use ((:instance fn-bch-push-list-of-blocks-octets
                                   (blocks (fn-bch-blocks s)))
                        (:instance fn-bch-push-list-fills-the-tail
                                   (s (fn-bch-make (fn-bch-count s) 0 1 (fn-bch-blocks s)))
                                   (xs (fn-bch-unpack (fn-bch-tail s)))))
                  :in-theory (disable fn-bch-push-list-of-blocks-octets
                                      fn-bch-push-list-fills-the-tail))))

(defthm fn-bch-wf-equal-by-octets
  (implies (and (fn-bch-wfp s1) (fn-bch-wfp s2)
                (equal (fn-bch-octets s1) (fn-bch-octets s2)))
           (equal s1 s2))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bch-wf-is-of-octets (s s1))
                        (:instance fn-bch-wf-is-of-octets (s s2)))
                  :in-theory (disable fn-bch-wf-is-of-octets fn-bch-of fn-bch-octets))))

; -----------------------------------------------------------------------------
; Reading the octets back: the low LEN base-256 digits of N.  Total, so the
; readers below need only the wire's scalar guard; under a well-formed store
; they are the unpacking (fn-bch-unpack-is-digits).  Executes divide and
; conquer: two shifts a level, depth log2 of LEN.

(defun fn-bch-digits (n len)
  (declare (xargs :guard (and (natp n) (natp len))))
  (if (zp len)
      nil
    (cons (mod n 256) (fn-bch-digits (floor n 256) (- len 1)))))

(defthm fn-bch-unpack-is-digits
  (implies (fn-bch-packedp n)
           (equal (fn-bch-digits n (len (fn-bch-unpack n)))
                  (fn-bch-unpack n))))

(local
 (defthm fn-bch-floor-floor-256
   (implies (and (natp n) (natp h))
            (equal (floor (floor n 256) (fn-bch-pow h))
                   (floor n (fn-bch-pow (+ 1 h)))))))

(defthm fn-bch-digits-of-plus
  (implies (and (natp n) (natp a) (natp b))
           (equal (fn-bch-digits n (+ a b))
                  (append (fn-bch-digits n a)
                          (fn-bch-digits (floor n (fn-bch-pow a)) b))))
  :hints (("Goal" :induct (fn-bch-digits n a))))

(local
 (defthm fn-bch-floor-of-mod-256
   (implies (and (natp n) (posp q))
            (equal (floor (mod n (* 256 q)) 256)
                   (mod (floor n 256) q)))))

(local
 (defthm fn-bch-mod-of-mod-256
   (implies (and (natp n) (posp q))
            (equal (mod (mod n (* 256 q)) 256)
                   (mod n 256)))))

(defthm fn-bch-digits-of-mod
  (implies (and (natp n) (natp h))
           (equal (fn-bch-digits (mod n (fn-bch-pow h)) h)
                  (fn-bch-digits n h)))
  :hints (("Goal" :induct (fn-bch-digits n h)
                  :in-theory (enable fn-bch-pow))))

; The executable reader: the digits consed before ACC, divide and conquer.
; Depth log2 of LEN (a block: 7 levels); each level two shifts of its part.
(defun fn-bch-low (n h)
  (declare (xargs :guard (and (natp n) (natp h))
                  :guard-hints (("Goal" :in-theory (enable fn-bch-pow-is-expt mod)))))
  (mbe :logic (mod n (fn-bch-pow h))
       :exec (- n (ash (ash n (- (* 8 h))) (* 8 h)))))

(defun fn-bch-high (n h)
  (declare (xargs :guard (and (natp n) (natp h))
                  :guard-hints (("Goal" :in-theory (enable fn-bch-pow-is-expt)))))
  (mbe :logic (floor n (fn-bch-pow h))
       :exec (ash n (- (* 8 h)))))

(defun fn-bch-digits-onto (n len acc)
  (declare (xargs :guard (and (natp n) (natp len))
                  :measure (nfix len)
                  :verify-guards nil))
  (if (or (zp len) (<= len 8))
      (append (fn-bch-digits n len) acc)
    (let ((h (floor len 2)))
      (fn-bch-digits-onto (fn-bch-low n h) h
                          (fn-bch-digits-onto (fn-bch-high n h) (- len h) acc)))))

(defthm fn-bch-digits-onto-is-digits
  (implies (and (natp n) (natp len))
           (equal (fn-bch-digits-onto n len acc)
                  (append (fn-bch-digits n len) acc)))
  :hints (("Goal" :induct (fn-bch-digits-onto n len acc)
                  :in-theory (disable fn-bch-digits fn-bch-digits-of-plus))
          ("Subgoal *1/2" :use ((:instance fn-bch-digits-of-plus
                                           (a (floor len 2)) (b (- len (floor len 2))))))))

(defthm fn-bch-digits-true-listp
  (true-listp (fn-bch-digits n len))
  :rule-classes :type-prescription)

(verify-guards fn-bch-digits-onto)

; -----------------------------------------------------------------------------
; The lines.  The body held is its lines, each followed by CR LF; a line
; ends at an LF, and the one CR before it is not part of the line.

(defun fn-bch-line-of (cur)
  (declare (xargs :guard t))
  (if (and (consp cur) (equal (car cur) 13))
      (fn-ag-rev-onto (cdr cur) nil)
    (fn-ag-rev-onto cur nil)))

; (CUR . LINES) after reading XS: CUR the current line reversed, LINES the
; finished lines newest first.  A loop.
(defun fn-bch-split-onto (xs cur lines)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (equal (car xs) 10)
          (fn-bch-split-onto (cdr xs) nil (cons (fn-bch-line-of cur) lines))
        (fn-bch-split-onto (cdr xs) (cons (car xs) cur) lines))
    (cons cur lines)))

(defthm fn-bch-split-onto-of-append
  (equal (fn-bch-split-onto (append xs ys) cur lines)
         (let ((st (fn-bch-split-onto xs cur lines)))
           (fn-bch-split-onto ys (car st) (cdr st)))))

; The lines joined, each followed by CR LF (the specification of the body
; the wire holds).
(defun fn-bch-join (lines)
  (declare (xargs :guard t))
  (if (consp lines)
      (append (fn-ag-rev-onto (fn-ag-rev-onto (car lines) nil) nil)
              (list* 13 10 (fn-bch-join (cdr lines))))
    nil))

(defun fn-bch-no-lf-p (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (not (equal (car xs) 10)) (fn-bch-no-lf-p (cdr xs)))
    (null xs)))

(defun fn-bch-clean-linesp (lines)
  (declare (xargs :guard t))
  (if (consp lines)
      (and (fn-bch-no-lf-p (car lines)) (fn-bch-clean-linesp (cdr lines)))
    (null lines)))

(local (defthm fn-bch-rev-onto-is-revappend
         (equal (fn-ag-rev-onto xs acc) (revappend xs acc))))

(local (defthm fn-bch-no-lf-p-true-listp
         (implies (fn-bch-no-lf-p xs) (true-listp xs))
         :rule-classes :forward-chaining))

(defthm fn-bch-split-onto-of-no-lf
  (implies (fn-bch-no-lf-p xs)
           (equal (fn-bch-split-onto xs cur lines)
                  (cons (revappend xs cur) lines))))


(local
 (defun fn-bch-join-induction (ls lines)
   (if (consp ls)
       (fn-bch-join-induction (cdr ls) (cons (car ls) lines))
     lines)))

(defthm fn-bch-split-onto-of-join
  (implies (fn-bch-clean-linesp ls)
           (equal (fn-bch-split-onto (fn-bch-join ls) nil lines)
                  (cons nil (revappend ls lines))))
  :hints (("Goal" :induct (fn-bch-join-induction ls lines))))

; KEYSTONE: the lines split back out of lines joined by CR LF are those
; lines (newest first, as the wire keeps them).
(defthm fn-bch-lines-of-join
  (implies (fn-bch-clean-linesp ls)
           (equal (cdr (fn-bch-split-onto (fn-bch-join ls) nil nil))
                  (revappend ls nil))))

; -----------------------------------------------------------------------------
; The lines of a store, read block by block (a block's digits at a time, so
; the transient is one block's list besides the lines themselves).

(defthm fn-bch-split-onto-consp
  (consp (fn-bch-split-onto xs cur lines))
  :rule-classes :type-prescription)

(defun fn-bch-split-blocks (bl st)
  (declare (xargs :guard (consp st)))
  (if (consp bl)
      (fn-bch-split-blocks
       (cdr bl)
       (fn-bch-split-onto (fn-bch-digits-onto (nfix (car bl)) *fn-bch-block* nil)
                          (car st) (cdr st)))
    st))

(defthm fn-bch-split-blocks-consp
  (implies (consp st) (consp (fn-bch-split-blocks bl st)))
  :rule-classes :type-prescription)

; The finished lines of S, newest first (its partial last line, if any, is
; not among them).
(defun fn-bch-lines-rev (s)
  (declare (xargs :guard t))
  (let ((st (fn-bch-split-blocks (fn-ag-rev-onto (fn-bch-blocks s) nil) (cons nil nil))))
    (cdr (fn-bch-split-onto (fn-bch-digits-onto (fn-bch-tail s) (fn-bch-tail-len s) nil)
                            (car st) (cdr st)))))

(defun fn-bch-blocks-octets-old (bl)
  (if (consp bl)
      (append (fn-bch-unpack (car bl)) (fn-bch-blocks-octets-old (cdr bl)))
    nil))

(local (defthm fn-bch-blocks-octets-old-of-append
         (equal (fn-bch-blocks-octets-old (append a b))
                (append (fn-bch-blocks-octets-old a) (fn-bch-blocks-octets-old b)))))

(local (defthm fn-bch-blocks-octets-is-old-of-rev
         (equal (fn-bch-blocks-octets bl)
                (fn-bch-blocks-octets-old (rev bl)))))

(local (defthm fn-bch-blocksp-of-append
         (implies (and (fn-bch-blocksp a) (fn-bch-blocksp b))
                  (fn-bch-blocksp (append a b)))))

(local (defthm fn-bch-blocksp-of-rev
         (implies (fn-bch-blocksp a) (fn-bch-blocksp (rev a)))))

(local (defthm fn-bch-split-blocks-is-split-onto
         (implies (and (fn-bch-blocksp bl) (consp st))
                  (equal (fn-bch-split-blocks bl st)
                         (fn-bch-split-onto (fn-bch-blocks-octets-old bl) (car st) (cdr st))))
         :hints (("Goal" :induct (fn-bch-split-blocks bl st)
                  :in-theory (disable fn-bch-unpack-is-digits))
                 ("Subgoal *1/1" :use ((:instance fn-bch-unpack-is-digits (n (car bl))))))))

; The lines of a well-formed store are the lines of its octets.
(defthm fn-bch-lines-rev-is-split
  (implies (fn-bch-wfp s)
           (equal (fn-bch-lines-rev s)
                  (cdr (fn-bch-split-onto (fn-bch-octets s) nil nil))))
  :hints (("Goal" :use ((:instance fn-bch-unpack-is-digits (n (fn-bch-tail s))))
                  :in-theory (disable fn-bch-unpack-is-digits))))

; -----------------------------------------------------------------------------
; The fast path's test, in constant work: the tail is packed with exactly its
; length's octets exactly when its digits above them are the sentinel 1.

(local
 (defthm fn-bch-packed-len-is-top-digit
   (implies (and (posp n) (natp k))
            (equal (and (fn-bch-packedp n) (equal (len (fn-bch-unpack n)) k))
                   (equal (floor n (fn-bch-pow k)) 1)))
   :hints (("Goal" :induct (fn-bch-digits n k)
                   :in-theory (enable fn-bch-pow)))))

(defun fn-bch-tail-okp (s)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable fn-bch-tail-ok-logic fn-bch-pow-is-expt)
                                 :use ((:instance fn-bch-packed-len-is-top-digit
                                                  (n (fn-bch-tail s)) (k (fn-bch-tail-len s))))))))
  (mbe :logic (fn-bch-tail-ok-logic s)
       :exec (and (consp s) (consp (cdr s)) (consp (cddr s))
                  (natp (car s)) (natp (cadr s)) (posp (caddr s))
                  (< (fn-bch-tail-len s) *fn-bch-block*)
                  (equal (ash (fn-bch-tail s) (- (* 8 (fn-bch-tail-len s)))) 1))))

; X shifted past K octets.
(defun fn-bch-shift (x k)
  (declare (xargs :guard (and (natp x) (natp k))))
  (mbe :logic (* x (fn-bch-pow k))
       :exec (ash x (* 8 k))))
