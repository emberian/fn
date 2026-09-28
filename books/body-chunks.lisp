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
;   fn-bch-octets-of-push-list   the store's octets after appending XS are
;                                its octets and XS (the abstraction);
;   fn-bch-wf-is-of-octets       canonicity;
;   fn-bch-lines-of-join         the lines split back out of lines each
;                                followed by CR LF are those lines.
;
;   fn-bch-body-okp-*            the held body (below): what the wire's
;                                article mode keeps, and its lines.
;
; Every executable here is guard-verified with guard t.  The per-octet
; append costs one block's copy (at most 65 digits); a block is read by the
; codec's divide and conquer (depth log2 of *fn-bch-block*).

(in-package "ACL2")
(include-book "rev-onto")
(include-book "packed-octets")
(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "std/lists/revappend" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/append" :dir :system))

(defconst *fn-bch-block* 512)

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
; Appending one octet: the tail gains a digit under its sentinel (fn-bch-digit,
; books/packed-octets.lisp); a full tail becomes the newest block.

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

(defthm fn-bch-octets-true-listp
  (true-listp (fn-bch-octets s))
  :rule-classes :type-prescription)

(local (defthm fn-bch-len-of-blocks-octets
         (implies (fn-bch-blocksp bl)
                  (equal (len (fn-bch-blocks-octets bl))
                         (* *fn-bch-block* (len bl))))))

(defthm fn-bch-len-of-octets
  (implies (fn-bch-wfp s)
           (equal (len (fn-bch-octets s)) (fn-bch-length s))))

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

(defun fn-bch-tail-okp (s)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (e/d (fn-bch-tail-ok-logic) (ash fn-bch-packedp fn-bch-unpack))
                                 :use ((:instance fn-bch-top-digit-test
                                                  (n (fn-bch-tail s)) (k (fn-bch-tail-len s))))))))
  (mbe :logic (fn-bch-tail-ok-logic s)
       :exec (and (consp s) (consp (cdr s)) (consp (cddr s))
                  (natp (car s)) (natp (cadr s)) (posp (caddr s))
                  (< (fn-bch-tail-len s) *fn-bch-block*)
                  (equal (ash (fn-bch-tail s) (- (* 8 (fn-bch-tail-len s)))) 1))))

; -----------------------------------------------------------------------------
; THE HELD BODY (books/wire.lisp, article mode).  A store B holds the decoded
; body so far: its completed lines each followed by CR LF (N octets, the
; TEXT), then the current line's decoded octets (the PARTIAL).  L is the
; current line's length as it arrived; it is one more than the partial's
; exactly when the line began with a dot, which the wire dropped.

; Octets none of which is a CR or an LF: a line's content.
(defun fn-bch-plain-octetsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-bch-octetp (car xs))
           (not (equal (car xs) 13))
           (not (equal (car xs) 10))
           (fn-bch-plain-octetsp (cdr xs)))
    (null xs)))

(defun fn-bch-plain-linesp (lines)
  (declare (xargs :guard t))
  (if (consp lines)
      (and (fn-bch-plain-octetsp (car lines))
           (fn-bch-plain-linesp (cdr lines)))
    (null lines)))

; The lines of CR LF text, first first.
(defun fn-bch-lines-of (text)
  (declare (xargs :guard t))
  (fn-ag-rev-onto (cdr (fn-bch-split-onto text nil nil)) nil))

; TEXT is lines each followed by CR LF.
(defun fn-bch-framedp (text)
  (declare (xargs :guard t))
  (let ((lines (fn-bch-lines-of text)))
    (and (fn-bch-plain-linesp lines)
         (equal (fn-bch-join lines) text))))

(defun fn-bch-held-text (b n)
  (declare (xargs :guard t))
  (let ((o (fn-bch-octets b)))
    (take (min (nfix n) (len o)) o)))

(defun fn-bch-held-partial (b n)
  (declare (xargs :guard t))
  (nthcdr (nfix n) (fn-bch-octets b)))

; The current line's decoded length: constant work.
(defun fn-bch-partial-len (b n)
  (declare (xargs :guard t))
  (nfix (- (fn-bch-length b) (nfix n))))

; The completed lines (the abstraction the wire's article event is).
(defun fn-bch-held-lines (b n)
  (declare (xargs :guard t))
  (fn-bch-lines-of (fn-bch-held-text b n)))

(defun fn-bch-body-okp (b n l)
  (declare (xargs :guard t))
  (let ((p (fn-bch-held-partial b n)))
    (and (fn-bch-wfp b)
         (natp n)
         (<= n (fn-bch-length b))
         (fn-bch-framedp (fn-bch-held-text b n))
         (fn-bch-plain-octetsp p)
         (or (equal l (len p)) (equal l (+ 1 (len p))))
         (or (not (equal l (len p))) (not (equal (car p) 46))))))

(local (defthm fn-bch-take-of-append
         (implies (and (natp n) (<= n (len x)))
                  (equal (take n (append x y)) (take n x)))))

(local (defthm fn-bch-nthcdr-of-append
         (implies (and (natp n) (<= n (len x)))
                  (equal (nthcdr n (append x y)) (append (nthcdr n x) y)))))

(local (defthm fn-bch-true-listp-of-nthcdr
         (implies (true-listp x) (true-listp (nthcdr n x)))))

(local (defthm fn-bch-len-of-nthcdr
         (implies (and (natp n) (<= n (len x)))
                  (equal (len (nthcdr n x)) (- (len x) n)))))

(local (defthm fn-bch-take-at-len
         (implies (and (true-listp x) (equal n (len x)))
                  (equal (take n x) x))))

(local (defthm fn-bch-take-zero (equal (take 0 x) nil)))

(local (defthm fn-bch-nthcdr-of-nil
         (equal (nthcdr n nil) nil)
         :hints (("Goal" :in-theory (enable nthcdr)))))

(local (defthm fn-bch-consp-of-nthcdr
         (equal (consp (nthcdr n x)) (< (nfix n) (len x)))
         :hints (("Goal" :in-theory (enable nthcdr)))))

(local (in-theory (disable take nthcdr)))

(defthm fn-bch-plain-octetsp-true-listp
  (implies (fn-bch-plain-octetsp xs) (true-listp xs))
  :rule-classes :forward-chaining)

(defthm fn-bch-plain-octetsp-of-append
  (equal (fn-bch-plain-octetsp (append xs ys))
         (and (fn-bch-plain-octetsp (true-list-fix xs))
              (fn-bch-plain-octetsp ys))))

(defthm fn-bch-plain-linesp-of-append
  (equal (fn-bch-plain-linesp (append xs ys))
         (and (fn-bch-plain-linesp (true-list-fix xs))
              (fn-bch-plain-linesp ys))))

(local (defthm fn-bch-plain-octetsp-no-lf
         (implies (fn-bch-plain-octetsp xs) (fn-bch-no-lf-p xs))))

(local (defthm fn-bch-plain-linesp-clean
         (implies (fn-bch-plain-linesp ls) (fn-bch-clean-linesp ls))))

(local (defthm fn-bch-plain-linesp-true-listp
         (implies (fn-bch-plain-linesp ls) (true-listp ls))
         :rule-classes :forward-chaining))

(defthm fn-bch-lines-of-of-join
  (implies (fn-bch-plain-linesp ls)
           (equal (fn-bch-lines-of (fn-bch-join ls)) ls)))

(defthm fn-bch-framedp-of-join
  (implies (fn-bch-plain-linesp ls)
           (fn-bch-framedp (fn-bch-join ls))))

(defthm fn-bch-framedp-facts
  (implies (fn-bch-framedp text)
           (and (fn-bch-plain-linesp (fn-bch-lines-of text))
                (equal (fn-bch-join (fn-bch-lines-of text)) text))))

(in-theory (disable fn-bch-lines-of fn-bch-framedp))

(defthm fn-bch-join-of-append
  (implies (true-listp p)
           (equal (fn-bch-join (append ls (list p)))
                  (append (fn-bch-join ls) p (list 13 10)))))

(defthm fn-bch-framedp-append-line
  (implies (and (fn-bch-framedp text) (fn-bch-plain-octetsp p))
           (and (fn-bch-framedp (append text p (list 13 10)))
                (equal (fn-bch-lines-of (append text p (list 13 10)))
                       (append (fn-bch-lines-of text) (list p)))))
  :hints (("Goal" :in-theory (disable fn-bch-framedp-of-join fn-bch-lines-of-of-join
                                      fn-bch-join-of-append fn-bch-framedp-facts)
                  :use ((:instance fn-bch-framedp-facts)
                        (:instance fn-bch-framedp-of-join
                                   (ls (append (fn-bch-lines-of text) (list p))))
                        (:instance fn-bch-lines-of-of-join
                                   (ls (append (fn-bch-lines-of text) (list p))))
                        (:instance fn-bch-join-of-append
                                   (ls (fn-bch-lines-of text)))))))

(defthm fn-bch-body-okp-of-empty
  (fn-bch-body-okp (fn-bch-empty) 0 0))

(local (in-theory (disable fn-bch-octets fn-bch-push fn-bch-push-of-tail-ok fn-bch-length)))

(defthm fn-bch-held-text-of-push
  (implies (and (fn-bch-wfp b) (fn-bch-octetp x) (natp n) (<= n (fn-bch-length b)))
           (equal (fn-bch-held-text (fn-bch-push b x) n)
                  (fn-bch-held-text b n))))

(defthm fn-bch-held-partial-of-push
  (implies (and (fn-bch-wfp b) (fn-bch-octetp x) (natp n) (<= n (fn-bch-length b)))
           (equal (fn-bch-held-partial (fn-bch-push b x) n)
                  (append (fn-bch-held-partial b n) (list x)))))

(defthm fn-bch-len-of-held-partial
  (implies (and (fn-bch-wfp b) (natp n) (<= n (fn-bch-length b)))
           (equal (len (fn-bch-held-partial b n))
                  (fn-bch-partial-len b n))))

(defthm fn-bch-length-of-push
  (implies (fn-bch-wfp b)
           (equal (fn-bch-length (fn-bch-push b x))
                  (+ 1 (fn-bch-length b))))
  :hints (("Goal" :in-theory (enable fn-bch-push-of-tail-ok fn-bch-length))))

(defthm fn-bch-octets-at-length-zero
  (implies (and (fn-bch-wfp b) (equal (fn-bch-length b) 0))
           (equal (fn-bch-octets b) nil))
  :hints (("Goal" :use ((:instance fn-bch-len-of-octets (s b)))
                  :expand ((len (fn-bch-octets b)))
                  :in-theory (disable fn-bch-len-of-octets))))

(defthm fn-bch-held-text-at-length
  (implies (fn-bch-wfp b)
           (equal (fn-bch-held-text b (fn-bch-length b))
                  (fn-bch-octets b))))

(local (defthm fn-bch-append-take-nthcdr
         (implies (and (natp n) (<= n (len x)) (true-listp x))
                  (equal (append (take n x) (nthcdr n x)) x))
         :hints (("Goal" :in-theory (enable take nthcdr)))))

(defthm fn-bch-held-text-and-partial
  (implies (and (fn-bch-wfp b) (natp n) (<= n (fn-bch-length b)))
           (equal (append (fn-bch-held-text b n) (fn-bch-held-partial b n))
                  (fn-bch-octets b)))
  :hints (("Goal" :use ((:instance fn-bch-append-take-nthcdr (x (fn-bch-octets b)))
                        (:instance fn-bch-len-of-octets (s b)))
                  :in-theory (disable fn-bch-append-take-nthcdr fn-bch-len-of-octets))))

(defthm fn-bch-consp-of-held-partial
  (implies (and (fn-bch-wfp b) (natp n) (<= n (fn-bch-length b)))
           (equal (consp (fn-bch-held-partial b n))
                  (not (equal (fn-bch-partial-len b n) 0))))
  :hints (("Goal" :use ((:instance fn-bch-len-of-held-partial))
                  :expand ((len (fn-bch-held-partial b n)))
                  :in-theory (disable fn-bch-len-of-held-partial))))

(defthm fn-bch-partial-len-plus
  (implies (and (natp n) (<= n (fn-bch-length b)))
           (equal (+ n (fn-bch-partial-len b n)) (fn-bch-length b)))
  :hints (("Goal" :in-theory (enable fn-bch-partial-len))))

(local (defthm fn-bch-nthcdr-at-len
         (implies (and (true-listp x) (equal n (len x)))
                  (equal (nthcdr n x) nil))
         :hints (("Goal" :in-theory (enable nthcdr)))))

(defthm fn-bch-held-partial-at-length
  (implies (fn-bch-wfp b)
           (equal (fn-bch-held-partial b (fn-bch-length b)) nil)))

(defthm fn-bch-line-end-held
  (implies (fn-bch-wfp b)
           (let ((b2 (fn-bch-push (fn-bch-push b 13) 10))
                 (m (+ 2 (fn-bch-length b))))
             (and (equal (fn-bch-held-text b2 m)
                         (append (fn-bch-octets b) (list 13 10)))
                  (equal (fn-bch-held-partial b2 m) nil)
                  (equal (fn-bch-partial-len b2 m) 0)
                  (equal (fn-bch-length b2) m))))
  :hints (("Goal" :use ((:instance fn-bch-held-text-at-length (b (fn-bch-push (fn-bch-push b 13) 10)))
                        (:instance fn-bch-held-partial-at-length (b (fn-bch-push (fn-bch-push b 13) 10))))
                  :in-theory (disable fn-bch-held-text-at-length
                                      fn-bch-held-partial-at-length
                                      fn-bch-held-text fn-bch-held-partial))))

(defthm fn-bch-partial-len-at-length
  (equal (fn-bch-partial-len b (fn-bch-length b)) 0)
  :hints (("Goal" :in-theory (enable fn-bch-partial-len))))

(defthm fn-bch-held-partial-true-listp
  (true-listp (fn-bch-held-partial b n))
  :rule-classes :type-prescription)

(defthm fn-bch-held-partial-empty
  (implies (and (fn-bch-wfp b) (natp n) (<= n (fn-bch-length b))
                (equal (fn-bch-partial-len b n) 0))
           (equal (fn-bch-held-partial b n) nil))
  :hints (("Goal" :use ((:instance fn-bch-consp-of-held-partial))
                  :in-theory (disable fn-bch-consp-of-held-partial fn-bch-held-partial
                                      fn-bch-partial-len))))

(in-theory (disable fn-bch-held-text fn-bch-held-partial fn-bch-partial-len))

(defthm fn-bch-body-okp-dot
  (implies (fn-bch-body-okp b n 0)
           (fn-bch-body-okp b n 1)))

(defthm fn-bch-body-okp-octet
  (implies (and (fn-bch-body-okp b n l)
                (fn-bch-octetp x)
                (not (equal x 13))
                (not (equal x 10))
                (not (and (equal l 0) (equal x 46))))
           (fn-bch-body-okp (fn-bch-push b x) n (+ 1 l))))

(defthm fn-bch-body-okp-line
  (implies (fn-bch-body-okp b n l)
           (fn-bch-body-okp (fn-bch-push (fn-bch-push b 13) 10)
                            (+ 2 n (fn-bch-partial-len b n))
                            0))
  :hints (("Goal" :use ((:instance fn-bch-held-text-and-partial)
                        (:instance fn-bch-framedp-append-line
                                   (text (fn-bch-held-text b n))
                                   (p (fn-bch-held-partial b n))))
                  :in-theory (disable fn-bch-held-text-and-partial fn-bch-framedp-append-line))))

(defthm fn-bch-body-okp-facts
  (implies (fn-bch-body-okp b n l)
           (and (fn-bch-wfp b)
                (natp n)
                (<= n (fn-bch-length b))
                (fn-bch-framedp (fn-bch-held-text b n))
                (fn-bch-plain-octetsp (fn-bch-held-partial b n))
                (or (equal l (fn-bch-partial-len b n))
                    (equal l (+ 1 (fn-bch-partial-len b n))))))
  :rule-classes nil)

; The lines the terminator reads out of the store are the completed lines.
(defthm fn-bch-body-okp-terminator-lines
  (implies (and (fn-bch-body-okp b n l)
                (equal (fn-bch-partial-len b n) 0))
           (equal (fn-ag-rev-onto (fn-bch-lines-rev b) nil)
                  (fn-bch-held-lines b n)))
  :hints (("Goal" :use ((:instance fn-bch-partial-len-plus)
                        (:instance fn-bch-held-text-at-length))
                  :in-theory (e/d (fn-bch-lines-of)
                                  (fn-bch-partial-len-plus fn-bch-held-text-at-length)))))

(defthm fn-bch-held-lines-of-empty
  (equal (fn-bch-held-lines (fn-bch-empty) 0) nil))

(defthm fn-bch-held-lines-of-push
  (implies (and (fn-bch-wfp b) (fn-bch-octetp x) (natp n) (<= n (fn-bch-length b)))
           (equal (fn-bch-held-lines (fn-bch-push b x) n)
                  (fn-bch-held-lines b n))))

(defthm fn-bch-held-lines-of-line
  (implies (fn-bch-body-okp b n l)
           (equal (fn-bch-held-lines (fn-bch-push (fn-bch-push b 13) 10)
                                     (+ 2 n (fn-bch-partial-len b n)))
                  (append (fn-bch-held-lines b n)
                          (list (fn-bch-held-partial b n)))))
  :hints (("Goal" :use ((:instance fn-bch-held-text-and-partial)
                        (:instance fn-bch-framedp-append-line
                                   (text (fn-bch-held-text b n))
                                   (p (fn-bch-held-partial b n))))
                  :in-theory (disable fn-bch-held-text-and-partial fn-bch-framedp-append-line))))

(defthm fn-bch-body-okp-length-bound
  (implies (fn-bch-body-okp b n l)
           (<= (fn-bch-length b) (+ n l)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-bch-body-okp-facts)
                        (:instance fn-bch-partial-len-plus))
                  :in-theory (disable fn-bch-partial-len-plus))))

; -----------------------------------------------------------------------------
; A run of a line's octets appended at once (the wire's article lines, the
; outbound round trip).

(defthm fn-bch-length-of-push-list
  (implies (fn-bch-wfp b)
           (equal (fn-bch-length (fn-bch-push-list b xs))
                  (+ (fn-bch-length b) (len xs))))
  :hints (("Goal" :induct (fn-bch-push-list b xs))))

(defthm fn-bch-held-lines-of-push-list
  (implies (and (fn-bch-wfp b) (fn-bch-octetsp xs) (natp n) (<= n (fn-bch-length b)))
           (equal (fn-bch-held-lines (fn-bch-push-list b xs) n)
                  (fn-bch-held-lines b n)))
  :hints (("Goal" :induct (fn-bch-push-list b xs))))

(defthm fn-bch-held-partial-of-push-list
  (implies (and (fn-bch-wfp b) (fn-bch-octetsp xs) (natp n) (<= n (fn-bch-length b)))
           (equal (fn-bch-held-partial (fn-bch-push-list b xs) n)
                  (append (fn-bch-held-partial b n) xs)))
  :hints (("Goal" :induct (fn-bch-push-list b xs))))

(defthm fn-bch-plain-octetsp-implies-octetsp
  (implies (fn-bch-plain-octetsp xs) (fn-bch-octetsp xs)))

(defthm fn-bch-partial-len-of-push-list
  (implies (and (fn-bch-wfp b) (natp n) (<= n (fn-bch-length b)))
           (equal (fn-bch-partial-len (fn-bch-push-list b xs) n)
                  (+ (fn-bch-partial-len b n) (len xs))))
  :hints (("Goal" :in-theory (enable fn-bch-partial-len))))

(local
 (defun fn-bch-push-list-l-induction (b xs l)
   (if (consp xs)
       (fn-bch-push-list-l-induction (fn-bch-push b (car xs)) (cdr xs) (+ 1 l))
     (list b l))))

(defthm fn-bch-body-okp-of-push-list
  (implies (and (fn-bch-body-okp b n l)
                (fn-bch-plain-octetsp xs)
                (natp l)
                (not (and (equal l 0) (consp xs) (equal (car xs) 46))))
           (fn-bch-body-okp (fn-bch-push-list b xs) n (+ l (len xs))))
  :hints (("Goal" :induct (fn-bch-push-list-l-induction b xs l)
                  :in-theory (disable fn-bch-body-okp))))

(defthm fn-bch-body-okp-line-start
  (implies (fn-bch-body-okp b n 0)
           (equal (fn-bch-partial-len b n) 0))
  :hints (("Goal" :use ((:instance fn-bch-body-okp-facts (l 0))))))

; A whole line received from a line start: its octets, then CR LF.
(defthm fn-bch-body-okp-whole-line
  (implies (and (fn-bch-body-okp b n 0)
                (fn-bch-plain-octetsp xs))
           (let ((b2 (fn-bch-push (fn-bch-push (fn-bch-push-list b xs) 13) 10)))
             (and (fn-bch-body-okp b2 (+ 2 n (len xs)) 0)
                  (equal (fn-bch-held-lines b2 (+ 2 n (len xs)))
                         (append (fn-bch-held-lines b n) (list xs))))))
  :hints (("Goal"
           :use ((:instance fn-bch-body-okp-facts (l 0))
                 (:instance fn-bch-body-okp-line-start)
                 (:instance fn-bch-body-okp-dot)
                 (:instance fn-bch-body-okp-of-push-list
                            (l (if (and (consp xs) (equal (car xs) 46)) 1 0)))
                 (:instance fn-bch-body-okp-line (b (fn-bch-push-list b xs))
                            (l (+ (len xs) (if (and (consp xs) (equal (car xs) 46)) 1 0))))
                 (:instance fn-bch-held-lines-of-line (b (fn-bch-push-list b xs))
                            (l (+ (len xs) (if (and (consp xs) (equal (car xs) 46)) 1 0)))))
           :in-theory (disable fn-bch-body-okp-line-start
                               fn-bch-body-okp-dot fn-bch-body-okp-of-push-list
                               fn-bch-body-okp-line fn-bch-held-lines-of-line
                               fn-bch-body-okp fn-bch-held-lines))))

(defthm fn-bch-body-okp-forward
  (implies (fn-bch-body-okp b n l)
           (and (natp n) (fn-bch-wfp b)))
  :rule-classes :forward-chaining
  :hints (("Goal" :use ((:instance fn-bch-body-okp-facts)))))

(defthm fn-bch-held-lines-true-listp
  (true-listp (fn-bch-held-lines b n))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-bch-held-lines fn-bch-lines-of))))

(in-theory (disable fn-bch-held-lines fn-bch-body-okp fn-bch-length
                    fn-bch-push-of-tail-ok fn-bch-push-list-fills-the-tail
                    fn-bch-lines-rev fn-bch-lines-rev-is-split))
