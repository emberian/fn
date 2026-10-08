; fn: the payload reference a paged-checkpoint tape row carries (lane
; s-pck-host, 2026-10-07; STORAGE-PROGRAM section 3.3, D41-STAGE5-ONE-ROW-IMAGE).
;
; A row of the events tape holds the record's metadata and a REF to its payload,
; not the payload octets.  The payloads live durably in the append-only file
; <store>/checkpoint.payloads (books/checkpoint-payloads.lisp, the payload-file
; lane).  This book is the interface both sides build to:
;
;   fn-cpl-refp REF          REF = (OFFSET LEN): OFFSET a natural byte offset into
;                            the payload file, LEN the payload's octet count.
;   fn-cpl-resolve REF FILE  the payload octets REF names in FILE (an octet
;                            list), or :absent when the file ends before
;                            OFFSET + LEN.
;
; The frame digest is checked by the extent digest path when the payload is
; realized; it is not part of the reference.

(in-package "ACL2")
(include-book "store-checkpoint-codec")
(include-book "store-checkpoint-buffer")
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "std/lists/append" :dir :system))

(local (defthm cpl-nthcdr-len-append
  (equal (nthcdr (len a) (append a b)) b)))
(local (defthm cpl-take-len
  (implies (true-listp x) (equal (take (len x) x) x))))
(local (defthm cpl-take-append
  (implies (<= (nfix n) (len a))
           (equal (take n (append a b)) (take n a)))))
(local (defthm cpl-nthcdr-append
  (implies (<= (nfix n) (len a))
           (equal (nthcdr n (append a b)) (append (nthcdr n a) b)))))
(local (defthm cpl-len-nthcdr
  (implies (natp n) (equal (len (nthcdr n x)) (nfix (- (len x) n))))
  :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr)))))
(local (defthm cpl-len-append (equal (len (append a b)) (+ (len a) (len b)))))
(local (defthm cpl-take-len-append
  (implies (true-listp a) (equal (take (len a) (append a b)) a))))

(defun fn-cpl-refp (ref)
  (declare (xargs :guard t))
  (and (true-listp ref) (equal (len ref) 2)
       (natp (car ref)) (natp (cadr ref))))

(defun fn-cpl-ref (offset len)
  (declare (xargs :guard (and (natp offset) (natp len))))
  (list offset len))

(defun fn-cpl-resolve (ref file)
  (declare (xargs :guard (and (fn-cpl-refp ref) (true-listp file))))
  (if (and (fn-cpl-refp ref) (true-listp file)
           (<= (+ (car ref) (cadr ref)) (len file)))
      (take (cadr ref) (nthcdr (car ref) file))
    :absent))

(defthm fn-cpl-refp-of-ref
  (equal (fn-cpl-refp (fn-cpl-ref offset len)) (and (natp offset) (natp len))))

(defthm fn-cpl-resolve-of-ref-in-append
  ; A payload appended after PRE resolves to itself, whatever follows.
  (implies (and (true-listp pre) (true-listp payload) (true-listp post))
           (equal (fn-cpl-resolve (fn-cpl-ref (len pre) (len payload))
                                  (append pre payload post))
                  payload))
  :hints (("Goal" :in-theory (e/d (fn-cpl-ref) (cpl-nthcdr-append cpl-take-append))
           :do-not-induct t)))

(defthm fn-cpl-resolve-ignores-a-tail
  ; Octets past OFFSET + LEN (an uncommitted tail) do not change the answer.
  (implies (and (fn-cpl-refp ref) (true-listp file) (true-listp tail)
                (<= (+ (car ref) (cadr ref)) (len file)))
           (equal (fn-cpl-resolve ref (append file tail))
                  (fn-cpl-resolve ref file)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cpl-refp) (cpl-nthcdr-append cpl-take-append))
           :use ((:instance cpl-nthcdr-append (n (car ref)) (a file) (b tail))
                 (:instance cpl-take-append (n (cadr ref)) (a (nthcdr (car ref) file)) (b tail))
                 (:instance cpl-len-nthcdr (n (car ref)) (x file))))))

; The frame a payload takes in the file (books/checkpoint-payloads.lisp): one
; fn-scc frame, a 37-octet header, the payload, a 32-octet trailer (the digest
; the extent path verifies).  A ref points at the PAYLOAD, 37 octets into its
; frame.  Frames of consecutive payloads lie end to end.
(defconst *fn-cpl-header-octets* 37)
(defconst *fn-cpl-trailer-octets* 32)

(defun fn-cpl-frame-octets (n)
  (declare (xargs :guard t))
  (+ *fn-cpl-header-octets* (nfix n) *fn-cpl-trailer-octets*))

; The frame's trailer as four u64 words, big-endian: the tape row's form, a
; concrete function of the payload (the frame digest of header ++ payload,
; packed).  Defined here, below books/checkpoint-payloads.lisp, so the paged
; checkpoint reaches the implementation itself: nothing is constrained.

; A payload the file can hold: an octet list whose length fits a frame header.
(defun fn-cpl-payloadp (p)
  (declare (xargs :guard t))
  (and (true-listp p) (fn-scc-octet-listp p) (< (+ 1 (len p)) *fn-scc-u64-bound*)))

(local
 (defthm cpl-u64-octets (fn-scc-octet-listp (fn-scc-u64 n k))
   :hints (("Goal" :in-theory (enable fn-scc-u64 fn-scc-octetp)))))

(local
 (defthm cpl-octets-append
   (implies (and (fn-scc-octet-listp a) (fn-scc-octet-listp b))
            (fn-scc-octet-listp (append a b)))
   :hints (("Goal" :induct (fn-scc-octet-listp a)
            :in-theory (e/d (fn-scc-octet-listp) (fn-scc-octet-listp-facts))))))

(local
 (defthm cpl-header-octets (fn-scc-octet-listp (fn-scc-header 0 1 l 0))
   :hints (("Goal" :in-theory (e/d (fn-scc-header fn-scc-octetp fn-scc-octet-listp)
                                   (fn-scc-octet-listp-facts))
            :use ((:instance cpl-u64-octets (n l) (k 8))
                  (:instance cpl-octets-append (a (fn-scc-u64 l 8))
                             (b '(0 0 0 0 0 0 0 0))))))))

(local
 (defthm cpl-cbor-octets
   (implies (fn-scc-octet-listp x) (fn-cbor-octet-listp x))
   :hints (("Goal" :induct (fn-scc-octet-listp x)
            :in-theory (e/d (fn-scc-octet-listp fn-sccb-scc-octetp-is-cbor-octetp)
                            (fn-scc-octet-listp-facts))))))

(local
 (defthm cpl-cbor-scc
   (implies (fn-cbor-octet-listp x) (fn-scc-octet-listp x))
   :hints (("Goal" :induct (fn-cbor-octet-listp x)
            :in-theory (e/d (fn-scc-octet-listp fn-cbor-octet-listp
                                                fn-sccb-scc-octetp-is-cbor-octetp)
                            (fn-scc-octet-listp-facts))))))

(local
 (defthm cpl-trailer-facts
   (implies (fn-cbor-octet-listp x)
            (and (fn-scc-octet-listp (fn-frame-trailer x))
                 (equal (len (fn-frame-trailer x)) 32)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-frame-trailer-is-a-digest (octets x))
                  (:instance cpl-cbor-scc (x (fn-frame-trailer x))))
            :in-theory (e/d (fn-frame-digestp)
                            (fn-frame-trailer-is-a-digest cpl-cbor-scc))))))

(local
 (defthm cpl-seal-facts-gen
   (implies (and (fn-scc-octet-listp q) (fn-scc-octet-listp h) (fn-scc-octet-listp p))
            (and (fn-scc-octet-listp (fn-scc-seal q h p))
                 (equal (len (fn-scc-seal q h p)) 32)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance cpl-trailer-facts (x (append q h p)))
                  (:instance cpl-cbor-octets (x (append q h p)))
                  (:instance cpl-octets-append (a h) (b p))
                  (:instance cpl-octets-append (a q) (b (append h p))))
            :in-theory (e/d (fn-scc-seal)
                            (cpl-trailer-facts cpl-cbor-octets cpl-octets-append))))))

(local
 (defthm cpl-seal-facts
   (implies (and (fn-scc-octet-listp h) (fn-scc-octet-listp p))
            (and (fn-scc-octet-listp (fn-scc-seal nil h p))
                 (equal (len (fn-scc-seal nil h p)) 32)))
   :hints (("Goal" :use ((:instance cpl-seal-facts-gen (q nil)))))))

(local
 (defthm cpl-take-octets
   (implies (and (fn-scc-octet-listp x) (natp n) (<= n (len x)))
            (fn-scc-octet-listp (take n x)))
   :hints (("Goal" :induct (take n x)
            :in-theory (e/d (take fn-scc-octet-listp) (fn-scc-octet-listp-facts))))))

; The frame's 32-octet trailer: the digest over the header
; and the payload.  A function of the payload alone (index 0 of 1, sequence 0).
(defun fn-cpl-trailer (p)
  (declare (xargs :guard (true-listp p) :verify-guards nil))
  (fn-scc-seal nil (fn-scc-header 0 1 (len p) 0) p))

; -----------------------------------------------------------------------------
; 7. The trailer.

(defthm fn-cpl-trailer-shape
  (implies (fn-cpl-payloadp p)
           (and (fn-scc-octet-listp (fn-cpl-trailer p))
                (equal (len (fn-cpl-trailer p)) 32)))
  :hints (("Goal" :use ((:instance cpl-seal-facts (h (fn-scc-header 0 1 (len p) 0)) (p p)))
           :in-theory (e/d (fn-cpl-trailer fn-cpl-payloadp)
                           (cpl-seal-facts fn-scc-header fn-scc-seal)))))

; -----------------------------------------------------------------------------
; 8. The trailer as four u64 words, big-endian (the tape row's form).
; Word i is octets [8i, 8i+8) of the trailer, most significant octet first.

(defun fn-cpl-trailer-word-count () (declare (xargs :guard t)) 4)

(defun fn-cpl-be-fold (xs acc)
  (declare (xargs :guard (and (true-listp xs) (natp acc))))
  (if (consp xs)
      (fn-cpl-be-fold (cdr xs) (+ (* 256 (nfix acc)) (nfix (car xs))))
    (nfix acc)))

(defun fn-cpl-be-octets (w n)
  (declare (xargs :guard (and (natp w) (natp n))))
  (if (zp n)
      nil
    (append (fn-cpl-be-octets (floor (nfix w) 256) (1- n)) (list (mod (nfix w) 256)))))

(defun fn-cpl-pack-words (tr n)
  (declare (xargs :guard (and (true-listp tr) (natp n))))
  (if (zp n)
      nil
    (cons (fn-cpl-be-fold (take 8 tr) 0) (fn-cpl-pack-words (nthcdr 8 tr) (1- n)))))

(defun fn-cpl-unpack-words (ws)
  (declare (xargs :guard (true-listp ws)))
  (if (consp ws)
      (append (fn-cpl-be-octets (nfix (car ws)) 8) (fn-cpl-unpack-words (cdr ws)))
    nil))

(defun fn-cpl-trailer-words-impl (p)
  (declare (xargs :guard (fn-cpl-payloadp p) :verify-guards nil))
  (fn-cpl-pack-words (fn-cpl-trailer p) (fn-cpl-trailer-word-count)))

(defun fn-cpl-ub64-listp (ws)
  (declare (xargs :guard t))
  (if (consp ws)
      (and (unsigned-byte-p 64 (car ws)) (fn-cpl-ub64-listp (cdr ws)))
    (null ws)))

(local
 (defthm cpl-be-octets-snoc
   (implies (and (natp v) (natp x) (< x 256) (natp n))
            (equal (fn-cpl-be-octets (+ (* 256 v) x) (+ 1 n))
                   (append (fn-cpl-be-octets v n) (list x))))
   :hints (("Goal" :expand ((fn-cpl-be-octets (+ (* 256 v) x) (+ 1 n)))))))

(local (defun cpl-ind3 (xs acc k)
         (declare (xargs :verify-guards nil))
         (if (consp xs)
             (cpl-ind3 (cdr xs) (+ (* 256 (nfix acc)) (nfix (car xs))) (+ 1 (nfix k)))
           (list acc k))))

(local
 (defthm cpl-be-fold-roundtrip
   (implies (and (fn-scc-octet-listp xs) (natp acc) (natp k))
            (equal (fn-cpl-be-octets (fn-cpl-be-fold xs acc) (+ k (len xs)))
                   (append (fn-cpl-be-octets acc k) xs)))
   :hints (("Goal" :induct (cpl-ind3 xs acc k)
            :in-theory (e/d (fn-scc-octet-listp fn-scc-octetp)
                            (fn-cpl-be-octets fn-scc-octet-listp-facts)))
           (and stable-under-simplificationp
                '(:use ((:instance cpl-be-octets-snoc (v acc) (x (car xs)) (n k))))))))

(local (defun cpl-ind5 (xs acc b)
         (declare (xargs :verify-guards nil))
         (if (consp xs)
             (cpl-ind5 (cdr xs) (+ (* 256 (nfix acc)) (nfix (car xs))) (* 256 (nfix b)))
           (list acc b))))

(local
 (defthm cpl-be-fold-bound
   (implies (and (fn-scc-octet-listp xs) (natp acc) (posp b) (< acc b))
            (< (fn-cpl-be-fold xs acc) (* b (expt 256 (len xs)))))
   :hints (("Goal" :induct (cpl-ind5 xs acc b)
            :in-theory (e/d (fn-scc-octet-listp fn-scc-octetp) (fn-scc-octet-listp-facts))))))

(local
 (defthm cpl-slice
   (implies (and (fn-scc-octet-listp xs) (equal (len xs) 8))
            (equal (fn-cpl-be-octets (fn-cpl-be-fold xs 0) 8) xs))
   :hints (("Goal" :use ((:instance cpl-be-fold-roundtrip (acc 0) (k 0)))
            :in-theory (disable cpl-be-fold-roundtrip)))))

(local (defthm cpl-append-take-nthcdr
         (implies (and (natp n) (<= n (len x))) (equal (append (take n x) (nthcdr n x)) x))))

(local (defthm cpl-nthcdr-octets
         (implies (fn-scc-octet-listp x) (fn-scc-octet-listp (nthcdr n x)))))

(local (defthm cpl-len-nthcdr2
         (implies (natp k) (equal (len (nthcdr k x)) (nfix (- (len x) k))))
         :hints (("Goal" :induct (nthcdr k x)))))

(local (defthm cpl-len-take (implies (and (natp n) (<= n (len x))) (equal (len (take n x)) n))))

(local
 (defthm cpl-slice-at
   (implies (and (fn-scc-octet-listp tr) (natp k) (<= (+ k 8) (len tr)))
            (equal (fn-cpl-be-octets (fn-cpl-be-fold (take 8 (nthcdr k tr)) 0) 8)
                   (take 8 (nthcdr k tr))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance cpl-slice (xs (take 8 (nthcdr k tr))))
                  (:instance cpl-take-octets (x (nthcdr k tr)) (n 8))
                  (:instance cpl-nthcdr-octets (x tr) (n k))
                  (:instance cpl-len-nthcdr2 (x tr))
                  (:instance cpl-len-take (n 8) (x (nthcdr k tr))))
            :in-theory (disable cpl-slice cpl-take-octets cpl-len-nthcdr2 cpl-nthcdr-octets
                                cpl-len-take)))))

(local
 (defthm cpl-len0
   (implies (and (fn-scc-octet-listp tr) (equal (len tr) 0)) (equal tr nil))
   :hints (("Goal" :in-theory (enable fn-scc-octet-listp)))
   :rule-classes nil))

(local
 (defthm cpl-pack-unpack
   (implies (and (fn-scc-octet-listp tr) (natp n) (equal (len tr) (* 8 n)))
            (equal (fn-cpl-unpack-words (fn-cpl-pack-words tr n)) tr))
   :hints (("Goal" :induct (fn-cpl-pack-words tr n) :in-theory (disable cpl-slice-at))
           (and stable-under-simplificationp
                '(:use ((:instance cpl-slice-at (k 0))
                        (:instance cpl-append-take-nthcdr (n 8) (x tr))
                        (:instance cpl-nthcdr-octets (x tr) (n 8))
                        (:instance cpl-len-nthcdr2 (x tr) (k 8))
                        (:instance cpl-len0))
                  :in-theory (disable cpl-slice-at cpl-append-take-nthcdr cpl-nthcdr-octets
                                      cpl-len-nthcdr2))))))

(local
 (defthm cpl-pack-ub64
   (implies (and (fn-scc-octet-listp tr) (natp n) (equal (len tr) (* 8 n)))
            (and (fn-cpl-ub64-listp (fn-cpl-pack-words tr n))
                 (equal (len (fn-cpl-pack-words tr n)) n)))
   :hints (("Goal" :induct (fn-cpl-pack-words tr n) :in-theory (disable cpl-be-fold-bound))
           (and stable-under-simplificationp
                '(:use ((:instance cpl-be-fold-bound (xs (take 8 tr)) (acc 0) (b 1))
                        (:instance cpl-take-octets (x tr) (n 8))
                        (:instance cpl-nthcdr-octets (x tr) (n 8))
                        (:instance cpl-len-nthcdr2 (x tr) (k 8))
                        (:instance cpl-len-take (x tr) (n 8)))
                  :in-theory (e/d (unsigned-byte-p integer-range-p)
                                  (cpl-be-fold-bound cpl-take-octets cpl-nthcdr-octets
                                                     cpl-len-nthcdr2 cpl-len-take)))))))

; Unpacking the words gives the trailer.
(defthm fn-cpl-trailer-words-pack
  (implies (fn-cpl-payloadp p)
           (equal (fn-cpl-unpack-words (fn-cpl-trailer-words-impl p)) (fn-cpl-trailer p)))
  :hints (("Goal" :use (fn-cpl-trailer-shape
                        (:instance cpl-pack-unpack (tr (fn-cpl-trailer p))
                                   (n (fn-cpl-trailer-word-count))))
           :in-theory (e/d (fn-cpl-trailer-word-count fn-cpl-trailer-words-impl)
                           (cpl-pack-unpack fn-cpl-trailer-shape fn-cpl-trailer
                                            fn-cpl-pack-words fn-cpl-unpack-words)))))

; The shape the paged checkpoint's tape row relies on: four u64 words.
(defthm fn-cpl-trailer-words-impl-shape
  (implies (fn-cpl-payloadp p)
           (and (true-listp (fn-cpl-trailer-words-impl p))
                (consp (fn-cpl-trailer-words-impl p))
                (equal (len (fn-cpl-trailer-words-impl p)) 4)
                (unsigned-byte-p 64 (car (fn-cpl-trailer-words-impl p)))
                (unsigned-byte-p 64 (cadr (fn-cpl-trailer-words-impl p)))
                (unsigned-byte-p 64 (caddr (fn-cpl-trailer-words-impl p)))
                (unsigned-byte-p 64 (cadddr (fn-cpl-trailer-words-impl p)))))
  :hints (("Goal" :use (fn-cpl-trailer-shape
                        (:instance cpl-pack-ub64 (tr (fn-cpl-trailer p))
                                   (n (fn-cpl-trailer-word-count))))
           :in-theory (e/d (fn-cpl-trailer-word-count fn-cpl-trailer-words-impl fn-cpl-ub64-listp)
                           (cpl-pack-ub64 fn-cpl-trailer-shape fn-cpl-trailer
                                          fn-cpl-pack-words)))))

; -----------------------------------------------------------------------------
; 9. The executable: the frames written through the buffer.  No octet list is
; built for the file: the header (37 octets) and the trailer (32) are the small
; lists, the payload is appended as given (the arena-to-buffer copy without a
; transient list waits on the arena's inner-octet read, as
; fn-scka-append-src does).

(verify-guards fn-cpl-trailer)

(verify-guards fn-cpl-trailer-words-impl
  :hints (("Goal" :use (fn-cpl-trailer-shape)
           :in-theory (e/d (fn-cpl-trailer-word-count) (fn-cpl-trailer-shape fn-cpl-trailer)))))
