; fn: the payload arena's BYTE-ARRAY implementation, `fn-arena-bytes' (D27,
; representation wave D; the records freeze, lane records-freeze 2026-09-26;
; derived from one declaration, lane s-vocab 2026-10-07).
;
; This book has two parts.  The LOGICAL SIDE of the arena (`fn-arn-payload-listp',
; `fn-arena$ap', `create-fn-arena$a', the eight `fn-arena$a-*'): a true list of
; octet lists, the model every implementation of the arena is proved against.
; The IMPLEMENTATION is one `def-representation' declaration
; (books/def-representation.lisp, the :octets vocabulary): the concrete stobj
; `fn-arena-bytes$c' (an offset and a length column per handle, one resizable
; `(unsigned-byte 8)' pool holding every payload back to back, the count and
; the fill), the abstraction relation, and every {CORRESPONDENCE}, {PRESERVED}
; and {GUARD-THM} obligation, obtained from ACL2 and closed by the generator's
; one uniform hint over lemmas proved once (books/def-representation-lib.lisp).
; Nothing above this book names `fn-arena-bytes': the books above the arena name
; the GENERIC `fn-arena' (books/payload-arena.lisp, `:attachable t'), whose
; logical side this implementation shares, so that `(attach-stobj fn-arena
; fn-arena-bytes)' would make the generic execute here while every certificate
; above it is the generic's (the consolidation design, section 3).
;
; Exports (logic / exec), positionally the generic's:
;   fn-arena-bytes-count             (len a)                         / the count
;   fn-arena-bytes-payload-len h     (len (nth h a))                 / the length column
;   fn-arena-bytes-get h i           (nth i (nth h a))               / pool[off[h] + i]
;   fn-arena-bytes-payload h         (nth h a)                       / the slice, consed once
;   fn-arena-bytes-seal-list xs      (append a (list xs))            / xs written at the fill point
;   fn-arena-bytes-seal-buffer st    (append a (list st))            / the octet buffer's cells copied
;   fn-arena-bytes-clear             nil                             / count := 0, fill := 0
;   fn-arena-bytes-seal-range a b st (append a (list st[a..b)))     / the cells [A, B) copied, no list
; The two sealing exports of an octet buffer read its cells straight into the
; pool: no octet list is built.
;
; The logical side and its keystones (immutability under seals, no reuse of
; a handle, the relation with a store history) are stated once, over the
; generic, in books/payload-arena.lisp; they hold of this implementation by
; attachment, which is the point.  No `skip-proofs'.

(in-package "ACL2")
(include-book "octets-stobj")
(include-book "records-shape")
(include-book "def-representation")

; -----------------------------------------------------------------------------
; The logical view: a true list of octet lists.

(defun fn-arn-payload-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-cbor-octet-listp (car xs))
           (fn-arn-payload-listp (cdr xs)))
    (null xs)))

(defthm fn-arn-payload-listp-true-listp
  (implies (fn-arn-payload-listp xs) (true-listp xs)))

(defthm fn-arn-payload-listp-of-append-one
  (implies (and (fn-arn-payload-listp a) (fn-cbor-octet-listp xs))
           (fn-arn-payload-listp (append a (list xs)))))

(defthm fn-arn-payload-listp-nth
  (implies (and (fn-arn-payload-listp a) (natp h) (< h (len a)))
           (fn-cbor-octet-listp (nth h a)))
  :hints (("Goal" :in-theory (enable nth))))

; -----------------------------------------------------------------------------
; The logical side: the list of payloads.

(defun fn-arena$ap (x)
  (declare (xargs :guard t))
  (fn-arn-payload-listp x))

(defun create-fn-arena$a ()
  (declare (xargs :guard t))
  nil)

(defun fn-arena$a-count (fn-arena$a)
  (declare (xargs :guard t))
  (len fn-arena$a))

; The guards name the arena only through the exports (single-threadedness
; of an abstract stobj's guards), as octets-stobj's do through its length.
(defun fn-arena$a-payload-len (h fn-arena$a)
  (declare (xargs :guard (and (natp h) (< h (fn-arena$a-count fn-arena$a)))))
  (len (fn-oct-nth h fn-arena$a)))

(defun fn-arena$a-get (h i fn-arena$a)
  (declare (xargs :guard (and (natp h) (< h (fn-arena$a-count fn-arena$a))
                              (natp i) (< i (fn-arena$a-payload-len h fn-arena$a)))))
  (fn-oct-nth i (fn-oct-nth h fn-arena$a)))

(defun fn-arena$a-payload (h fn-arena$a)
  (declare (xargs :guard (and (natp h) (< h (fn-arena$a-count fn-arena$a)))))
  (fn-oct-nth h fn-arena$a))

(defun fn-arena$a-seal-list (xs fn-arena$a)
  (declare (xargs :guard (fn-cbor-octet-listp xs)))
  (fn-oct-snoc fn-arena$a xs))

(defun fn-arena$a-seal-buffer (fn-octets fn-arena$a)
  (declare (xargs :stobjs fn-octets :guard t))
  (fn-oct-snoc fn-arena$a (fn-octets-list fn-octets)))

(defun fn-arena$a-clear (fn-arena$a)
  (declare (xargs :guard t) (ignore fn-arena$a))
  nil)

; The octet buffer's cells [A, B) sealed as one payload (the intern from a
; buffer range: lane open-by-index's fn-obi-seal-range, its book landing in
; batch AQ, is this export's caller).
(defun fn-arena$a-seal-range (a b fn-octets fn-arena$a)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp a) (natp b) (<= a b) (<= b (fn-octets-len fn-octets)))))
  (fn-oct-snoc fn-arena$a (fn-oct-slice-list a b fn-octets)))

; -----------------------------------------------------------------------------
; The slices of an octet buffer, as the arena's logical side reads them.

(local
 (defthm fn-arn-take-of-len
   (implies (true-listp x)
            (equal (take (len x) x) x))))

(defthm fn-arn-slice-list-whole
  (implies (fn-cbor-octet-listp fn-octets)
           (equal (fn-oct-slice-list 0 (len fn-octets) fn-octets)
                  fn-octets))
  :hints (("Goal" :use ((:instance fn-oct-slice-list-is-take-nthcdr
                                   (i 0) (n (len fn-octets)))))))

; A slice of an octet buffer is an octet list: each cell read is an octet.
(local
 (defthm fn-arn-octetp-of-nth
   (implies (and (fn-cbor-octet-listp l) (natp i) (< i (len l)))
            (fn-cbor-octetp (nth i l)))
   :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-arn-slice-list-octets
  (implies (and (fn-cbor-octet-listp fn-octets) (natp a) (natp b) (<= a b)
                (<= b (len fn-octets)))
           (fn-cbor-octet-listp (fn-oct-slice-list a b fn-octets)))
  :hints (("Goal" :induct (fn-oct-slice-list a b fn-octets)
           :in-theory (e/d (fn-oct-slice-list fn-oct-get-is-nth
                            fn-cbor-octet-listp)
                           (fn-oct-slice-list-is-take-nthcdr)))))

; -----------------------------------------------------------------------------
; The implementation, from one declaration.  The logical side above is GIVEN
; (:model), so the generator proves the executables against it and defines
; none of its own.  The theorems the proofs read it through, all about lists:
; the recognizer is the scalar sequence of octet lists, a source buffer is a
; list of octets, and the arena's total readers are `nth', `append' and the
; slice `take' of `nthcdr'.

(local
 (defthm fn-arn-octet-listp-is-adt-octetsp
   (equal (fn-cbor-octet-listp x) (adt-octetsp x))
   :hints (("Goal" :in-theory (enable adt-octetsp fn-cbor-octet-listp fn-cbor-octetp
                                      unsigned-byte-p)))))

(local
 (defthm fn-arn-recognizer-is-the-scalar-sequence
   (equal (fn-arena$ap x) (adt-scalar-seq-p '(:octets) x))
   :hints (("Goal" :in-theory (enable fn-arena$ap fn-arn-payload-listp adt-scalar-seq-p adt-val-okp
                                      fn-arn-octet-listp-is-adt-octetsp)))))

(local
 (defthm fn-arn-source-octets-are-adt-octets
   (implies (fn-octets-p x) (adt-octetsp x))
   :hints (("Goal" :in-theory (enable fn-oct-octets-p-is-octet-listp
                                      fn-arn-octet-listp-is-adt-octetsp)))))

(def-representation fn-arena-bytes (payload :octets) :scalar t :paged nil
  :source fn-octets
  :model (:recognizer fn-arena$ap :creator create-fn-arena$a)
  :lemmas (fn-arn-recognizer-is-the-scalar-sequence fn-arn-octet-listp-is-adt-octetsp
           fn-arn-source-octets-are-adt-octets
           fn-oct-nth-is-nth fn-oct-snoc-is-append fn-oct-list-is-identity
           fn-oct-slice-list-is-take-nthcdr)
  :exports ((count :logic fn-arena$a-count)
            (payload-len :logic fn-arena$a-payload-len)
            (inner-get :as fn-arena-bytes-get :logic fn-arena$a-get)
            (get :as fn-arena-bytes-payload :logic fn-arena$a-payload)
            (append :as fn-arena-bytes-seal-list :logic fn-arena$a-seal-list)
            (seal-buffer :logic fn-arena$a-seal-buffer)
            (clear :logic fn-arena$a-clear)
            (seal-range :logic fn-arena$a-seal-range)))

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:rewrite fn-arn-payload-listp-nth)
                    (:rewrite fn-arn-payload-listp-true-listp)))
