; fn: the payload arena, an abstract stobj (D27, representation wave D).
;
; The heap census (planning/evidence/rep-heap-2026-09-25.md) found the one
; long-lived copy of every article: the store record's payload, an octet
; list, sixteen bytes per octet, shared by the archive, the views and the
; trie.  The octet buffer (books/octets-stobj.lisp) took the transient copies
; off the served POST; the record's own copy stays a list because the record
; is a value of the logical store.  This book is the retained payloads'
; concrete home: an abstract stobj `fn-arena' whose logical value is the
; list of sealed payloads, oldest first, each an octet list, and whose
; executable is one resizable `(unsigned-byte 8)' array holding every
; payload back to back, with an offset and a size per handle.  A handle is
; a position in the logical list.  One byte per payload octet, sixteen per
; handle.
;
; Exports (logic / exec):
;   fn-arena-count             (len a)                         / the count
;   fn-arena-payload-len h     (len (nth h a))                 / size[h]
;   fn-arena-get h i           (nth i (nth h a))               / buf[off[h] + i]
;   fn-arena-payload h         (nth h a)                       / the slice, consed once
;   fn-arena-seal-list xs      (append a (list xs))            / xs written at the fill point,
;                                                                 a new handle (the old count)
;   fn-arena-seal-buffer st    (append a (list st))            / the octet buffer's cells copied
;                                                                 at the fill point (no list)
;   fn-arena-clear             nil                             / count := 0, fill := 0
;
; The abstraction relation `fn-arena$corr': the concrete object is well
; formed, the count and the fill are within their arrays, every handle's
; range lies below the fill, and the slices buf[off[h]..off[h]+size[h])
; for h below the count, in order, are the logical list.  It is established
; by the creator and preserved by every export; the {CORRESPONDENCE},
; {PRESERVED} and {GUARD-THM} theorems below are stated exactly as
; `defabsstobj-missing-events' prints them and proved before the
; `defabsstobj' event.  No `skip-proofs'.
;
; What the arena guarantees, as theorems over the logical view:
;   - a sealed handle is immutable: `fn-arena-seal-keeps-sealed' (one seal)
;     and `fn-arena-seals-keep-sealed' (any sequence): a reader that pinned
;     handle h before a seal reads the same octets after it;
;   - a handle is never reused: a seal's new handle is the old count and
;     denotes the sealed octets (`fn-arena-seal-new-handle'), and the count
;     only grows (`fn-arena-seal-count');
;   - nothing removes a payload: the arena has no delete export, so no
;     reference held by a pinned reader, a feed, a consumer or a BP job can
;     dangle across a seal (the reclaim interface: a reclaimed record's
;     tombstone is a new seal, the old handle stays valid until the next
;     open rebuilds the arena from the retained records).
;   `fn-arn-store-corr' is the relation between an arena and a store
;   history: the arena is the history's payloads oldest first.  Commit
;   (a seal of the finished record's payload, `fn-arn-store-corr-of-commit')
;   and open (a seal per retained record, oldest first, from the empty
;   arena, `fn-arn-store-corr-of-open') establish the same relation.
;
; The host boundary: `fn-arena-seal-buffer' is the seal the served POST
; will make at the finish, from the octet buffer the attempt filled
; (host/native/owner.lisp fnn-owner-attempt); no host code reaches the
; array.  This book is the base; the record's payload field becomes a
; handle in the representation lane that follows
; (planning/evidence/rep-wave-d-2026-09-25.md, the design section).

(in-package "ACL2")
(include-book "octets-stobj")
(include-book "records-shape")

; -----------------------------------------------------------------------------
; The concrete stobj: the byte array, the offset and size per handle, the
; count of sealed handles and the fill point.

(defstobj fn-arena$c
  (fn-arena$c-buf :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t)
  (fn-arena$c-off :type (array (integer 0 *) (0)) :initially 0 :resizable t)
  (fn-arena$c-size :type (array (integer 0 *) (0)) :initially 0 :resizable t)
  (fn-arena$c-count :type (integer 0 *) :initially 0)
  (fn-arena$c-fill :type (integer 0 *) :initially 0)
  :inline t)

; The byte array's recognizer is the octet buffer's, so that book's array
; lemmas apply here.
(defthm fn-arn-bufp-is-octets-bufp
  (equal (fn-arena$c-bufp x) (fn-octets$c-bufp x)))

(local (in-theory (disable fn-arena$c-bufp)))

; The handle arrays' recognizers: a cell is a natural; a write of a natural
; and a resize keep them.
(defthm fn-arn-offp-cell
  (implies (and (fn-arena$c-offp off) (natp k) (< k (len off)))
           (natp (nth k off)))
  :hints (("Goal" :in-theory (enable nth))))

(defthm fn-arn-sizep-cell
  (implies (and (fn-arena$c-sizep size) (natp k) (< k (len size)))
           (natp (nth k size)))
  :hints (("Goal" :in-theory (enable nth))))

(defthm fn-arn-offp-of-update-nth
  (implies (and (fn-arena$c-offp off) (natp k) (< k (len off)) (natp v))
           (fn-arena$c-offp (update-nth k v off)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm fn-arn-sizep-of-update-nth
  (implies (and (fn-arena$c-sizep size) (natp k) (< k (len size)) (natp v))
           (fn-arena$c-sizep (update-nth k v size)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm fn-arn-offp-of-resize-list
  (implies (fn-arena$c-offp off)
           (fn-arena$c-offp (resize-list off m 0))))

(defthm fn-arn-sizep-of-resize-list
  (implies (fn-arena$c-sizep size)
           (fn-arena$c-sizep (resize-list size m 0))))


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
; The abstraction: the slices buf[off[h]..off[h]+size[h]) for h in [h, count),
; and the range invariant every handle satisfies.  Both are lemmas about
; lists (the arrays as the lists they are).

(defun fn-arn-slices (h count off size buf)
  (declare (xargs :guard t :verify-guards nil :measure (nfix (- (nfix count) (nfix h)))))
  (if (or (not (natp h)) (not (natp count)) (<= count h))
      nil
    (cons (fn-oct-list-from (nth h off) (+ (nth h off) (nth h size)) buf)
          (fn-arn-slices (1+ h) count off size buf))))

(defun fn-arn-rangesp (h count off size top)
  (declare (xargs :guard t :verify-guards nil :measure (nfix (- (nfix count) (nfix h)))))
  (if (or (not (natp h)) (not (natp count)) (<= count h))
      t
    (and (natp (nth h off)) (natp (nth h size))
         (<= (+ (nth h off) (nth h size)) top)
         (fn-arn-rangesp (1+ h) count off size top))))

(defthm fn-arn-len-of-slices
  (equal (len (fn-arn-slices h count off size buf))
         (if (and (natp h) (natp count) (< h count)) (- count h) 0)))

(defthm fn-arn-true-listp-of-slices
  (true-listp (fn-arn-slices h count off size buf)))

(local
 (defun fn-arn-ind-hk (h k count)
   (declare (xargs :measure (nfix (- (nfix count) (nfix h)))))
   (if (or (not (natp h)) (not (natp count)) (<= count h))
       (list h k)
     (fn-arn-ind-hk (1+ h) (1- k) count))))

(defthm fn-arn-nth-of-slices
  (implies (and (natp h) (natp count) (natp k) (< (+ h k) count))
           (equal (nth k (fn-arn-slices h count off size buf))
                  (fn-oct-list-from (nth (+ h k) off)
                                    (+ (nth (+ h k) off) (nth (+ h k) size))
                                    buf)))
  :hints (("Goal" :induct (fn-arn-ind-hk h k count))))

(defthm fn-arn-slices-empty
  (implies (and (natp h) (natp count) (<= count h))
           (equal (fn-arn-slices h count off size buf) nil)))

(defthm fn-arn-rangesp-empty
  (implies (and (natp h) (natp count) (<= count h))
           (equal (fn-arn-rangesp h count off size top) t)))

; The split of the slices at the last handle.  Not a rewrite rule.
(defthm fn-arn-slices-snoc
  (implies (and (natp h) (natp n) (<= h n))
           (equal (fn-arn-slices h (1+ n) off size buf)
                  (append (fn-arn-slices h n off size buf)
                          (list (fn-oct-list-from (nth n off) (+ (nth n off) (nth n size)) buf)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-arn-slices h n off size buf))))

(defthm fn-arn-rangesp-snoc
  (implies (and (natp h) (natp n) (<= h n))
           (equal (fn-arn-rangesp h (1+ n) off size top)
                  (and (fn-arn-rangesp h n off size top)
                       (natp (nth n off)) (natp (nth n size))
                       (<= (+ (nth n off) (nth n size)) top))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-arn-rangesp h n off size top))))

(defthm fn-arn-rangesp-at
  (implies (and (fn-arn-rangesp h count off size top)
                (natp h) (natp count) (natp k) (<= h k) (< k count))
           (and (natp (nth k off)) (natp (nth k size))
                (<= (+ (nth k off) (nth k size)) top)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-arn-rangesp h count off size top))))

(defthm fn-arn-rangesp-fill-monotone
  (implies (and (fn-arn-rangesp h count off size top) (<= top fill2))
           (fn-arn-rangesp h count off size fill2)))

; The handle arrays: a write at or past the count, and a resize keeping
; the count, change no slice and no range.

(defthm fn-arn-slices-of-update-off-outside
  (implies (and (natp count) (natp j) (<= count j))
           (equal (fn-arn-slices h count (update-nth j v off) size buf)
                  (fn-arn-slices h count off size buf))))

(defthm fn-arn-slices-of-update-size-outside
  (implies (and (natp count) (natp j) (<= count j))
           (equal (fn-arn-slices h count off (update-nth j v size) buf)
                  (fn-arn-slices h count off size buf))))

(defthm fn-arn-rangesp-of-update-off-outside
  (implies (and (natp count) (natp j) (<= count j))
           (equal (fn-arn-rangesp h count (update-nth j v off) size top)
                  (fn-arn-rangesp h count off size top))))

(defthm fn-arn-rangesp-of-update-size-outside
  (implies (and (natp count) (natp j) (<= count j))
           (equal (fn-arn-rangesp h count off (update-nth j v size) top)
                  (fn-arn-rangesp h count off size top))))

(defthm fn-arn-slices-of-resize-off
  (implies (and (natp count) (<= count (len off)) (<= count (nfix m)))
           (equal (fn-arn-slices h count (resize-list off m d) size buf)
                  (fn-arn-slices h count off size buf))))

(defthm fn-arn-slices-of-resize-size
  (implies (and (natp count) (<= count (len size)) (<= count (nfix m)))
           (equal (fn-arn-slices h count off (resize-list size m d) buf)
                  (fn-arn-slices h count off size buf))))

(defthm fn-arn-rangesp-of-resize-off
  (implies (and (natp count) (<= count (len off)) (<= count (nfix m)))
           (equal (fn-arn-rangesp h count (resize-list off m d) size top)
                  (fn-arn-rangesp h count off size top))))

(defthm fn-arn-rangesp-of-resize-size
  (implies (and (natp count) (<= count (len size)) (<= count (nfix m)))
           (equal (fn-arn-rangesp h count off (resize-list size m d) top)
                  (fn-arn-rangesp h count off size top))))

; The byte array: a write at or past the fill, and a resize keeping the
; fill, change no slice, because every range lies below the fill.

(defthm fn-arn-slices-of-update-buf-outside
  (implies (and (fn-arn-rangesp h count off size top) (natp j) (<= top j))
           (equal (fn-arn-slices h count off size (update-nth j v buf))
                  (fn-arn-slices h count off size buf))))

(defthm fn-arn-slices-of-resize-buf
  (implies (and (fn-arn-rangesp h count off size top)
                (<= top (len buf)) (<= top (nfix m)))
           (equal (fn-arn-slices h count off size (resize-list buf m d))
                  (fn-arn-slices h count off size buf))))

(defthm fn-arn-payload-listp-of-slices
  (implies (and (fn-octets$c-bufp buf) (fn-arn-rangesp h count off size top)
                (<= top (len buf)))
           (fn-arn-payload-listp (fn-arn-slices h count off size buf))))

(local (in-theory (disable fn-oct-list-from fn-arn-slices fn-arn-rangesp)))

; -----------------------------------------------------------------------------
; The executable reader: buf[i..n) consed from the top down in a tail call.

(defun fn-arn-buf-list-down (i n acc fn-arena$c)
  (declare (xargs :stobjs fn-arena$c
                  :guard (and (natp i) (natp n) (<= i n)
                              (<= n (fn-arena$c-buf-length fn-arena$c))
                              (true-listp acc))
                  :measure (nfix (- (nfix n) (nfix i)))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      acc
    (fn-arn-buf-list-down i (1- n)
                          (cons (fn-arena$c-bufi (1- n) fn-arena$c) acc)
                          fn-arena$c)))

(local
 (defthm fn-arn-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(defthm fn-arn-buf-list-down-is-list-from
  (implies (and (natp i) (natp n) (<= i n) (true-listp acc))
           (equal (fn-arn-buf-list-down i n acc fn-arena$c)
                  (append (fn-oct-list-from i n (nth 0 fn-arena$c)) acc)))
  :hints (("Goal" :induct (fn-arn-buf-list-down i n acc fn-arena$c))
          ("Subgoal *1/2" :use ((:instance fn-oct-list-from-snoc
                                           (i i) (n (1- n)) (buf (nth 0 fn-arena$c)))))))

; -----------------------------------------------------------------------------
; The exec functions.

(defun fn-arena$c-wfp (fn-arena$c)
  ; The executable invariant: the fill and the count are within their arrays.
  (declare (xargs :stobjs fn-arena$c))
  (and (<= (fn-arena$c-fill fn-arena$c) (fn-arena$c-buf-length fn-arena$c))
       (<= (fn-arena$c-count fn-arena$c) (fn-arena$c-off-length fn-arena$c))
       (<= (fn-arena$c-count fn-arena$c) (fn-arena$c-size-length fn-arena$c))))

(defun fn-arena$c-payload-len (h fn-arena$c)
  (declare (xargs :stobjs fn-arena$c
                  :guard (and (natp h) (< h (fn-arena$c-count fn-arena$c))
                              (fn-arena$c-wfp fn-arena$c))))
  (fn-arena$c-sizei h fn-arena$c))

(defun fn-arena$c-get (h i fn-arena$c)
  (declare (xargs :stobjs fn-arena$c
                  :guard (and (fn-arena$c-wfp fn-arena$c)
                              (natp h) (< h (fn-arena$c-count fn-arena$c))
                              (natp i)
                              (natp (fn-arena$c-offi h fn-arena$c))
                              (natp (fn-arena$c-sizei h fn-arena$c))
                              (< i (fn-arena$c-sizei h fn-arena$c))
                              (<= (+ (fn-arena$c-offi h fn-arena$c) (fn-arena$c-sizei h fn-arena$c))
                                  (fn-arena$c-fill fn-arena$c)))))
  (fn-arena$c-bufi (+ (fn-arena$c-offi h fn-arena$c) i) fn-arena$c))

(defun fn-arena$c-payload (h fn-arena$c)
  (declare (xargs :stobjs fn-arena$c
                  :guard (and (fn-arena$c-wfp fn-arena$c)
                              (natp h) (< h (fn-arena$c-count fn-arena$c))
                              (natp (fn-arena$c-offi h fn-arena$c))
                              (natp (fn-arena$c-sizei h fn-arena$c))
                              (<= (+ (fn-arena$c-offi h fn-arena$c) (fn-arena$c-sizei h fn-arena$c))
                                  (fn-arena$c-fill fn-arena$c)))))
  (fn-arn-buf-list-down (fn-arena$c-offi h fn-arena$c)
                        (+ (fn-arena$c-offi h fn-arena$c) (fn-arena$c-sizei h fn-arena$c))
                        nil fn-arena$c))

(defun fn-arena$c-clear (fn-arena$c)
  (declare (xargs :stobjs fn-arena$c))
  (let ((fn-arena$c (update-fn-arena$c-count 0 fn-arena$c)))
    (update-fn-arena$c-fill 0 fn-arena$c)))

; One octet at the fill point, doubling the array when full.
(defun fn-arn-write-octet (o fn-arena$c)
  (declare (xargs :stobjs fn-arena$c
                  :guard (and (fn-cbor-octetp o)
                              (<= (fn-arena$c-fill fn-arena$c) (fn-arena$c-buf-length fn-arena$c)))))
  (let* ((n (fn-arena$c-fill fn-arena$c))
         (fn-arena$c (if (< n (fn-arena$c-buf-length fn-arena$c))
                         fn-arena$c
                       (resize-fn-arena$c-buf (max 1024 (* 2 n)) fn-arena$c)))
         (fn-arena$c (update-fn-arena$c-bufi n o fn-arena$c)))
    (update-fn-arena$c-fill (1+ n) fn-arena$c)))

(defun fn-arn-write (xs fn-arena$c)
  ; XS at the fill point, one write per octet.
  (declare (xargs :stobjs fn-arena$c
                  :guard (and (fn-cbor-octet-listp xs)
                              (<= (fn-arena$c-fill fn-arena$c) (fn-arena$c-buf-length fn-arena$c)))))
  (if (atom xs)
      fn-arena$c
    (let ((fn-arena$c (fn-arn-write-octet (car xs) fn-arena$c)))
      (fn-arn-write (cdr xs) fn-arena$c))))

(defun fn-arn-write-buffer (i n fn-octets fn-arena$c)
  ; The octet buffer's cells [i, n) at the fill point, read in place.
  (declare (xargs :stobjs (fn-octets fn-arena$c)
                  :guard (and (natp i) (natp n) (<= n (fn-octets-len fn-octets))
                              (<= (fn-arena$c-fill fn-arena$c) (fn-arena$c-buf-length fn-arena$c)))
                  :measure (nfix (- (nfix n) (nfix i)))))
  (if (or (not (natp i)) (not (natp n)) (<= n i))
      fn-arena$c
    (let ((fn-arena$c (fn-arn-write-octet (fn-octets-get i fn-octets) fn-arena$c)))
      (fn-arn-write-buffer (1+ i) n fn-octets fn-arena$c))))

(defun fn-arn-seal-entry (start fn-arena$c)
  ; The bytes written at [start, fill) become the next handle.
  (declare (xargs :stobjs fn-arena$c
                  :guard (and (natp start) (<= start (fn-arena$c-fill fn-arena$c))
                              (<= (fn-arena$c-count fn-arena$c) (fn-arena$c-off-length fn-arena$c))
                              (<= (fn-arena$c-count fn-arena$c) (fn-arena$c-size-length fn-arena$c)))))
  (let* ((h (fn-arena$c-count fn-arena$c))
         (fn-arena$c (if (< h (fn-arena$c-off-length fn-arena$c))
                         fn-arena$c
                       (resize-fn-arena$c-off (max 64 (* 2 h)) fn-arena$c)))
         (fn-arena$c (if (< h (fn-arena$c-size-length fn-arena$c))
                         fn-arena$c
                       (resize-fn-arena$c-size (max 64 (* 2 h)) fn-arena$c)))
         (fn-arena$c (update-fn-arena$c-offi h start fn-arena$c))
         (fn-arena$c (update-fn-arena$c-sizei h (- (fn-arena$c-fill fn-arena$c) start) fn-arena$c)))
    (update-fn-arena$c-count (1+ h) fn-arena$c)))

(defun fn-arena$c-seal-list (xs fn-arena$c)
  ; Guards verified below, once the write's effect on the fill is a lemma.
  (declare (xargs :stobjs fn-arena$c
                  :guard (and (fn-cbor-octet-listp xs) (fn-arena$c-wfp fn-arena$c))
                  :verify-guards nil))
  (let* ((start (fn-arena$c-fill fn-arena$c))
         (fn-arena$c (fn-arn-write xs fn-arena$c)))
    (fn-arn-seal-entry start fn-arena$c)))

(defun fn-arena$c-seal-buffer (fn-octets fn-arena$c)
  (declare (xargs :stobjs (fn-octets fn-arena$c)
                  :guard (fn-arena$c-wfp fn-arena$c)
                  :verify-guards nil))
  (let* ((start (fn-arena$c-fill fn-arena$c))
         (fn-arena$c (fn-arn-write-buffer 0 (fn-octets-len fn-octets) fn-octets fn-arena$c)))
    (fn-arn-seal-entry start fn-arena$c)))

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

; -----------------------------------------------------------------------------
; The abstraction relation.

(defun fn-arena$corr (fn-arena$c fn-arena$a)
  (declare (xargs :verify-guards nil))
  (and (fn-arena$cp fn-arena$c)
       (fn-arn-payload-listp fn-arena$a)
       (<= (nth *fn-arena$c-fill* fn-arena$c) (len (nth *fn-arena$c-bufi* fn-arena$c)))
       (<= (nth *fn-arena$c-count* fn-arena$c) (len (nth *fn-arena$c-offi* fn-arena$c)))
       (<= (nth *fn-arena$c-count* fn-arena$c) (len (nth *fn-arena$c-sizei* fn-arena$c)))
       (fn-arn-rangesp 0 (nth *fn-arena$c-count* fn-arena$c)
                       (nth *fn-arena$c-offi* fn-arena$c) (nth *fn-arena$c-sizei* fn-arena$c)
                       (nth *fn-arena$c-fill* fn-arena$c))
       (equal (fn-arn-slices 0 (nth *fn-arena$c-count* fn-arena$c)
                             (nth *fn-arena$c-offi* fn-arena$c) (nth *fn-arena$c-sizei* fn-arena$c)
                             (nth *fn-arena$c-bufi* fn-arena$c))
              fn-arena$a)))

; `nth' and `update-nth' stay closed from here on (octets-stobj, rep-sha256).
(local (in-theory (disable nth update-nth)))
(local (in-theory (enable update-nth-array)))

(defthm fn-arn-cp-fields
  (implies (fn-arena$cp fn-arena$c)
           (and (true-listp fn-arena$c)
                (equal (len fn-arena$c) 5)
                (fn-octets$c-bufp (nth 0 fn-arena$c))
                (fn-arena$c-offp (nth 1 fn-arena$c))
                (fn-arena$c-sizep (nth 2 fn-arena$c))
                (integerp (nth 3 fn-arena$c)) (<= 0 (nth 3 fn-arena$c))
                (integerp (nth 4 fn-arena$c)) (<= 0 (nth 4 fn-arena$c))))
  :rule-classes ((:forward-chaining :trigger-terms ((fn-arena$cp fn-arena$c)))))

(defthm fn-arn-cp-of-update-buf
  (implies (and (fn-arena$cp fn-arena$c) (fn-octets$c-bufp buf))
           (fn-arena$cp (update-nth 0 buf fn-arena$c))))

(defthm fn-arn-cp-of-update-off
  (implies (and (fn-arena$cp fn-arena$c) (fn-arena$c-offp off))
           (fn-arena$cp (update-nth 1 off fn-arena$c))))

(defthm fn-arn-cp-of-update-size
  (implies (and (fn-arena$cp fn-arena$c) (fn-arena$c-sizep size))
           (fn-arena$cp (update-nth 2 size fn-arena$c))))

(defthm fn-arn-cp-of-update-count
  (implies (and (fn-arena$cp fn-arena$c) (natp n))
           (fn-arena$cp (update-nth 3 n fn-arena$c))))

(defthm fn-arn-cp-of-update-fill
  (implies (and (fn-arena$cp fn-arena$c) (natp n))
           (fn-arena$cp (update-nth 4 n fn-arena$c))))

(local (in-theory (disable fn-arena$cp fn-arena$c-offp fn-arena$c-sizep)))

; -----------------------------------------------------------------------------
; The write at the fill point: the concrete invariant is kept, the handle
; fields are untouched, the fill grows by the octets written, every cell
; below the old fill is unchanged, and the cells [old fill, new fill) are
; the octets.

(defthm fn-arn-write-octet-step
  (implies (and (fn-arena$cp fn-arena$c)
                (<= (nth 4 fn-arena$c) (len (nth 0 fn-arena$c)))
                (fn-cbor-octetp o))
           (let ((next (fn-arn-write-octet o fn-arena$c)))
             (and (fn-arena$cp next)
                  (equal (nth 1 next) (nth 1 fn-arena$c))
                  (equal (nth 2 next) (nth 2 fn-arena$c))
                  (equal (nth 3 next) (nth 3 fn-arena$c))
                  (equal (nth 4 next) (1+ (nth 4 fn-arena$c)))
                  (<= (nth 4 next) (len (nth 0 next)))
                  (equal (nth (nth 4 fn-arena$c) (nth 0 next)) o)))))

; The same room fact in the form the rewriter meets it once the fill has
; been rewritten to its successor: a linear rule.
(defthm fn-arn-write-octet-room
  (implies (and (fn-arena$cp fn-arena$c)
                (<= (nth 4 fn-arena$c) (len (nth 0 fn-arena$c)))
                (fn-cbor-octetp o))
           (< (nth 4 fn-arena$c) (len (nth 0 (fn-arn-write-octet o fn-arena$c)))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use ((:instance fn-arn-write-octet-step))
           :in-theory (disable fn-arn-write-octet-step fn-arn-write-octet))))

(defthm fn-arn-write-octet-keeps-below-fill
  (implies (and (fn-arena$cp fn-arena$c)
                (<= (nth 4 fn-arena$c) (len (nth 0 fn-arena$c)))
                (natp k) (< k (nth 4 fn-arena$c)))
           (equal (nth k (nth 0 (fn-arn-write-octet o fn-arena$c)))
                  (nth k (nth 0 fn-arena$c)))))

(defthm fn-arn-write-octet-keeps-list-from-below-fill
  (implies (and (fn-arena$cp fn-arena$c)
                (<= (nth 4 fn-arena$c) (len (nth 0 fn-arena$c)))
                (natp n) (<= n (nth 4 fn-arena$c)))
           (equal (fn-oct-list-from i n (nth 0 (fn-arn-write-octet o fn-arena$c)))
                  (fn-oct-list-from i n (nth 0 fn-arena$c)))))

(local (in-theory (disable fn-arn-write-octet)))

(defthm fn-arn-write-steps
  (implies (and (fn-arena$cp fn-arena$c)
                (<= (nth 4 fn-arena$c) (len (nth 0 fn-arena$c)))
                (fn-cbor-octet-listp xs))
           (let ((next (fn-arn-write xs fn-arena$c)))
             (and (fn-arena$cp next)
                  (equal (nth 1 next) (nth 1 fn-arena$c))
                  (equal (nth 2 next) (nth 2 fn-arena$c))
                  (equal (nth 3 next) (nth 3 fn-arena$c))
                  (equal (nth 4 next) (+ (nth 4 fn-arena$c) (len xs)))
                  (<= (+ (nth 4 fn-arena$c) (len xs)) (len (nth 0 next))))))
  :hints (("Goal" :induct (fn-arn-write xs fn-arena$c))))

(defthm fn-arn-write-room
  (implies (and (fn-arena$cp fn-arena$c)
                (<= (nth 4 fn-arena$c) (len (nth 0 fn-arena$c)))
                (fn-cbor-octet-listp xs))
           (<= (+ (nth 4 fn-arena$c) (len xs)) (len (nth 0 (fn-arn-write xs fn-arena$c)))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-arn-write-steps))
           :in-theory (disable fn-arn-write-steps fn-arn-write))))

(defthm fn-arn-write-keeps-below-fill
  (implies (and (fn-arena$cp fn-arena$c)
                (<= (nth 4 fn-arena$c) (len (nth 0 fn-arena$c)))
                (fn-cbor-octet-listp xs)
                (natp k) (< k (nth 4 fn-arena$c)))
           (equal (nth k (nth 0 (fn-arn-write xs fn-arena$c)))
                  (nth k (nth 0 fn-arena$c))))
  :hints (("Goal" :induct (fn-arn-write xs fn-arena$c))))

(defthm fn-arn-write-keeps-list-from-below-fill
  (implies (and (fn-arena$cp fn-arena$c)
                (<= (nth 4 fn-arena$c) (len (nth 0 fn-arena$c)))
                (fn-cbor-octet-listp xs)
                (natp n) (<= n (nth 4 fn-arena$c)))
           (equal (fn-oct-list-from i n (nth 0 (fn-arn-write xs fn-arena$c)))
                  (fn-oct-list-from i n (nth 0 fn-arena$c))))
  :hints (("Goal" :induct (fn-arn-write xs fn-arena$c))))

(defthm fn-arn-write-appends
  (implies (and (fn-arena$cp fn-arena$c)
                (<= (nth 4 fn-arena$c) (len (nth 0 fn-arena$c)))
                (fn-cbor-octet-listp xs))
           (equal (fn-oct-list-from (nth 4 fn-arena$c) (+ (nth 4 fn-arena$c) (len xs))
                                    (nth 0 (fn-arn-write xs fn-arena$c)))
                  xs))
  :hints (("Goal" :induct (fn-arn-write xs fn-arena$c)
           :in-theory (enable fn-oct-list-from))))

(defthm fn-arn-write-keeps-slices
  (implies (and (fn-arena$cp fn-arena$c)
                (<= (nth 4 fn-arena$c) (len (nth 0 fn-arena$c)))
                (fn-cbor-octet-listp xs)
                (fn-arn-rangesp h count off size (nth 4 fn-arena$c)))
           (equal (fn-arn-slices h count off size (nth 0 (fn-arn-write xs fn-arena$c)))
                  (fn-arn-slices h count off size (nth 0 fn-arena$c))))
  :hints (("Goal" :in-theory (enable fn-arn-slices fn-arn-rangesp)
           :induct (fn-arn-slices h count off size (nth 0 fn-arena$c)))))

(local (in-theory (disable fn-arn-write)))

(verify-guards fn-arena$c-seal-list)

; The buffer copy is the write of the buffer's slice, hence of its value.

(defthm fn-arn-write-buffer-is-write
  (equal (fn-arn-write-buffer i n fn-octets fn-arena$c)
         (fn-arn-write (fn-oct-slice-list i n fn-octets) fn-arena$c))
  :hints (("Goal" :induct (fn-arn-write-buffer i n fn-octets fn-arena$c)
           :in-theory (e/d (fn-arn-write fn-oct-slice-list) (fn-arn-write-octet))
           :expand ((fn-oct-slice-list i n fn-octets)))))

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

(verify-guards fn-arena$c-seal-buffer
  :hints (("Goal" :in-theory (enable fn-oct-octets-p-is-octet-listp))))

; The seal entry: the new handle is the old count, its range is
; [start, fill), every older slice and range is kept.

(defthm fn-arn-seal-entry-step
  (implies (and (fn-arena$cp fn-arena$c)
                (<= (nth 3 fn-arena$c) (len (nth 1 fn-arena$c)))
                (<= (nth 3 fn-arena$c) (len (nth 2 fn-arena$c)))
                (natp start) (<= start (nth 4 fn-arena$c)))
           (let ((next (fn-arn-seal-entry start fn-arena$c)))
             (and (fn-arena$cp next)
                  (equal (nth 0 next) (nth 0 fn-arena$c))
                  (equal (nth 3 next) (1+ (nth 3 fn-arena$c)))
                  (equal (nth 4 next) (nth 4 fn-arena$c))
                  (<= (nth 3 next) (len (nth 1 next)))
                  (<= (nth 3 next) (len (nth 2 next)))
                  (equal (nth (nth 3 fn-arena$c) (nth 1 next)) start)
                  (equal (nth (nth 3 fn-arena$c) (nth 2 next)) (- (nth 4 fn-arena$c) start))
                  (equal (fn-arn-slices 0 (nth 3 fn-arena$c) (nth 1 next) (nth 2 next) buf)
                         (fn-arn-slices 0 (nth 3 fn-arena$c) (nth 1 fn-arena$c) (nth 2 fn-arena$c) buf))
                  (equal (fn-arn-rangesp 0 (nth 3 fn-arena$c) (nth 1 next) (nth 2 next) top)
                         (fn-arn-rangesp 0 (nth 3 fn-arena$c) (nth 1 fn-arena$c) (nth 2 fn-arena$c) top))))))

(defthm fn-arn-seal-entry-room
  (implies (and (fn-arena$cp fn-arena$c)
                (<= (nth 3 fn-arena$c) (len (nth 1 fn-arena$c)))
                (<= (nth 3 fn-arena$c) (len (nth 2 fn-arena$c)))
                (natp start) (<= start (nth 4 fn-arena$c)))
           (and (< (nth 3 fn-arena$c) (len (nth 1 (fn-arn-seal-entry start fn-arena$c))))
                (< (nth 3 fn-arena$c) (len (nth 2 (fn-arn-seal-entry start fn-arena$c))))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use ((:instance fn-arn-seal-entry-step))
           :in-theory (disable fn-arn-seal-entry-step fn-arn-seal-entry))))

; The same facts with the handle and the count as free variables: in a goal
; about a seal after a write, the count is the outer state's (the write
; keeps it), and a rule whose left side names the written state's count
; never matches.
(defthm fn-arn-seal-entry-reads
  (implies (and (fn-arena$cp fn-arena$c)
                (<= (nth 3 fn-arena$c) (len (nth 1 fn-arena$c)))
                (<= (nth 3 fn-arena$c) (len (nth 2 fn-arena$c)))
                (natp start) (<= start (nth 4 fn-arena$c))
                (equal h (nth 3 fn-arena$c)))
           (and (equal (nth h (nth 1 (fn-arn-seal-entry start fn-arena$c))) start)
                (equal (nth h (nth 2 (fn-arn-seal-entry start fn-arena$c)))
                       (- (nth 4 fn-arena$c) start))
                (equal (fn-arn-slices 0 h (nth 1 (fn-arn-seal-entry start fn-arena$c))
                                      (nth 2 (fn-arn-seal-entry start fn-arena$c)) buf)
                       (fn-arn-slices 0 h (nth 1 fn-arena$c) (nth 2 fn-arena$c) buf))
                (equal (fn-arn-rangesp 0 h (nth 1 (fn-arn-seal-entry start fn-arena$c))
                                       (nth 2 (fn-arn-seal-entry start fn-arena$c)) top)
                       (fn-arn-rangesp 0 h (nth 1 fn-arena$c) (nth 2 fn-arena$c) top))))
  :hints (("Goal" :use ((:instance fn-arn-seal-entry-step))
           :in-theory (disable fn-arn-seal-entry-step fn-arn-seal-entry))))

; fn-arn-write-appends with the sum as the prover orders it.
(defthm fn-arn-write-appends-2
  (implies (and (fn-arena$cp fn-arena$c)
                (<= (nth 4 fn-arena$c) (len (nth 0 fn-arena$c)))
                (fn-cbor-octet-listp xs))
           (equal (fn-oct-list-from (nth 4 fn-arena$c) (+ (len xs) (nth 4 fn-arena$c))
                                    (nth 0 (fn-arn-write xs fn-arena$c)))
                  xs))
  :hints (("Goal" :use ((:instance fn-arn-write-appends)))))

(local (in-theory (disable fn-arn-seal-entry)))

; The seal, in one lemma: the slices grow by the octets written.

(defthm fn-arn-seal-list-step
  (implies (and (fn-arena$cp fn-arena$c)
                (<= (nth 4 fn-arena$c) (len (nth 0 fn-arena$c)))
                (<= (nth 3 fn-arena$c) (len (nth 1 fn-arena$c)))
                (<= (nth 3 fn-arena$c) (len (nth 2 fn-arena$c)))
                (fn-arn-rangesp 0 (nth 3 fn-arena$c) (nth 1 fn-arena$c) (nth 2 fn-arena$c)
                                (nth 4 fn-arena$c))
                (fn-cbor-octet-listp xs))
           (let ((next (fn-arena$c-seal-list xs fn-arena$c)))
             (and (fn-arena$cp next)
                  (<= (nth 4 next) (len (nth 0 next)))
                  (<= (nth 3 next) (len (nth 1 next)))
                  (<= (nth 3 next) (len (nth 2 next)))
                  (fn-arn-rangesp 0 (nth 3 next) (nth 1 next) (nth 2 next) (nth 4 next))
                  (equal (fn-arn-slices 0 (nth 3 next) (nth 1 next) (nth 2 next) (nth 0 next))
                         (append (fn-arn-slices 0 (nth 3 fn-arena$c) (nth 1 fn-arena$c)
                                                (nth 2 fn-arena$c) (nth 0 fn-arena$c))
                                 (list xs))))))
  :hints (("Goal" :use ((:instance fn-arn-slices-snoc
                                   (h 0) (n (nth 3 fn-arena$c))
                                   (off (nth 1 (fn-arn-seal-entry (nth 4 fn-arena$c) (fn-arn-write xs fn-arena$c))))
                                   (size (nth 2 (fn-arn-seal-entry (nth 4 fn-arena$c) (fn-arn-write xs fn-arena$c))))
                                   (buf (nth 0 (fn-arn-write xs fn-arena$c))))
                        (:instance fn-arn-rangesp-snoc
                                   (h 0) (n (nth 3 fn-arena$c))
                                   (off (nth 1 (fn-arn-seal-entry (nth 4 fn-arena$c) (fn-arn-write xs fn-arena$c))))
                                   (size (nth 2 (fn-arn-seal-entry (nth 4 fn-arena$c) (fn-arn-write xs fn-arena$c))))
                                   (top (+ (nth 4 fn-arena$c) (len xs)))))
           :do-not-induct t)))

(local (in-theory (disable fn-arena$c-seal-list)))

; -----------------------------------------------------------------------------
; The obligations, each as `defabsstobj-missing-events' states it.

(defthm create-fn-arena{correspondence}
  (fn-arena$corr (create-fn-arena$c) (create-fn-arena$a))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-arena$cp fn-arn-slices fn-arn-rangesp))))

(defthm create-fn-arena{preserved}
  (fn-arena$ap (create-fn-arena$a))
  :rule-classes nil)

(defthm fn-arena-count{correspondence}
  (implies (fn-arena$corr fn-arena$c fn-arena)
           (equal (fn-arena$c-count fn-arena$c) (fn-arena$a-count fn-arena)))
  :rule-classes nil)

(defthm fn-arena-payload-len{correspondence}
  (implies (and (fn-arena$corr fn-arena$c fn-arena)
                (natp h) (< h (fn-arena$a-count fn-arena)))
           (equal (fn-arena$c-payload-len h fn-arena$c) (fn-arena$a-payload-len h fn-arena)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-arn-rangesp-at
                                   (h 0) (k h) (count (nth 3 fn-arena$c))
                                   (off (nth 1 fn-arena$c)) (size (nth 2 fn-arena$c))
                                   (top (nth 4 fn-arena$c)))))))

(defthm fn-arena-payload-len{guard-thm}
  (implies (and (fn-arena$corr fn-arena$c fn-arena)
                (natp h) (< h (fn-arena$a-count fn-arena)))
           (and (natp h) (< h (fn-arena$c-count fn-arena$c))
                (fn-arena$c-wfp fn-arena$c)))
  :rule-classes nil)

(defthm fn-arena-get{correspondence}
  (implies (and (fn-arena$corr fn-arena$c fn-arena)
                (natp h) (< h (fn-arena$a-count fn-arena))
                (natp i) (< i (fn-arena$a-payload-len h fn-arena)))
           (equal (fn-arena$c-get h i fn-arena$c) (fn-arena$a-get h i fn-arena)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-arn-rangesp-at
                                   (h 0) (k h) (count (nth 3 fn-arena$c))
                                   (off (nth 1 fn-arena$c)) (size (nth 2 fn-arena$c))
                                   (top (nth 4 fn-arena$c)))))))

(defthm fn-arena-get{guard-thm}
  (implies (and (fn-arena$corr fn-arena$c fn-arena)
                (natp h) (< h (fn-arena$a-count fn-arena))
                (natp i) (< i (fn-arena$a-payload-len h fn-arena)))
           (and (fn-arena$c-wfp fn-arena$c)
                (natp h) (< h (fn-arena$c-count fn-arena$c))
                (natp i)
                (natp (fn-arena$c-offi h fn-arena$c))
                (natp (fn-arena$c-sizei h fn-arena$c))
                (< i (fn-arena$c-sizei h fn-arena$c))
                (<= (+ (fn-arena$c-offi h fn-arena$c) (fn-arena$c-sizei h fn-arena$c))
                    (fn-arena$c-fill fn-arena$c))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-arn-rangesp-at
                                   (h 0) (k h) (count (nth 3 fn-arena$c))
                                   (off (nth 1 fn-arena$c)) (size (nth 2 fn-arena$c))
                                   (top (nth 4 fn-arena$c)))))))

(defthm fn-arena-payload{correspondence}
  (implies (and (fn-arena$corr fn-arena$c fn-arena)
                (natp h) (< h (fn-arena$a-count fn-arena)))
           (equal (fn-arena$c-payload h fn-arena$c) (fn-arena$a-payload h fn-arena)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-arn-rangesp-at
                                   (h 0) (k h) (count (nth 3 fn-arena$c))
                                   (off (nth 1 fn-arena$c)) (size (nth 2 fn-arena$c))
                                   (top (nth 4 fn-arena$c)))))))

(defthm fn-arena-payload{guard-thm}
  (implies (and (fn-arena$corr fn-arena$c fn-arena)
                (natp h) (< h (fn-arena$a-count fn-arena)))
           (and (fn-arena$c-wfp fn-arena$c)
                (natp h) (< h (fn-arena$c-count fn-arena$c))
                (natp (fn-arena$c-offi h fn-arena$c))
                (natp (fn-arena$c-sizei h fn-arena$c))
                (<= (+ (fn-arena$c-offi h fn-arena$c) (fn-arena$c-sizei h fn-arena$c))
                    (fn-arena$c-fill fn-arena$c))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-arn-rangesp-at
                                   (h 0) (k h) (count (nth 3 fn-arena$c))
                                   (off (nth 1 fn-arena$c)) (size (nth 2 fn-arena$c))
                                   (top (nth 4 fn-arena$c)))))))

(defthm fn-arena-seal-list{correspondence}
  (implies (and (fn-arena$corr fn-arena$c fn-arena)
                (fn-cbor-octet-listp xs))
           (fn-arena$corr (fn-arena$c-seal-list xs fn-arena$c)
                          (fn-arena$a-seal-list xs fn-arena)))
  :rule-classes nil)

(defthm fn-arena-seal-list{guard-thm}
  (implies (and (fn-arena$corr fn-arena$c fn-arena)
                (fn-cbor-octet-listp xs))
           (and (fn-cbor-octet-listp xs) (fn-arena$c-wfp fn-arena$c)))
  :rule-classes nil)

(defthm fn-arena-seal-list{preserved}
  (implies (and (fn-arena$ap fn-arena)
                (fn-cbor-octet-listp xs))
           (fn-arena$ap (fn-arena$a-seal-list xs fn-arena)))
  :rule-classes nil)

(defthm fn-arena-seal-buffer{correspondence}
  (implies (and (fn-arena$corr fn-arena$c fn-arena)
                (fn-octets-p fn-octets))
           (fn-arena$corr (fn-arena$c-seal-buffer fn-octets fn-arena$c)
                          (fn-arena$a-seal-buffer fn-octets fn-arena)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-arena$c-seal-list fn-oct-octets-p-is-octet-listp)
                                  (fn-arn-seal-list-step))
           :use ((:instance fn-arn-seal-list-step (xs fn-octets))))))

(defthm fn-arena-seal-buffer{guard-thm}
  (implies (and (fn-arena$corr fn-arena$c fn-arena)
                (fn-octets-p fn-octets))
           (fn-arena$c-wfp fn-arena$c))
  :rule-classes nil)

(defthm fn-arena-seal-buffer{preserved}
  (implies (and (fn-arena$ap fn-arena)
                (fn-octets-p fn-octets))
           (fn-arena$ap (fn-arena$a-seal-buffer fn-octets fn-arena)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-oct-octets-p-is-octet-listp))))

(defthm fn-arena-clear{correspondence}
  (implies (fn-arena$corr fn-arena$c fn-arena)
           (fn-arena$corr (fn-arena$c-clear fn-arena$c) (fn-arena$a-clear fn-arena)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-arn-slices fn-arn-rangesp))))

(defthm fn-arena-clear{preserved}
  (implies (fn-arena$ap fn-arena)
           (fn-arena$ap (fn-arena$a-clear fn-arena)))
  :rule-classes nil)

(defabsstobj fn-arena
  :foundation fn-arena$c
  :recognizer (fn-arena-p :logic fn-arena$ap :exec fn-arena$cp)
  :creator (create-fn-arena :logic create-fn-arena$a :exec create-fn-arena$c)
  :corr-fn fn-arena$corr
  :exports ((fn-arena-count :logic fn-arena$a-count :exec fn-arena$c-count)
            (fn-arena-payload-len :logic fn-arena$a-payload-len :exec fn-arena$c-payload-len)
            (fn-arena-get :logic fn-arena$a-get :exec fn-arena$c-get)
            (fn-arena-payload :logic fn-arena$a-payload :exec fn-arena$c-payload)
            (fn-arena-seal-list :logic fn-arena$a-seal-list :exec fn-arena$c-seal-list
                                :protect t)
            (fn-arena-seal-buffer :logic fn-arena$a-seal-buffer :exec fn-arena$c-seal-buffer
                                  :protect t)
            (fn-arena-clear :logic fn-arena$a-clear :exec fn-arena$c-clear :protect t)))

; -----------------------------------------------------------------------------
; The logical view, opened: the value is the list of payloads, a handle is
; a position, a seal is an append.

(defthm fn-arena-p-is-payload-listp
  (equal (fn-arena-p x) (fn-arn-payload-listp x)))

(defthm fn-arena-count-is-len
  (equal (fn-arena-count fn-arena) (len fn-arena)))

(defthm fn-arena-payload-len-is-len-nth
  (equal (fn-arena-payload-len h fn-arena) (len (nth h fn-arena))))

(defthm fn-arena-get-is-nth
  (equal (fn-arena-get h i fn-arena) (nth i (nth h fn-arena))))

(defthm fn-arena-payload-is-nth
  (equal (fn-arena-payload h fn-arena) (nth h fn-arena)))

(defthm fn-arena-seal-list-is-append
  (implies (fn-arena-p fn-arena)
           (equal (fn-arena-seal-list xs fn-arena) (append fn-arena (list xs)))))

(defthm fn-arena-seal-buffer-is-append
  (implies (fn-arena-p fn-arena)
           (equal (fn-arena-seal-buffer fn-octets fn-arena) (append fn-arena (list fn-octets)))))

(defthm fn-arena-clear-is-nil
  (equal (fn-arena-clear fn-arena) nil))

(defthm fn-arena-p-forward
  (implies (fn-arena-p x)
           (and (fn-arn-payload-listp x) (true-listp x)))
  :rule-classes :forward-chaining)

(in-theory (disable fn-arena-p fn-arena-count fn-arena-payload-len fn-arena-get
                    fn-arena-payload fn-arena-seal-list fn-arena-seal-buffer fn-arena-clear
                    fn-arena-p-is-payload-listp))

; -----------------------------------------------------------------------------
; KEYSTONES.  What a reader holding a handle may rely on.

; A sealed handle is immutable: whatever a seal appends, every handle below
; the old count denotes the octets it denoted before.  A reader that pinned
; a handle sees the same payload after any later commit.
; The hypotheses are that the handle is a natural below the count: on the
; empty arena a negative handle reads the new payload (`nth' of a negative
; is `car'), so `natp' is not redundant.  No recognizer is needed: the
; seal walks the conses the value has.
(local
 (defthm fn-arn-nth-of-snoc-below
   (implies (and (natp h) (< h (len a)))
            (equal (nth h (fn-oct-snoc a xs)) (nth h a)))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm fn-arn-nth-of-snoc-at
   (equal (nth (len a) (fn-oct-snoc a xs)) xs)
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm fn-arn-len-of-snoc
   (equal (len (fn-oct-snoc a xs)) (1+ (len a)))))

(defthm fn-arena-seal-keeps-sealed
  (implies (and (natp h) (< h (fn-arena-count fn-arena)))
           (equal (fn-arena-payload h (fn-arena-seal-list xs fn-arena))
                  (fn-arena-payload h fn-arena)))
  :hints (("Goal" :in-theory (enable fn-arena-payload fn-arena-seal-list fn-arena-count))))

(defthm fn-arena-seal-buffer-keeps-sealed
  (implies (and (natp h) (< h (fn-arena-count fn-arena)))
           (equal (fn-arena-payload h (fn-arena-seal-buffer fn-octets fn-arena))
                  (fn-arena-payload h fn-arena)))
  :hints (("Goal" :in-theory (enable fn-arena-payload fn-arena-seal-buffer fn-arena-count))))

; A handle is never reused: the seal's new handle is the old count, it
; denotes the sealed octets, and the count grows by one.  No hypothesis.
(defthm fn-arena-seal-new-handle
  (equal (fn-arena-payload (fn-arena-count fn-arena) (fn-arena-seal-list xs fn-arena))
         xs)
  :hints (("Goal" :in-theory (enable fn-arena-payload fn-arena-seal-list fn-arena-count))))

(defthm fn-arena-seal-count
  (equal (fn-arena-count (fn-arena-seal-list xs fn-arena))
         (1+ (fn-arena-count fn-arena)))
  :hints (("Goal" :in-theory (enable fn-arena-seal-list fn-arena-count))))

; The same two facts in the `len' form the opened view leaves behind, so
; that a guard about a count after seals is arithmetic.
(defthm fn-arena-seal-list-len
  (equal (len (fn-arena-seal-list xs fn-arena)) (1+ (len fn-arena)))
  :hints (("Goal" :in-theory (enable fn-arena-seal-list))))

(defthm fn-arena-seal-buffer-len
  (equal (len (fn-arena-seal-buffer fn-octets fn-arena)) (1+ (len fn-arena)))
  :hints (("Goal" :in-theory (enable fn-arena-seal-buffer))))

; Any sequence of seals (the admitted transitions of a live arena: a commit
; is a seal, and nothing else changes the value between open and close)
; keeps every handle it found.
(defun fn-arn-seal-many (payloads fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-arn-payload-listp payloads)))
  (if (atom payloads)
      fn-arena
    (let ((fn-arena (fn-arena-seal-list (car payloads) fn-arena)))
      (fn-arn-seal-many (cdr payloads) fn-arena))))

; The seal is `append' on any true list, whatever its elements: the
; recognizer is not needed here and is not what the fold preserves.
(defthm fn-arn-seal-many-is-append
  (implies (and (true-listp fn-arena) (true-listp payloads))
           (equal (fn-arn-seal-many payloads fn-arena)
                  (append fn-arena payloads)))
  :hints (("Goal" :induct (fn-arn-seal-many payloads fn-arena)
           :in-theory (enable fn-arena-seal-list))))

; The immutability fact in the `nth' form the opened view leaves behind.
(defthm fn-arena-seal-list-keeps-nth-below
  (implies (and (natp h) (< h (len fn-arena)))
           (equal (nth h (fn-arena-seal-list xs fn-arena)) (nth h fn-arena)))
  :hints (("Goal" :in-theory (enable fn-arena-seal-list))))

(defthm fn-arena-seals-keep-sealed
  (implies (and (natp h) (< h (fn-arena-count fn-arena)))
           (equal (fn-arena-payload h (fn-arn-seal-many payloads fn-arena))
                  (fn-arena-payload h fn-arena)))
  :hints (("Goal" :induct (fn-arn-seal-many payloads fn-arena)
           :in-theory (disable fn-arn-seal-many-is-append))))

; -----------------------------------------------------------------------------
; The relation with a store history.  The history (fn-sf-records,
; books/store-files.lisp) is oldest first, a commit appending the finished
; record at its end (fn-sf-finish: `(append (fn-sf-records s) (list record))'),
; and so is the arena: handle k is the payload of the k-th record.

(defun fn-arn-payloads-of (records)
  (declare (xargs :guard t))
  (if (consp records)
      (cons (fn-record-payload (car records))
            (fn-arn-payloads-of (cdr records)))
    nil))

(defthm fn-arn-true-listp-of-payloads-of
  (true-listp (fn-arn-payloads-of records)))

(defthm fn-arn-payloads-of-append-one
  (equal (fn-arn-payloads-of (append records (list record)))
         (append (fn-arn-payloads-of records) (list (fn-record-payload record)))))

; The relation itself is logical (defun-nx): the arena's value against the
; history.  Nothing executes it; a commit and an open establish it by the
; two theorems that follow, and nothing on a served path evaluates it.
(defun-nx fn-arn-store-corr (fn-arena records)
  (equal fn-arena (fn-arn-payloads-of records)))

; Commit: the finished record joins the head of the history and its
; payload is sealed; the relation is kept.
(defthm fn-arn-store-corr-of-commit
  (implies (fn-arn-store-corr fn-arena records)
           (fn-arn-store-corr (fn-arena-seal-list (fn-record-payload record) fn-arena)
                              (append records (list record))))
  :hints (("Goal" :in-theory (enable fn-arena-seal-list))))

; Open: every retained record's payload sealed oldest first from the empty
; arena establishes the same relation a history of commits would have.
(defthm fn-arn-store-corr-of-open
  (fn-arn-store-corr (fn-arn-seal-many (fn-arn-payloads-of records) nil) records)
  :hints (("Goal" :in-theory (enable fn-arena-seal-list))))
