; fn: BPv7 bundle fragmentation and application data unit reassembly.
;
; RFC 9171 section 5.8 says fragmentation replaces a bundle whose payload is of
; size M with fragments whose payloads concatenate to exactly the original
; payload, each carrying the same source node ID and creation timestamp as the
; fragmented bundle, each with the fragment flag set and both fragment offset
; and total application data unit length present.  Section 5.9 says reassembly
; collects the "material extents" of fragments with the same source node ID and
; creation timestamp, and that fragments from different fragmentation episodes
; "may be overlapping subsets of the fragmented bundle's payload".
;
; That last sentence is the whole design constraint here.  Overlap is normal,
; not an error.  fn's existing transfer kernel treats a partial overlap as
; `:overlap-conflict` without comparing the bytes, which stalls a re-fragmented
; object permanently; this book does not repeat that.  Overlapping extents that
; carry the same bytes are accepted and merged; only differing bytes at one
; offset are a conflict, and the conflict names the offset.
;
; The reassembler is specified index-wise rather than as a fold over fragments,
; so the result does not depend on the order fragments arrive in: every cell of
; the reassembled array is a function of the whole fragment list at that index.
; The cost of that choice is honest and bounded -- a reassembly examines at most
; `*fn-bpf-max-length*` cells against at most `*fn-bpf-max-fragments*`
; fragments -- and a production reassembler would carry an interval structure
; refined against this specification rather than executing it directly.
;
; This book performs no I/O, reserves no capacity, and releases no obligation.
; A reassembled ADU is not an accepted article.

(in-package "ACL2")

(include-book "bp-primary")

(local (include-book "arithmetic/top" :dir :system))
; codecs withdrew the record and cbor proof vocabularies at export (2026-09-19);
; this book reasons under them, so open them here, locally.
(local (in-theory (enable fn-cbor-record-vocabulary fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary)))

; `arithmetic/top`'s generalization rule for `mod` introduces fresh `mod`
; terms into case trees that never had one, and loops the waterfall on the
; bit-level recursions below.  Local, so nothing downstream inherits it.
(local (in-theory (disable mod-x-y-=-x+y-for-rationals)))

; -----------------------------------------------------------------------------
; Bounds
;
; fn's BP application data unit cap is 32 KiB; 65536 leaves BP framing headroom
; without claiming a general BPv7 limit.  Both bounds are local policy.

(defconst *fn-bpf-max-length* 65536)
(defconst *fn-bpf-max-fragments* 64)

; -----------------------------------------------------------------------------
; Fragments
;
; A fragment is (:fn-bp-fragment offset bytes total), where `total` is the
; total application data unit length of RFC 9171 section 4.3.1.  The payload
; length is `(len bytes)`; it is not stored separately, because a stored copy
; could only ever disagree with the bytes.

(defun fn-bpf-make (offset bytes total)
  (declare (xargs :guard t))
  (list :fn-bp-fragment offset bytes total))

(defun fn-bpf-offset (f) (declare (xargs :guard (true-listp f))) (nth 1 f))
(defun fn-bpf-bytes (f) (declare (xargs :guard (true-listp f))) (nth 2 f))
(defun fn-bpf-total (f) (declare (xargs :guard (true-listp f))) (nth 3 f))

(verify-guards fn-bpf-make)
(verify-guards fn-bpf-offset)
(verify-guards fn-bpf-bytes)
(verify-guards fn-bpf-total)

(defun fn-bpf-fragmentp (f)
  (declare (xargs :guard t))
  (and (true-listp f)
       (equal (len f) 4)
       (eq (nth 0 f) :fn-bp-fragment)
       (natp (fn-bpf-offset f))
       (fn-cbor-octet-listp (fn-bpf-bytes f))
       (natp (fn-bpf-total f))
       (<= (fn-bpf-total f) *fn-bpf-max-length*)
       (consp (fn-bpf-bytes f))
       (<= (+ (fn-bpf-offset f) (len (fn-bpf-bytes f))) (fn-bpf-total f))))

(defun fn-bpf-fragment-listp (fs)
  (declare (xargs :guard t))
  (if (consp fs)
      (and (fn-bpf-fragmentp (car fs)) (fn-bpf-fragment-listp (cdr fs)))
    (null fs)))

(verify-guards fn-bpf-fragmentp)
(verify-guards fn-bpf-fragment-listp)

(defthm fn-bpf-fragmentp-fields
  (implies (fn-bpf-fragmentp f)
           (and (true-listp f)
                (natp (fn-bpf-offset f))
                (integerp (fn-bpf-offset f))
                (<= 0 (fn-bpf-offset f))
                (fn-cbor-octet-listp (fn-bpf-bytes f))
                (true-listp (fn-bpf-bytes f))
                (natp (fn-bpf-total f))))
  :rule-classes (:rewrite :forward-chaining))

(defthm fn-bpf-fragment-listp-is-a-true-list
  (implies (fn-bpf-fragment-listp fs) (true-listp fs))
  :rule-classes (:rewrite :forward-chaining))

(defthm fn-bpf-fragment-listp-car-and-cdr
  (implies (and (fn-bpf-fragment-listp fs) (consp fs))
           (and (fn-bpf-fragmentp (car fs))
                (fn-bpf-fragment-listp (cdr fs)))))

; Every fragment must declare the same total application data unit length, and
; there must not be more of them than the model admits.  This is checked before
; any cell is allocated.
(defun fn-bpf-same-total (fs total)
  (declare (xargs :guard (fn-bpf-fragment-listp fs)))
  (if (consp fs)
      (and (equal (fn-bpf-total (car fs)) total)
           (fn-bpf-same-total (cdr fs) total))
    t))

(defun fn-bpf-inputsp (fs total)
  (declare (xargs :guard t))
  (and (fn-bpf-fragment-listp fs)
       (natp total)
       (< 0 total)
       (<= total *fn-bpf-max-length*)
       (consp fs)
       (<= (len fs) *fn-bpf-max-fragments*)
       (fn-bpf-same-total fs total)))

(verify-guards fn-bpf-same-total)
(verify-guards fn-bpf-inputsp)

; -----------------------------------------------------------------------------
; Extents and coverage
;
; `:gap` marks an index no fragment covers.  An octet is a natural number, so
; no octet can be mistaken for a gap, and `:conflict` is likewise distinct.

(defun fn-bpf-coversp (f i)
  (declare (xargs :guard (and (fn-bpf-fragmentp f) (natp i))))
  (and (<= (fn-bpf-offset f) i)
       (< i (+ (fn-bpf-offset f) (len (fn-bpf-bytes f))))))

(defun fn-bpf-cell-of (f i)
  (declare (xargs :guard (and (fn-bpf-fragmentp f) (natp i))))
  (if (fn-bpf-coversp f i)
      (nth (- i (fn-bpf-offset f)) (fn-bpf-bytes f))
    :gap))

(defun fn-bpf-merge-cell (x y)
  (declare (xargs :guard t))
  (cond ((eq x :gap) y)
        ((eq y :gap) x)
        ((equal x y) x)
        (t :conflict)))

(defun fn-bpf-cell-at (fs i)
  (declare (xargs :guard (and (fn-bpf-fragment-listp fs) (natp i))))
  (if (consp fs)
      (fn-bpf-merge-cell (fn-bpf-cell-of (car fs) i)
                         (fn-bpf-cell-at (cdr fs) i))
    :gap))

(defun fn-bpf-coveredp (fs i)
  (declare (xargs :guard (and (fn-bpf-fragment-listp fs) (natp i))))
  (if (consp fs)
      (or (fn-bpf-coversp (car fs) i) (fn-bpf-coveredp (cdr fs) i))
    nil))

(verify-guards fn-bpf-coversp)
(verify-guards fn-bpf-cell-of)
(verify-guards fn-bpf-merge-cell)
(verify-guards fn-bpf-cell-at)
(verify-guards fn-bpf-coveredp)

; Every index in [from, from+n) is covered by some fragment.  The range form
; is what the reassembled array's own recursion needs.
(defun fn-bpf-covered-range (fs from n)
  (declare (xargs :guard (and (fn-bpf-fragment-listp fs) (natp from) (natp n))
                  :measure (nfix n)))
  (if (zp n)
      t
    (and (fn-bpf-coveredp fs from)
         (fn-bpf-covered-range fs (+ 1 from) (- n 1)))))

(defun fn-bpf-covers-all (fs n)
  (declare (xargs :guard (and (fn-bpf-fragment-listp fs) (natp n))))
  (fn-bpf-covered-range fs 0 n))

(verify-guards fn-bpf-covered-range)
(verify-guards fn-bpf-covers-all)

; The fragment's bytes are the extent of `payload` at its offset.
(defun fn-bpf-bytes-agreep (bytes offset payload)
  (declare (xargs :guard (and (true-listp bytes) (natp offset)
                              (true-listp payload))))
  (if (consp bytes)
      (and (equal (car bytes) (nth offset payload))
           (fn-bpf-bytes-agreep (cdr bytes) (+ 1 offset) payload))
    t))

(defun fn-bpf-agreesp (f payload)
  (declare (xargs :guard (and (fn-bpf-fragmentp f) (true-listp payload))))
  (fn-bpf-bytes-agreep (fn-bpf-bytes f) (fn-bpf-offset f) payload))

(defun fn-bpf-all-agreep (fs payload)
  (declare (xargs :guard (and (fn-bpf-fragment-listp fs) (true-listp payload))))
  (if (consp fs)
      (and (fn-bpf-agreesp (car fs) payload)
           (fn-bpf-all-agreep (cdr fs) payload))
    t))

(verify-guards fn-bpf-bytes-agreep)
(verify-guards fn-bpf-agreesp)
(verify-guards fn-bpf-all-agreep)

; -----------------------------------------------------------------------------
; The reassembled array

(defun fn-bpf-canvas (fs from n)
  (declare (xargs :guard (and (fn-bpf-fragment-listp fs) (natp from) (natp n))
                  :measure (nfix n)))
  (if (zp n)
      nil
    (cons (fn-bpf-cell-at fs from)
          (fn-bpf-canvas fs (+ 1 from) (- n 1)))))

(verify-guards fn-bpf-canvas)

(defun fn-bpf-first-index (cells from marker)
  (declare (xargs :guard (and (true-listp cells) (natp from) (symbolp marker))))
  (cond ((not (consp cells)) nil)
        ((eq (car cells) marker) from)
        (t (fn-bpf-first-index (cdr cells) (+ 1 from) marker))))

(defun fn-bpf-run-end (cells from marker)
  (declare (xargs :guard (and (true-listp cells) (natp from) (symbolp marker))))
  (if (and (consp cells) (eq (car cells) marker))
      (fn-bpf-run-end (cdr cells) (+ 1 from) marker)
    from))

(verify-guards fn-bpf-first-index)
(verify-guards fn-bpf-run-end)

(defthm fn-bpf-first-index-is-natural
  (implies (and (natp from) (fn-bpf-first-index cells from marker))
           (and (natp (fn-bpf-first-index cells from marker))
                (integerp (fn-bpf-first-index cells from marker))
                (<= 0 (fn-bpf-first-index cells from marker))))
  :hints (("Goal" :induct (fn-bpf-first-index cells from marker))))

(defthm fn-bpf-canvas-is-a-true-list
  (true-listp (fn-bpf-canvas fs from n))
  :hints (("Goal" :induct (fn-bpf-canvas fs from n))))

(defthm fn-bpf-nthcdr-of-true-list
  (implies (true-listp xs)
           (true-listp (nthcdr n xs)))
  :hints (("Goal" :induct (nthcdr n xs))))

; -----------------------------------------------------------------------------
; Reassembly (RFC 9171 section 5.9)
;
; Four outcomes stay distinct all the way out:
;
;   (:invalid reason)   the fragment list is outside the modeled bounds, or the
;                       fragments disagree about the total ADU length.  Checked
;                       before any cell is built.
;   (:conflict i)       two fragments cover index i with different octets.
;   (:missing lo hi)    no fragment covers [lo, hi); `lo` is the least
;                       uncovered index.
;   (:ok bytes)         the complete reassembled application data unit.
;
; A conflict is reported in preference to a gap: a peer that contradicts itself
; is a different event from a peer that has not finished sending.

(defun fn-bpf-reassemble (fs total)
  (declare (xargs :guard t))
  (if (not (fn-bpf-inputsp fs total))
      (list :invalid :bounds)
    (let* ((cells (fn-bpf-canvas fs 0 total))
           (conflict (fn-bpf-first-index cells 0 :conflict)))
      (if conflict
          (list :conflict conflict)
        (let ((gap (fn-bpf-first-index cells 0 :gap)))
          (if gap
              (list :missing gap
                    (fn-bpf-run-end (nthcdr gap cells) gap :gap))
            (list :ok cells)))))))

(verify-guards fn-bpf-reassemble)

(defun fn-bpf-result-tag (r)
  (declare (xargs :guard (true-listp r)))
  (nth 0 r))

(defun fn-bpf-result-bytes (r)
  (declare (xargs :guard (true-listp r)))
  (nth 1 r))

(verify-guards fn-bpf-result-tag)
(verify-guards fn-bpf-result-bytes)

; -----------------------------------------------------------------------------
; Fragmentation (RFC 9171 section 5.8)
;
; `boundaries` is the list of interior cut points, strictly increasing and
; strictly inside (0, len payload).  A bundle whose "must not be fragmented"
; flag is set is refused here rather than at a caller.

(defun fn-bpf-extent (payload from to)
  (declare (xargs :guard (and (true-listp payload) (natp from) (natp to))
                  :measure (nfix (- (nfix to) (nfix from)))))
  (if (or (not (natp from)) (not (natp to)) (<= to from))
      nil
    (cons (nth from payload)
          (fn-bpf-extent payload (+ 1 from) to))))

(verify-guards fn-bpf-extent)

(defun fn-bpf-boundariesp (bs from limit)
  (declare (xargs :guard (and (natp from) (natp limit))))
  (if (consp bs)
      (and (natp (car bs))
           (< from (car bs))
           (< (car bs) limit)
           (fn-bpf-boundariesp (cdr bs) (car bs) limit))
    (null bs)))

(verify-guards fn-bpf-boundariesp)

(defun fn-bpf-cut (payload from boundaries total)
  (declare (xargs :guard (and (true-listp payload) (natp from) (natp total))
                  :measure (acl2-count boundaries)))
  (if (consp boundaries)
      (cons (fn-bpf-make from (fn-bpf-extent payload from (nfix (car boundaries)))
                         total)
            (fn-bpf-cut payload (nfix (car boundaries)) (cdr boundaries) total))
    (list (fn-bpf-make from (fn-bpf-extent payload from total) total))))

(verify-guards fn-bpf-cut)

(defun fn-bpf-fragment (payload boundaries)
  (declare (xargs :guard t))
  (if (not (and (fn-cbor-octet-listp payload)
                (consp payload)
                (<= (len payload) *fn-bpf-max-length*)
                (fn-bpf-boundariesp boundaries 0 (len payload))
                (< (len boundaries) *fn-bpf-max-fragments*)))
      (list :invalid :bounds)
    (list :ok (fn-bpf-cut payload 0 boundaries (len payload)))))

(verify-guards fn-bpf-fragment)

; -----------------------------------------------------------------------------
; Fragment primary blocks (RFC 9171 section 5.8)
;
; The primary block of a fragment differs from that of the fragmented bundle
; only in the fragment flag, the fragment offset and the total application data
; unit length.  Everything the bundle's identity is built from -- source node
; ID, creation time, sequence number -- is carried across unchanged, and the
; CRC is recomputed by `fn-bpp-encode` because the block's bytes changed.

(defun fn-bpf-fragment-block (b offset total)
  (declare (xargs :guard (and (fn-bpp-blockp b) (natp offset) (natp total))))
  (fn-bpp-make-block
   (if (fn-bpp-fragmentp (fn-bpp-flags b))
       (fn-bpp-flags b)
     (+ (fn-bpp-flags b) *fn-bpp-flag-fragment*))
   (fn-bpp-crc-type b)
   (fn-bpp-destination b)
   (fn-bpp-source b)
   (fn-bpp-report-to b)
   (fn-bpp-creation-time b)
   (fn-bpp-sequence b)
   (fn-bpp-lifetime b)
   offset
   total))

(verify-guards fn-bpf-fragment-block)

; Section 5.8: any bundle whose flags do NOT forbid fragmentation MAY be
; fragmented.  A bundle with an anonymous source must set that flag
; (section 4.2.3), so an unidentifiable bundle is never fragmentable.
(defun fn-bpf-fragmentablep (b)
  (declare (xargs :guard (fn-bpp-blockp b)))
  (not (fn-bpp-no-fragmentp (fn-bpp-flags b))))

(verify-guards fn-bpf-fragmentablep)
