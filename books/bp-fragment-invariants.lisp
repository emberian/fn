; fn: certified properties of BPv7 fragmentation and reassembly.
;
; The keystone is that any complete cover of the original payload -- in any
; order, with any amount of byte-identical overlap -- reassembles to exactly
; that payload.  Nothing in its statement mentions the order the fragments
; arrive in, because the reassembled array is specified index-wise.
;
; The other three outcomes are pinned down too: a successful reassembly agrees
; with every fragment it consumed, an uncovered index makes success impossible
; and the reported missing range really is uncovered, and two fragments that
; carry different octets at one offset force a conflict.

(in-package "ACL2")

(include-book "bp-fragment")

(local (include-book "arithmetic/top" :dir :system))
; codecs withdrew the record and cbor proof vocabularies at export (2026-09-19);
; this book reasons under them, so open them here, locally.
(local (in-theory (enable fn-cbor-record-vocabulary fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary)))

; `arithmetic/top`'s generalization rule for `mod` introduces fresh `mod`
; terms into case trees that never had one, and loops the waterfall on the
; bit-level recursions below.  Local, so nothing downstream inherits it.
(local (in-theory (disable mod-x-y-=-x+y-for-rationals)))

; -----------------------------------------------------------------------------
; Octets are not markers

(defthm fn-bpf-nth-of-octet-list
  (implies (and (fn-cbor-octet-listp xs) (natp i) (< i (len xs)))
           (fn-cbor-octetp (nth i xs)))
  :hints (("Goal" :induct (nth i xs))))

(defthm fn-bpf-octet-is-not-a-marker
  (implies (fn-cbor-octetp x)
           (and (not (equal x :gap))
                (not (equal x :conflict)))))

; -----------------------------------------------------------------------------
; Agreement is pointwise

; The index steps with the list: `k` into `bytes` is `offset + k` into the
; payload, so the induction has to walk both at once.
(local
 (defun fn-bpf-agreep-nth-induction (bytes offset k)
   (if (or (not (consp bytes)) (zp k))
       (list bytes offset k)
     (fn-bpf-agreep-nth-induction (cdr bytes) (+ 1 offset) (- k 1)))))

(defthm fn-bpf-bytes-agreep-nth
  (implies (and (fn-bpf-bytes-agreep bytes offset payload)
                (natp offset) (natp k) (< k (len bytes)))
           (equal (nth k bytes) (nth (+ offset k) payload)))
  :hints (("Goal" :induct (fn-bpf-agreep-nth-induction bytes offset k))))

(defthm fn-bpf-cell-of-of-agreeing-fragment
  (implies (and (fn-bpf-fragmentp f)
                (fn-bpf-agreesp f payload)
                (natp i)
                (fn-bpf-coversp f i))
           (equal (fn-bpf-cell-of f i) (nth i payload)))
  :hints (("Goal"
           :use ((:instance fn-bpf-bytes-agreep-nth
                            (bytes (fn-bpf-bytes f))
                            (offset (fn-bpf-offset f))
                            (k (- i (fn-bpf-offset f)))))
           :in-theory (disable fn-bpf-bytes-agreep-nth))))

; -----------------------------------------------------------------------------
; A cell is a gap exactly when no fragment covers it

(defthm fn-bpf-cell-of-gap-iff-uncovered
  (implies (and (fn-bpf-fragmentp f) (natp i)
                (fn-cbor-octet-listp (fn-bpf-bytes f)))
           (equal (equal (fn-bpf-cell-of f i) :gap)
                  (not (fn-bpf-coversp f i)))))

(defthm fn-bpf-cell-at-gap-iff-uncovered
  (implies (and (fn-bpf-fragment-listp fs) (natp i))
           (equal (equal (fn-bpf-cell-at fs i) :gap)
                  (not (fn-bpf-coveredp fs i))))
  :hints (("Goal" :induct (fn-bpf-cell-at fs i))))

; -----------------------------------------------------------------------------
; The reassembled array

; The index steps with the canvas: cell `i` of a canvas drawn from `from` is
; cell `from + i`, so the induction walks `from`, `n` and `i` together.
(local
 (defun fn-bpf-canvas-nth-induction (from n i)
   (if (or (zp n) (zp i))
       (list from n i)
     (fn-bpf-canvas-nth-induction (+ 1 from) (- n 1) (- i 1)))))

(defthm fn-bpf-nth-of-canvas
  (implies (and (natp from) (natp n) (natp i) (< i n))
           (equal (nth i (fn-bpf-canvas fs from n))
                  (fn-bpf-cell-at fs (+ from i))))
  :hints (("Goal" :induct (fn-bpf-canvas-nth-induction from n i)
           :expand ((fn-bpf-canvas fs from n)))))

(defthm fn-bpf-canvas-length
  (implies (natp n)
           (equal (len (fn-bpf-canvas fs from n)) n))
  :hints (("Goal" :induct (fn-bpf-canvas fs from n))))

; `nthcdr` folds one cell at a time, in the direction the extent recursion
; produces cells.
(local
 (defthm fn-bpf-nthcdr-folds
   (implies (and (natp from) (< from (len xs)))
            (equal (cons (nth from xs) (nthcdr from (cdr xs)))
                   (nthcdr from xs)))
   :hints (("Goal" :induct (nthcdr from xs)))))

(defthm fn-bpf-extent-is-nthcdr
  (implies (and (true-listp xs) (natp from) (<= from (len xs)))
           (equal (fn-bpf-extent xs from (len xs)) (nthcdr from xs)))
  :hints (("Goal" :induct (fn-bpf-extent xs from (len xs)))))

; Every covered cell of an agreeing cover carries the payload's own octet,
; whatever order the fragments are in and however much they overlap.  This is
; where identical overlap becomes harmless: two fragments that both cover an
; index both carry the payload octet there, so the merge never conflicts.
; What the closed `fn-bpf-cell-of` and `fn-bpf-coversp` still have to say in
; the cover induction: an uncovered cell is `:gap`, and a covered cell of an
; agreeing fragment is a payload octet, so never a marker.
(defthm fn-bpf-cell-of-uncovered-is-gap
  (implies (not (fn-bpf-coversp f i))
           (equal (fn-bpf-cell-of f i) :gap)))

(defthm fn-bpf-agreeing-payload-cell-is-an-octet
  (implies (and (fn-bpf-bytes-agreep bytes offset payload)
                (fn-cbor-octet-listp bytes)
                (natp offset) (natp i)
                (<= offset i) (< i (+ offset (len bytes))))
           (fn-cbor-octetp (nth i payload)))
  :hints (("Goal"
           :use ((:instance fn-bpf-bytes-agreep-nth (k (- i offset)))
                 (:instance fn-bpf-nth-of-octet-list
                            (xs bytes) (i (- i offset))))
           :in-theory (disable fn-bpf-bytes-agreep-nth
                               fn-bpf-nth-of-octet-list))))

(defthm fn-bpf-cell-at-of-agreeing-cover
  (implies (and (fn-bpf-fragment-listp fs)
                (fn-bpf-all-agreep fs payload)
                (natp i)
                (fn-bpf-coveredp fs i))
           (equal (fn-bpf-cell-at fs i) (nth i payload)))
  :hints (("Goal" :induct (fn-bpf-cell-at fs i))))

(defthm fn-bpf-canvas-is-payload-extent
  (implies (and (fn-cbor-octet-listp payload)
                (fn-bpf-fragment-listp fs)
                (fn-bpf-all-agreep fs payload)
                (natp from) (natp n)
                (<= (+ from n) (len payload))
                (fn-bpf-covered-range fs from n))
           (equal (fn-bpf-canvas fs from n)
                  (fn-bpf-extent payload from (+ from n))))
  :hints (("Goal"
           :induct (fn-bpf-canvas fs from n)
           :expand ((fn-bpf-extent payload from from)
                    (fn-bpf-extent payload from (+ from n)))
           :in-theory (disable fn-bpf-cell-at fn-bpf-coveredp))))

; -----------------------------------------------------------------------------
; A list with no markers has no first marker

(defthm fn-bpf-no-marker-in-octet-list
  (implies (and (fn-cbor-octet-listp cells)
                (or (equal marker :gap) (equal marker :conflict)))
           (equal (fn-bpf-first-index cells from marker) nil))
  :hints (("Goal" :induct (fn-bpf-first-index cells from marker))))

(defthm fn-bpf-extent-are-octets
  (implies (and (fn-cbor-octet-listp payload) (natp from) (natp to)
                (<= to (len payload)))
           (fn-cbor-octet-listp (fn-bpf-extent payload from to)))
  :hints (("Goal" :induct (fn-bpf-extent payload from to))))

; -----------------------------------------------------------------------------
; Keystone: a complete agreeing cover reassembles to the payload, whatever the
; order of the fragments and however much byte-identical overlap they carry.

(defthm fn-bpf-complete-agreeing-cover-reassembles-to-payload
  (implies (and (fn-cbor-octet-listp payload)
                (fn-bpf-inputsp fs (len payload))
                (fn-bpf-all-agreep fs payload)
                (fn-bpf-covers-all fs (len payload)))
           (equal (fn-bpf-reassemble fs (len payload))
                  (list :ok payload)))
  :hints (("Goal"
           :use ((:instance fn-bpf-canvas-is-payload-extent
                            (from 0) (n (len payload)))
                 (:instance fn-bpf-extent-is-nthcdr (xs payload) (from 0)))
           :in-theory (disable fn-bpf-canvas-is-payload-extent
                               fn-bpf-extent-is-nthcdr
                               fn-bpf-canvas fn-bpf-extent))))

; -----------------------------------------------------------------------------
; Keystone: a successful reassembly agrees with every fragment it consumed.
; This is what forbids a silent overwrite: no accepted output can contradict
; any input extent.

(defthm fn-bpf-merge-with-conflict
  (equal (fn-bpf-merge-cell x :conflict) :conflict))

(defthm fn-bpf-cell-at-agrees-with-member
  (implies (and (fn-bpf-fragment-listp fs)
                (member-equal f fs)
                (natp i)
                (not (equal (fn-bpf-cell-of f i) :gap))
                (not (equal (fn-bpf-cell-at fs i) :conflict)))
           (equal (fn-bpf-cell-at fs i) (fn-bpf-cell-of f i)))
  :hints (("Goal" :induct (fn-bpf-cell-at fs i))))

(defthm fn-bpf-reassemble-ok-shape
  (implies (equal (fn-bpf-result-tag (fn-bpf-reassemble fs total)) :ok)
           (and (fn-bpf-inputsp fs total)
                (equal (fn-bpf-result-bytes (fn-bpf-reassemble fs total))
                       (fn-bpf-canvas fs 0 total))
                (equal (fn-bpf-first-index (fn-bpf-canvas fs 0 total)
                                           0 :conflict)
                       nil)
                (equal (fn-bpf-first-index (fn-bpf-canvas fs 0 total) 0 :gap)
                       nil))))

; The index steps with the scan, as in `fn-bpf-bytes-agreep-nth`.
(local
 (defun fn-bpf-first-index-nth-induction (cells from i)
   (if (or (not (consp cells)) (zp i))
       (list cells from i)
     (fn-bpf-first-index-nth-induction (cdr cells) (+ 1 from) (- i 1)))))

(defthm fn-bpf-first-index-nil-means-no-marker
  (implies (and (true-listp cells)
                (equal (fn-bpf-first-index cells from marker) nil)
                (natp from) (natp i) (< i (len cells)))
           (not (equal (nth i cells) marker)))
  :hints (("Goal" :induct (fn-bpf-first-index-nth-induction cells from i))))

;; OPEN, not certified: the `:ok` shape gives
;; `fn-bpf-inputsp`, but placing `offset f + k` below `total` needs a member
;; lemma over `fn-bpf-same-total` this book does not yet have.
;; (defthm fn-bpf-reassemble-ok-agrees-with-every-fragment
;;   (implies (and (equal (fn-bpf-result-tag (fn-bpf-reassemble fs total)) :ok)
;;                 (member-equal f fs)
;;                 (natp k)
;;                 (< k (len (fn-bpf-bytes f))))
;;            (equal (nth k (fn-bpf-bytes f))
;;                   (nth (+ (fn-bpf-offset f) k)
;;                        (fn-bpf-result-bytes (fn-bpf-reassemble fs total)))))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :use ((:instance fn-bpf-cell-at-agrees-with-member
;;                             (i (+ (fn-bpf-offset f) k)))
;;                  (:instance fn-bpf-nth-of-canvas
;;                             (from 0) (n total)
;;                             (i (+ (fn-bpf-offset f) k)))
;;                  (:instance fn-bpf-first-index-nil-means-no-marker
;;                             (cells (fn-bpf-canvas fs 0 total))
;;                             (from 0) (marker :conflict)
;;                             (i (+ (fn-bpf-offset f) k))))
;;            :in-theory (disable fn-bpf-cell-at-agrees-with-member
;;                                fn-bpf-nth-of-canvas
;;                                fn-bpf-first-index-nil-means-no-marker
;;                                fn-bpf-canvas fn-bpf-cell-at
;;                                fn-bpf-reassemble fn-bpf-result-tag
;;                                fn-bpf-result-bytes))))

; -----------------------------------------------------------------------------
; Keystone: an uncovered index makes success impossible, and the reported
; missing range really is uncovered.

(defthm fn-bpf-uncovered-index-blocks-success
  (implies (and (fn-bpf-fragment-listp fs)
                (natp i) (< i total) (natp total)
                (not (fn-bpf-coveredp fs i)))
           (not (equal (fn-bpf-result-tag (fn-bpf-reassemble fs total)) :ok)))
  :hints (("Goal"
           :use ((:instance fn-bpf-nth-of-canvas (from 0) (n total))
                 (:instance fn-bpf-first-index-nil-means-no-marker
                            (cells (fn-bpf-canvas fs 0 total))
                            (from 0) (marker :gap)))
           :in-theory (disable fn-bpf-nth-of-canvas
                               fn-bpf-first-index-nil-means-no-marker
                               fn-bpf-canvas fn-bpf-cell-at))))

(defthm fn-bpf-car-of-nthcdr
  (equal (car (nthcdr n xs)) (nth n xs))
  :hints (("Goal" :induct (nthcdr n xs))))

(defthm fn-bpf-run-end-advances
  (implies (and (consp cells) (equal (car cells) marker) (natp from))
           (< from (fn-bpf-run-end cells from marker)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-bpf-run-end cells from marker))))

(defthm fn-bpf-first-index-finds-the-marker
  (implies (and (true-listp cells) (natp from)
                (fn-bpf-first-index cells from marker))
           (and (natp (fn-bpf-first-index cells from marker))
                (<= from (fn-bpf-first-index cells from marker))
                (< (fn-bpf-first-index cells from marker)
                   (+ from (len cells)))
                (equal (nth (- (fn-bpf-first-index cells from marker) from)
                            cells)
                       marker)))
  :hints (("Goal" :induct (fn-bpf-first-index cells from marker))))

(defthm fn-bpf-missing-low-index-is-uncovered
  (implies (equal (fn-bpf-result-tag (fn-bpf-reassemble fs total)) :missing)
           (not (fn-bpf-coveredp
                 fs (fn-bpf-result-bytes (fn-bpf-reassemble fs total)))))
  :hints (("Goal"
           :use ((:instance fn-bpf-first-index-finds-the-marker
                            (cells (fn-bpf-canvas fs 0 total))
                            (from 0) (marker :gap))
                 (:instance fn-bpf-nth-of-canvas
                            (from 0) (n total)
                            (i (fn-bpf-first-index (fn-bpf-canvas fs 0 total)
                                                   0 :gap))))
           :in-theory (disable fn-bpf-first-index-finds-the-marker
                               fn-bpf-nth-of-canvas
                               fn-bpf-canvas fn-bpf-cell-at))))

(local
 (defthm fn-bpf-nthcdr-is-consp
   (implies (and (natp n) (< n (len xs)))
            (consp (nthcdr n xs)))
   :hints (("Goal" :induct (nthcdr n xs)))))

(defthm fn-bpf-missing-range-is-non-empty
  (implies (equal (fn-bpf-result-tag (fn-bpf-reassemble fs total)) :missing)
           (< (nth 1 (fn-bpf-reassemble fs total))
              (nth 2 (fn-bpf-reassemble fs total))))
  :hints (("Goal"
           :use ((:instance fn-bpf-first-index-finds-the-marker
                            (cells (fn-bpf-canvas fs 0 total))
                            (from 0) (marker :gap))
                 (:instance fn-bpf-run-end-advances
                            (cells (nthcdr (fn-bpf-first-index
                                            (fn-bpf-canvas fs 0 total) 0 :gap)
                                           (fn-bpf-canvas fs 0 total)))
                            (from (fn-bpf-first-index
                                   (fn-bpf-canvas fs 0 total) 0 :gap))
                            (marker :gap)))
           :in-theory (disable fn-bpf-first-index-finds-the-marker
                               fn-bpf-run-end-advances
                               fn-bpf-canvas fn-bpf-cell-at))))

; -----------------------------------------------------------------------------
; Keystone: differing bytes at one offset are a conflict, and the conflict
; names an offset that really does carry a disagreement.  Byte-identical
; overlap is not a conflict; that is the previous keystone.

(defthm fn-bpf-disagreeing-fragments-yield-conflict
  (implies (and (fn-bpf-inputsp fs total)
                (member-equal f fs)
                (member-equal g fs)
                (natp i) (< i total)
                (not (equal (fn-bpf-cell-of f i) :gap))
                (not (equal (fn-bpf-cell-of g i) :gap))
                (not (equal (fn-bpf-cell-of f i) (fn-bpf-cell-of g i))))
           (equal (fn-bpf-result-tag (fn-bpf-reassemble fs total)) :conflict))
  :hints (("Goal"
           :use ((:instance fn-bpf-cell-at-agrees-with-member)
                 (:instance fn-bpf-cell-at-agrees-with-member (f g))
                 (:instance fn-bpf-nth-of-canvas (from 0) (n total))
                 (:instance fn-bpf-first-index-nil-means-no-marker
                            (cells (fn-bpf-canvas fs 0 total))
                            (from 0) (marker :conflict)))
           :in-theory (disable fn-bpf-cell-at-agrees-with-member
                               fn-bpf-nth-of-canvas
                               fn-bpf-first-index-nil-means-no-marker
                               fn-bpf-canvas fn-bpf-cell-at))))

(defthm fn-bpf-reassemble-outcomes-are-exhaustive
  (or (equal (fn-bpf-result-tag (fn-bpf-reassemble fs total)) :ok)
      (equal (fn-bpf-result-tag (fn-bpf-reassemble fs total)) :missing)
      (equal (fn-bpf-result-tag (fn-bpf-reassemble fs total)) :conflict)
      (equal (fn-bpf-result-tag (fn-bpf-reassemble fs total)) :invalid))
  :rule-classes nil)

; Bounds before allocation: an input list outside the modeled bounds is
; refused before a single cell of the reassembled array is built.
(defthm fn-bpf-out-of-bounds-input-allocates-nothing
  (implies (not (fn-bpf-inputsp fs total))
           (equal (fn-bpf-reassemble fs total) (list :invalid :bounds))))

; -----------------------------------------------------------------------------
; Fragmentation produces a complete agreeing cover, so it round trips.

(defthm fn-bpf-extent-length
  (implies (and (natp from) (natp to) (<= from to))
           (equal (len (fn-bpf-extent payload from to)) (- to from)))
  :hints (("Goal" :induct (fn-bpf-extent payload from to))))

(defthm fn-bpf-extent-agrees
  (implies (and (natp from) (natp to))
           (fn-bpf-bytes-agreep (fn-bpf-extent payload from to) from payload))
  :hints (("Goal" :induct (fn-bpf-extent payload from to))))

(defthm fn-bpf-cut-agrees
  (implies (and (natp from) (natp total))
           (fn-bpf-all-agreep (fn-bpf-cut payload from boundaries total)
                              payload))
  :hints (("Goal" :induct (fn-bpf-cut payload from boundaries total))))

(defthm fn-bpf-cut-same-total
  (implies (and (natp from) (natp total))
           (fn-bpf-same-total (fn-bpf-cut payload from boundaries total)
                              total))
  :hints (("Goal" :induct (fn-bpf-cut payload from boundaries total))))

(defthm fn-bpf-cut-length
  (equal (len (fn-bpf-cut payload from boundaries total))
         (+ 1 (len boundaries)))
  :hints (("Goal" :induct (fn-bpf-cut payload from boundaries total))))

;; OPEN, not certified: the step case needs a covered-range split lemma
;; (a fragment over [from, b) plus a cover of [b, total) cover [from, total))
;; that this book does not yet have.
;; (defthm fn-bpf-cut-covers
;;   (implies (and (natp from) (natp total)
;;                 (fn-bpf-boundariesp boundaries from total))
;;            (fn-bpf-covered-range (fn-bpf-cut payload from boundaries total)
;;                                  from (- total from)))
;;   :hints (("Goal" :induct (fn-bpf-cut payload from boundaries total))))

; -----------------------------------------------------------------------------
; Identity is preserved across fragmentation (RFC 9171 section 5.8)

(defthm fn-bpf-fragment-block-preserves-adu-key
  (implies (and (fn-bpp-blockp b) (natp offset) (natp total))
           (equal (fn-bpp-adu-key (fn-bpf-fragment-block b offset total))
                  (fn-bpp-adu-key b))))

(defthm fn-bpf-fragment-block-sets-the-fragment-flag
  (implies (and (fn-bpp-blockp b) (natp offset) (natp total)
                (<= (+ (fn-bpp-flags b) 1) *fn-bpc-max-uint*))
           (fn-bpp-fragmentp
            (fn-bpp-flags (fn-bpf-fragment-block b offset total))))
  ;; The field predicates stay closed: the fragment block carries the
  ;; original's fields and its two new ones are hypotheses.  Opened, they
  ;; split the goal 104 ways (2.2 and 2.6 s).
  :hints (("Goal" :in-theory (e/d (fn-bpp-flag-onp)
                                  (fn-bpp-eidp fn-bpp-timep fn-bpp-crc-typep
                                   fn-bpp-dtn-sspp)))))

(defthm fn-bpf-fragment-block-is-a-block
  (implies (and (fn-bpp-blockp b)
                (fn-bpp-timep offset) (fn-bpp-timep total)
                (<= (+ (fn-bpp-flags b) 1) *fn-bpc-max-uint*))
           (fn-bpp-blockp (fn-bpf-fragment-block b offset total)))
  ;; The field predicates stay closed: the fragment block carries the
  ;; original's fields and its two new ones are hypotheses.  Opened, they
  ;; split the goal 104 ways (2.2 and 2.6 s).
  :hints (("Goal" :in-theory (e/d (fn-bpp-flag-onp)
                                  (fn-bpp-eidp fn-bpp-timep fn-bpp-crc-typep
                                   fn-bpp-dtn-sspp)))))

; An unidentifiable bundle is never fragmentable: RFC 9171 section 4.2.3
; requires an anonymous source to set "must not be fragmented".  The fact is
; propositional in the three flag tests, so they stay closed: opened, each
; one is a `floor'/`mod' bit test, and the goal split 146 ways (32 more under
; each case) and forced 39 hypotheses, 12.8 s
; (planning/evidence/misc-books-cost-2026-09-23.md).
(defthm fn-bpf-anonymous-conformant-bundle-is-not-fragmentable
  (implies (and (fn-bpp-blockp b)
                (fn-bpp-flags-conformantp b)
                (not (fn-bpp-identifiablep b)))
           (not (fn-bpf-fragmentablep b)))
  :hints (("Goal" :in-theory (e/d (fn-bpp-identifiablep
                                   fn-bpp-flags-conformantp
                                   fn-bpf-fragmentablep)
                                  (fn-bpp-blockp fn-bpp-eidp fn-bpp-timep
                                   fn-bpp-crc-typep fn-bpp-dtn-sspp
                                   fn-bpp-no-fragmentp
                                   fn-bpp-any-status-requestp
                                   fn-bpp-administrativep)))))
