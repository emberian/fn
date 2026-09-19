; Witnesses and teeth for BPv7 fragmentation and reassembly.
;
; The overlap witnesses are the point of this book.  RFC 9171 section 5.9 says
; fragments from different fragmentation episodes "may be overlapping subsets
; of the fragmented bundle's payload", so an identical overlap must reassemble
; and only differing bytes may conflict.

(in-package "ACL2")

(include-book "../../books/bp-fragment-invariants")
(include-book "std/testing/must-fail" :dir :system)
; codecs withdrew the record and cbor proof vocabularies at export (2026-09-19);
; this book reasons under them, so open them here, locally.
(local (in-theory (enable fn-cbor-record-vocabulary fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary)))

(defconst *bpf-payload* '(10 20 30 40 50 60 70 80))

(assert-event (fn-cbor-octet-listp *bpf-payload*))
(assert-event (equal (len *bpf-payload*) 8))

; -----------------------------------------------------------------------------
; Fragmentation at interior cut points 3 and 5

(defconst *bpf-cut*
  (nth 1 (fn-bpf-fragment *bpf-payload* '(3 5))))

(assert-event (equal (fn-bpf-fragment *bpf-payload* '(3 5))
                     (list :ok *bpf-cut*)))
(assert-event
 (equal *bpf-cut*
        (list '(:fn-bp-fragment 0 (10 20 30) 8)
              '(:fn-bp-fragment 3 (40 50) 8)
              '(:fn-bp-fragment 5 (60 70 80) 8))))
(assert-event (fn-bpf-fragment-listp *bpf-cut*))
(assert-event (fn-bpf-inputsp *bpf-cut* 8))
(assert-event (fn-bpf-all-agreep *bpf-cut* *bpf-payload*))
(assert-event (fn-bpf-covers-all *bpf-cut* 8))
(assert-event (equal (fn-bpf-reassemble *bpf-cut* 8)
                     (list :ok *bpf-payload*)))

; Any order works, because the reassembled array is specified index-wise.
(assert-event
 (equal (fn-bpf-reassemble (list (nth 2 *bpf-cut*)
                                 (nth 0 *bpf-cut*)
                                 (nth 1 *bpf-cut*))
                           8)
        (list :ok *bpf-payload*)))

; -----------------------------------------------------------------------------
; Byte-identical overlap reassembles.  fn's transfer kernel stalls on exactly
; this shape (`transfer.lisp` returns `:overlap-conflict` without comparing the
; bytes); this book does not.

(defconst *bpf-overlap*
  (list '(:fn-bp-fragment 0 (10 20 30 40 50) 8)
        '(:fn-bp-fragment 3 (40 50 60 70 80) 8)))

(assert-event (fn-bpf-inputsp *bpf-overlap* 8))
(assert-event (fn-bpf-all-agreep *bpf-overlap* *bpf-payload*))
(assert-event (fn-bpf-covers-all *bpf-overlap* 8))
; The overlap is real: indices 3 and 4 are covered by both fragments.
(assert-event (fn-bpf-coversp (nth 0 *bpf-overlap*) 4))
(assert-event (fn-bpf-coversp (nth 1 *bpf-overlap*) 4))
(assert-event (equal (fn-bpf-reassemble *bpf-overlap* 8)
                     (list :ok *bpf-payload*)))

; Total containment is also an overlap, and also reassembles.
(assert-event
 (equal (fn-bpf-reassemble
         (list '(:fn-bp-fragment 0 (10 20 30 40 50 60 70 80) 8)
               '(:fn-bp-fragment 2 (30 40) 8))
         8)
        (list :ok *bpf-payload*)))

; -----------------------------------------------------------------------------
; Differing bytes at one offset are a conflict, and the conflict names it.

(defconst *bpf-conflict*
  (list '(:fn-bp-fragment 0 (10 20 30 40 50) 8)
        '(:fn-bp-fragment 3 (40 99 60 70 80) 8)))

(assert-event (fn-bpf-inputsp *bpf-conflict* 8))
(assert-event (fn-bpf-covers-all *bpf-conflict* 8))
(assert-event (equal (fn-bpf-reassemble *bpf-conflict* 8) '(:conflict 4)))
; Index 3 is an identical overlap even inside a conflicting pair.
(assert-event (equal (fn-bpf-cell-at *bpf-conflict* 3) 40))
(assert-event (equal (fn-bpf-cell-at *bpf-conflict* 4) :conflict))

; -----------------------------------------------------------------------------
; An incomplete cover names the missing range.

(defconst *bpf-gap*
  (list '(:fn-bp-fragment 0 (10 20 30) 8)
        '(:fn-bp-fragment 5 (60 70 80) 8)))

(assert-event (fn-bpf-inputsp *bpf-gap* 8))
(assert-event (not (fn-bpf-covers-all *bpf-gap* 8)))
(assert-event (equal (fn-bpf-reassemble *bpf-gap* 8) '(:missing 3 5)))
(assert-event (not (fn-bpf-coveredp *bpf-gap* 3)))
(assert-event (not (fn-bpf-coveredp *bpf-gap* 4)))
(assert-event (fn-bpf-coveredp *bpf-gap* 5))

; A conflict is reported in preference to a gap.
(assert-event
 (equal (fn-bpf-reassemble
         (list '(:fn-bp-fragment 0 (10 20 30 40 50) 8)
               '(:fn-bp-fragment 3 (40 99) 8))
         8)
        '(:conflict 4)))

; -----------------------------------------------------------------------------
; Bounds are checked before any cell is built.

(assert-event (equal (fn-bpf-reassemble nil 8) '(:invalid :bounds)))
(assert-event (equal (fn-bpf-reassemble *bpf-cut* 0) '(:invalid :bounds)))
; A fragment that claims a different total ADU length is refused outright.
(assert-event
 (equal (fn-bpf-reassemble
         (list '(:fn-bp-fragment 0 (10 20 30) 8)
               '(:fn-bp-fragment 3 (40 50 60 70 80) 9))
         8)
        '(:invalid :bounds)))
; A fragment extending past the total ADU length is not a fragment at all.
(assert-event
 (not (fn-bpf-fragmentp '(:fn-bp-fragment 6 (70 80 90) 8))))
(assert-event
 (equal (fn-bpf-fragment '(10 20 30) '(3)) '(:invalid :bounds)))
(assert-event
 (equal (fn-bpf-fragment '(10 20 30) '(2 1)) '(:invalid :bounds)))

; -----------------------------------------------------------------------------
; Identity is preserved across fragmentation (RFC 9171 section 5.8)

(defconst *bpf-block*
  (fn-bpp-make-block 0 1 '(:dtn 47 47 110 50 47 105 110 98 111 120)
                     '(:dtn 47 47 110 49 47) '(:dtn 47 47 110 49 47)
                     2342 2 60000000 nil nil))

(assert-event (fn-bpp-blockp *bpf-block*))
(assert-event (fn-bpp-flags-conformantp *bpf-block*))
(assert-event (fn-bpf-fragmentablep *bpf-block*))
(assert-event (not (fn-bpp-fragmentp (fn-bpp-flags *bpf-block*))))

(defconst *bpf-block-0* (fn-bpf-fragment-block *bpf-block* 0 8))
(defconst *bpf-block-3* (fn-bpf-fragment-block *bpf-block* 3 8))

(assert-event (fn-bpp-blockp *bpf-block-0*))
(assert-event (fn-bpp-blockp *bpf-block-3*))
(assert-event (fn-bpp-fragmentp (fn-bpp-flags *bpf-block-0*)))
(assert-event (equal (fn-bpp-adu-key *bpf-block-0*)
                     (fn-bpp-adu-key *bpf-block*)))
(assert-event (equal (fn-bpp-adu-key *bpf-block-3*)
                     (fn-bpp-adu-key *bpf-block*)))
; The two fragments share an ADU key and differ in bundle identity, exactly as
; RFC 9171 section 4.3.1 requires -- and the payload length is what separates
; two fragments at the same offset, which the primary block does not carry.
(assert-event (not (equal (fn-bpp-bundle-id *bpf-block-0* 3)
                          (fn-bpp-bundle-id *bpf-block-3* 5))))
(assert-event (not (equal (fn-bpp-bundle-id *bpf-block-0* 3)
                          (fn-bpp-bundle-id *bpf-block-0* 5))))
(assert-event (fn-bpp-result-okp (fn-bpp-decode (fn-bpp-encode *bpf-block-0*))))
; The fragment's CRC differs from the fragmented bundle's: its bytes changed.
(assert-event (not (equal (fn-bpp-block-crc *bpf-block-0*)
                          (fn-bpp-block-crc *bpf-block*))))

; A bundle that must not be fragmented is refused, and an anonymous conformant
; bundle is always such a bundle.
(defconst *bpf-anon*
  (fn-bpp-make-block 4 1 '(:dtn 47 47 110 50 47) '(:dtn-none)
                     '(:dtn-none) 2342 2 60000000 nil nil))
(assert-event (fn-bpp-blockp *bpf-anon*))
(assert-event (fn-bpp-flags-conformantp *bpf-anon*))
(assert-event (not (fn-bpp-identifiablep *bpf-anon*)))
(assert-event (not (fn-bpf-fragmentablep *bpf-anon*)))

; -----------------------------------------------------------------------------
; Teeth.

; fn-bpf-complete-agreeing-cover-reassembles-to-payload
;   without `fn-bpf-all-agreep`: a cover of the right shape carrying other
;   bytes does not reassemble to this payload.
(local
 (must-fail
  (thm (implies (and (fn-cbor-octet-listp payload)
                     (fn-bpf-inputsp fs (len payload))
                     (fn-bpf-covers-all fs (len payload)))
                (equal (fn-bpf-reassemble fs (len payload))
                       (list :ok payload))))))

;   without `fn-bpf-covers-all`: a gap yields `:missing`, not `:ok`.  Stated
;   generally, the negated goal opens `fn-bpf-reassemble` past the rewriter's
;   call-depth limit -- a hard error, not a fast refutation -- so the tooth is
;   bitten by an instance: payload = *bpf-payload* and fs = *bpf-gap*, whose
;   two fragments agree with the payload and are in bounds but leave indices
;   3 and 4 uncovered.  The body is false: the reassembly is (:missing 3 5).
(assert-event
 (not (implies (and (fn-cbor-octet-listp *bpf-payload*)
                    (fn-bpf-inputsp *bpf-gap* (len *bpf-payload*))
                    (fn-bpf-all-agreep *bpf-gap* *bpf-payload*))
               (equal (fn-bpf-reassemble *bpf-gap* (len *bpf-payload*))
                      (list :ok *bpf-payload*)))))

;   without `fn-bpf-inputsp`: an out-of-bounds input list is refused.
(local
 (must-fail
  (thm (implies (and (fn-cbor-octet-listp payload)
                     (fn-bpf-all-agreep fs payload)
                     (fn-bpf-covers-all fs (len payload)))
                (equal (fn-bpf-reassemble fs (len payload))
                       (list :ok payload))))))

;   without `fn-cbor-octet-listp` on the payload: agreement with a non-octet
;   list cannot produce that list back, because cells are octets and the
;   canvas is a proper list.  Stated generally, the negated goal opens
;   `fn-bpf-reassemble` past the rewriter's call-depth limit -- a hard error,
;   not a fast refutation -- so the tooth is bitten by an instance: the
;   improper list (10 20 30 . 7) has length 3 and its first three elements are
;   octets, so a single fragment carrying (10 20 30) at offset 0 of total 3 is
;   in bounds, agrees with it and covers it.  The body is false: the
;   reassembly is (:ok (10 20 30)), which drops the 7 in the final cdr.
;   Evaluated logically, because an improper list is outside
;   `fn-bpf-all-agreep`'s guard -- which is the point.
(assert-event
 (with-guard-checking :none
  (not (fn-cbor-octet-listp '(10 20 30 . 7)))))
(assert-event
 (with-guard-checking :none
  (not (implies
        (and (fn-bpf-inputsp (list '(:fn-bp-fragment 0 (10 20 30) 3))
                             (len '(10 20 30 . 7)))
             (fn-bpf-all-agreep (list '(:fn-bp-fragment 0 (10 20 30) 3))
                                '(10 20 30 . 7))
             (fn-bpf-covers-all (list '(:fn-bp-fragment 0 (10 20 30) 3))
                                (len '(10 20 30 . 7))))
        (equal (fn-bpf-reassemble (list '(:fn-bp-fragment 0 (10 20 30) 3))
                                  (len '(10 20 30 . 7)))
               (list :ok '(10 20 30 . 7)))))))

; fn-bpf-reassemble-ok-agrees-with-every-fragment
;   without `member-equal`: a fragment that was not consumed says nothing.
;   Stated generally over free `fs` and `total`, the negated goal drives the
;   rewriter past its call-depth limit inside `fn-bpf-reassemble`, so the tooth
;   is bitten by an instance instead: the theorem body at fs = *bpf-cut*,
;   total = 8, k = 0 and a fragment f that is not in *bpf-cut* satisfies every
;   surviving hypothesis and is false, because f's byte 99 is not the
;   reassembled byte 10 at that offset.
(assert-event
 (not (implies (and (equal (fn-bpf-result-tag (fn-bpf-reassemble *bpf-cut* 8))
                           :ok)
                    (natp 0)
                    (< 0 (len (fn-bpf-bytes '(:fn-bp-fragment 0 (99) 8)))))
               (equal (nth 0 (fn-bpf-bytes '(:fn-bp-fragment 0 (99) 8)))
                      (nth (+ (fn-bpf-offset '(:fn-bp-fragment 0 (99) 8)) 0)
                           (fn-bpf-result-bytes
                            (fn-bpf-reassemble *bpf-cut* 8)))))))

;   without the `:ok` hypothesis: a refused reassembly has no output to agree
;   with.  Stated generally, the negated goal drives the rewriter past its
;   call-depth limit inside `fn-bpf-reassemble` just as the tooth above does,
;   so the tooth is bitten by an instance: fs = *bpf-gap*, total = 8, f the
;   first fragment of that list and k = 0 satisfy every surviving hypothesis
;   and the body is false, because the reassembly is (:missing 3 5), whose
;   "bytes" position is the index 3, and the nth of an index is nil rather
;   than the fragment's byte 10.  The body is evaluated logically, because
;   an index is not a byte list and `nth` of it is outside `nth`'s guard --
;   which is the point.
(assert-event (equal (fn-bpf-reassemble *bpf-gap* 8) '(:missing 3 5)))
(assert-event
 (with-guard-checking :none
  (not (implies
        (and (member-equal '(:fn-bp-fragment 0 (10 20 30) 8) *bpf-gap*)
             (natp 0)
             (< 0 (len (fn-bpf-bytes '(:fn-bp-fragment 0 (10 20 30) 8)))))
        (equal (nth 0 (fn-bpf-bytes '(:fn-bp-fragment 0 (10 20 30) 8)))
               (nth (+ (fn-bpf-offset '(:fn-bp-fragment 0 (10 20 30) 8)) 0)
                    (fn-bpf-result-bytes
                     (fn-bpf-reassemble *bpf-gap* 8))))))))

; fn-bpf-disagreeing-fragments-yield-conflict
;   without the disagreement hypothesis: identical overlap is not a conflict.
;   This is the theorem that distinguishes this lane from the transfer kernel.
;   Stated generally, the negated goal opens `fn-bpf-reassemble` past the
;   rewriter's call-depth limit, so the tooth is bitten by an instance:
;   fs = *bpf-overlap*, total = 8, f and g its two fragments and i = 4 satisfy
;   every surviving hypothesis -- both fragments carry a real byte at index 4
;   -- and the body is false, because that overlap is byte-identical and
;   reassembles :ok.
(assert-event
 (not (implies
       (and (fn-bpf-inputsp *bpf-overlap* 8)
            (member-equal (nth 0 *bpf-overlap*) *bpf-overlap*)
            (member-equal (nth 1 *bpf-overlap*) *bpf-overlap*)
            (natp 4) (< 4 8)
            (not (equal (fn-bpf-cell-of (nth 0 *bpf-overlap*) 4) :gap))
            (not (equal (fn-bpf-cell-of (nth 1 *bpf-overlap*) 4) :gap)))
       (equal (fn-bpf-result-tag (fn-bpf-reassemble *bpf-overlap* 8))
              :conflict))))

;   without `member-equal` for g: a fragment outside the list cannot force a
;   conflict inside it.  Stated generally the negated goal opens
;   `fn-bpf-reassemble` past the rewriter's call-depth limit, so the tooth is
;   bitten by an instance: fs = *bpf-cut*, total = 8, f its first fragment,
;   i = 0, and g a fragment carrying 99 at offset 0 that is not in the list.
;   Every surviving hypothesis holds and the two cells disagree, yet the body
;   is false, because *bpf-cut* reassembles :ok.
(assert-event (not (member-equal '(:fn-bp-fragment 0 (99) 8) *bpf-cut*)))
(assert-event
 (not (implies (and (fn-bpf-inputsp *bpf-cut* 8)
                    (member-equal (nth 0 *bpf-cut*) *bpf-cut*)
                    (natp 0) (< 0 8)
                    (not (equal (fn-bpf-cell-of (nth 0 *bpf-cut*) 0) :gap))
                    (not (equal (fn-bpf-cell-of '(:fn-bp-fragment 0 (99) 8) 0)
                                :gap))
                    (not (equal (fn-bpf-cell-of (nth 0 *bpf-cut*) 0)
                                (fn-bpf-cell-of '(:fn-bp-fragment 0 (99) 8)
                                                0))))
               (equal (fn-bpf-result-tag (fn-bpf-reassemble *bpf-cut* 8))
                      :conflict))))

; fn-bpf-missing-low-index-is-uncovered
;   without the `:missing` hypothesis: the second position of a result that is
;   not a gap report is not an uncovered index.  Stated generally the negated
;   goal opens `fn-bpf-reassemble` past the rewriter's call-depth limit, so
;   the tooth is bitten by an instance: fs = *bpf-conflict* and total = 8
;   reassemble to (:conflict 4), whose second position is the conflicting
;   index 4 -- and index 4 is covered, by both fragments.  Dropping the
;   hypothesis leaves the bare conclusion, so the witness asserts its negation
;   directly.
(assert-event (equal (fn-bpf-reassemble *bpf-conflict* 8) '(:conflict 4)))
(assert-event
 (fn-bpf-coveredp *bpf-conflict*
                  (fn-bpf-result-bytes (fn-bpf-reassemble *bpf-conflict* 8))))

; fn-bpf-fragment-block-preserves-adu-key
;   without `fn-bpp-blockp`: HYPOTHESIS UNNECESSARY for the conclusion, so
;   this tooth has no witness and is not claimed.  `fn-bpp-adu-key` reads
;   positions 4, 6 and 7 of the record -- source, creation time, sequence --
;   and `fn-bpf-fragment-block` copies exactly those three positions through
;   `fn-bpp-make-block`, which is a `list`; only the flags, the offset and the
;   total ADU length change.  The conclusion therefore holds for every `b`,
;   block or not, and the theorem keeps `fn-bpp-blockp` for its guard, not for
;   its truth.  The fact is proved here rather than asserted, so the claim is
;   checked:
(local
 (defthm fn-bpf-fragment-block-preserves-adu-key-for-any-object
   (equal (fn-bpp-adu-key (fn-bpf-fragment-block b offset total))
          (fn-bpp-adu-key b))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-bpp-adu-key fn-bpf-fragment-block
                                      fn-bpp-make-block fn-bpp-source
                                      fn-bpp-creation-time
                                      fn-bpp-sequence)))))
