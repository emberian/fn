; Witnesses and teeth for BPv7 fragmentation and reassembly.
;
; The overlap witnesses are the point of this book.  RFC 9171 section 5.9 says
; fragments from different fragmentation episodes "may be overlapping subsets
; of the fragmented bundle's payload", so an identical overlap must reassemble
; and only differing bytes may conflict.

(in-package "ACL2")

(include-book "../../books/bp-fragment-invariants")
(include-book "std/testing/must-fail" :dir :system)

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

;   without `fn-bpf-covers-all`: a gap yields `:missing`, not `:ok`.
(local
 (must-fail
  (thm (implies (and (fn-cbor-octet-listp payload)
                     (fn-bpf-inputsp fs (len payload))
                     (fn-bpf-all-agreep fs payload))
                (equal (fn-bpf-reassemble fs (len payload))
                       (list :ok payload))))))

;   without `fn-bpf-inputsp`: an out-of-bounds input list is refused.
(local
 (must-fail
  (thm (implies (and (fn-cbor-octet-listp payload)
                     (fn-bpf-all-agreep fs payload)
                     (fn-bpf-covers-all fs (len payload)))
                (equal (fn-bpf-reassemble fs (len payload))
                       (list :ok payload))))))

;   without `fn-cbor-octet-listp` on the payload: agreement with a non-octet
;   list cannot produce that list back, because cells are octets.
(local
 (must-fail
  (thm (implies (and (fn-bpf-inputsp fs (len payload))
                     (fn-bpf-all-agreep fs payload)
                     (fn-bpf-covers-all fs (len payload)))
                (equal (fn-bpf-reassemble fs (len payload))
                       (list :ok payload))))))

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
;   with.
(local
 (must-fail
  (thm (implies (and (member-equal f fs)
                     (natp k)
                     (< k (len (fn-bpf-bytes f))))
                (equal (nth k (fn-bpf-bytes f))
                       (nth (+ (fn-bpf-offset f) k)
                            (fn-bpf-result-bytes
                             (fn-bpf-reassemble fs total))))))))

; fn-bpf-disagreeing-fragments-yield-conflict
;   without the disagreement hypothesis: identical overlap is not a conflict.
;   This is the theorem that distinguishes this lane from the transfer kernel.
(local
 (must-fail
  (thm (implies (and (fn-bpf-inputsp fs total)
                     (member-equal f fs)
                     (member-equal g fs)
                     (natp i) (< i total)
                     (not (equal (fn-bpf-cell-of f i) :gap))
                     (not (equal (fn-bpf-cell-of g i) :gap)))
                (equal (fn-bpf-result-tag (fn-bpf-reassemble fs total))
                       :conflict)))))

;   without `member-equal` for g: a fragment outside the list cannot force a
;   conflict inside it.
(local
 (must-fail
  (thm (implies (and (fn-bpf-inputsp fs total)
                     (member-equal f fs)
                     (natp i) (< i total)
                     (not (equal (fn-bpf-cell-of f i) :gap))
                     (not (equal (fn-bpf-cell-of g i) :gap))
                     (not (equal (fn-bpf-cell-of f i) (fn-bpf-cell-of g i))))
                (equal (fn-bpf-result-tag (fn-bpf-reassemble fs total))
                       :conflict)))))

; fn-bpf-missing-low-index-is-uncovered
;   without the `:missing` hypothesis.
(local
 (must-fail
  (thm (not (fn-bpf-coveredp
             fs (fn-bpf-result-bytes (fn-bpf-reassemble fs total)))))))

; fn-bpf-fragment-block-preserves-adu-key
;   without `fn-bpp-blockp`: a non-block has no fields to carry across.
(local
 (must-fail
  (thm (implies (and (natp offset) (natp total))
                (equal (fn-bpp-adu-key (fn-bpf-fragment-block b offset total))
                       (fn-bpp-adu-key b))))))
