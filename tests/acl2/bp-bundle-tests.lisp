; Witnesses, interoperability vectors and teeth for the whole-bundle codec.
;
; The order is the one `docs/proof-style.md` section 6 fixes: guard-world
; audit, malformed-input regressions, scenarios, teeth.
;
; Golden vectors.  RFC 9171 publishes no example bundle -- its only worked
; numbers are the CRC check values `tests/acl2/bp-primary-tests.lisp` already
; pins -- so the external vector here is `*bpb-dtn7-0-21-0*` below: 132
; octets that **dtn7-rs 0.21.0 authored**, captured off the wire by `bp
; receive` before fn decoded anything, and inlined so that this book needs no
; file at certification time.
;
; THE HISTORY OF THIS PARAGRAPH, because it was false for three days and the
; correction is worth keeping.  Until 2026-09-21 it claimed exactly what it
; claims now and there was nothing behind it: `tests/bp-dtn7/golden/' did not
; exist on any ref, no octets were inlined, and every other vector in this
; book -- *bpb-primary*, *bpb-bundle*, *bpb-bundle-nocrc*, the three teeth
; bundles, *bpb-full* -- is BUILT by fn's own constructors and round-tripped
; through fn's own encoder and decoder, which is a self-consistency check of
; the codec and cannot disagree with another implementation.  Lane
; w11/phantom-cites found that and marked the paragraph an obligation rather
; than deleting it (`planning/lanes/HANDOFF-w11-phantom-cites.md`).  Lane
; w11/bp-node met the obligation: `tests/bp-dtn7/golden/` exists now, holds
; both captured images with their digests and the run that produced them, and
; the dtn7-authored one is inlined below.  The other vectors are still fn
; against fn and are still not interoperability evidence; this one is.
;
; Provenance, in one line, so a reader need not leave the book: hbox,
; 2026-09-21, `tests/bp-dtn7/run_fn_bp_interop.py` against dtn7-rs 0.21.0 at
; revision 4daf02d7ea927e9293753b2a5c4497457f6e5a40, image
; `build/fn-host-dtn`; the octets are SHA-256
; 3ba1d435188867c7f5b184cbb90dacacb73ec40865b60ece080af524583616df and are
; `tests/bp-dtn7/golden/dtn7-rs-0.21.0-authored.bundle` byte for byte.

(in-package "ACL2")

(include-book "../../books/bp-bundle-invariants")

; This book evaluates the codec, so it opens what the two books withdrew.
(local (in-theory (enable fn-bpb-vocabulary fn-bpb-invariants-vocabulary
                          fn-cbor-record-vocabulary fn-cbor-codec-vocabulary)))

; -----------------------------------------------------------------------------
; Guard-world audit.  The two decoders take a peer's octets, so their guards
; are `fn-cbor-octet-listp` and a natural bound and nothing stronger: a
; decoder guarded by a property of what it is about to decode would be
; assuming its own conclusion.  The encoders are guarded by the record
; recognizers, which is what makes an unencodable value unrepresentable.

(assert-event (equal (symbol-class 'fn-bpb-decode (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-bpb-decode nil (w state))
                     '(if (fn-cbor-octet-listp octets) (natp limit) 'nil)))
(assert-event (equal (symbol-class 'fn-bpb-decode-block (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-bpb-decode-block nil (w state))
                     '(fn-cbor-octet-listp octets)))
(assert-event (equal (symbol-class 'fn-bpb-encode (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-bpb-encode nil (w state))
                     '(fn-bpb-bundlep bundle)))
(assert-event (equal (symbol-class 'fn-bpb-encode-block (w state)) :common-lisp-compliant))
(assert-event (equal (symbol-class 'fn-bpb-block-crc (w state)) :common-lisp-compliant))

; -----------------------------------------------------------------------------
; The interoperability vector: a bundle a FOREIGN encoder wrote.
;
; dtn7-rs 0.21.0 authored these 132 octets for `dtn://fn-b/incoming` and put
; them on an RFC 9174 session with fn; `bp receive` journalled them as they
; arrived, before the node was asked what it made of them, and
; `tests/bp-dtn7/golden/dtn7-rs-0.21.0-authored.bundle` is that file.  The
; assertions below are the only ones in this book that can fail because fn
; and another implementation disagree.
;
; What they say, and each is a distinct claim:
;
;   * fn's decoder ACCEPTS it, so fn parses what dtn7-rs writes;
;   * the fields it recovers are the ones dtn7-rs sent -- source
;     `dtn://dtn7x/`, destination `dtn://fn-b/incoming`, the payload text --
;     so fn agrees about what the octets MEAN and not merely that they parse;
;   * fn's ENCODER reproduces them byte for byte, so the deterministic
;     spelling `fn-bpb-decode` insists on (RFC 9171 section 4.1, RFC 8949
;     section 4.2) is the spelling dtn7-rs actually emits.  This is the
;     strongest of the three and the one a canonicality bug would break;
;   * two extension blocks dtn7-rs chose to include -- previous-node (type 6)
;     and hop count (type 10) -- survive the round trip in its order.
;
; The primary block carries no CRC (CRC type 0) and flags 131076, which is
; `no-fragment` (4) plus `report-delivery` (131072): dtn7-rs's defaults, not
; fn's, which is part of what makes this a vector rather than a mirror.

(defconst *bpb-dtn7-0-21-0*
  '(
   159 136 7 26 0 2 0 4 0 130 1 111
   47 47 102 110 45 98 47 105 110 99 111 109
   105 110 103 130 1 104 47 47 100 116 110 55
   120 47 130 1 104 47 47 100 116 110 55 120
   47 130 27 0 0 0 196 86 239 187 59 0
   26 0 54 238 128 133 6 3 0 0 75 130
   1 104 47 47 100 116 110 55 120 47 133 10
   2 0 0 68 130 24 32 1 133 1 1 0
   0 88 32 100 116 110 55 32 45 62 32 102
   110 44 32 100 101 99 111 100 101 100 32 97
   115 32 97 32 98 117 110 100 108 101 10 255))

(assert-event (equal (len *bpb-dtn7-0-21-0*) 132))
(assert-event (fn-cbor-octet-listp *bpb-dtn7-0-21-0*))

; It decodes.
(assert-event (fn-cbor-result-okp (fn-bpb-decode *bpb-dtn7-0-21-0* 1048576)))

(defconst *bpb-dtn7-decoded*
  (fn-cbor-result-value (fn-bpb-decode *bpb-dtn7-0-21-0* 1048576)))

(assert-event (fn-bpb-bundlep *bpb-dtn7-decoded*))

; The fields are dtn7-rs's, not fn's.
(assert-event
 (equal (fn-bpp-source (fn-bpb-bundle-primary *bpb-dtn7-decoded*))
        (cons :dtn '(47 47 100 116 110 55 120 47))))          ; dtn://dtn7x/
(assert-event
 (equal (fn-bpp-destination (fn-bpb-bundle-primary *bpb-dtn7-decoded*))
        (cons :dtn '(47 47 102 110 45 98 47
                     105 110 99 111 109 105 110 103))))       ; dtn://fn-b/incoming
(assert-event
 (equal (fn-bpp-crc-type (fn-bpb-bundle-primary *bpb-dtn7-decoded*)) 0))
(assert-event
 (equal (fn-bpp-flags (fn-bpb-bundle-primary *bpb-dtn7-decoded*)) 131076))
(assert-event
 (fn-bpp-no-fragmentp (fn-bpp-flags (fn-bpb-bundle-primary *bpb-dtn7-decoded*))))
(assert-event
 (not (fn-bpp-fragmentp (fn-bpp-flags (fn-bpb-bundle-primary *bpb-dtn7-decoded*)))))

; "dtn7 -> fn, decoded as a bundle\n"
(assert-event
 (equal (fn-bpb-payload *bpb-dtn7-decoded*)
        '(100 116 110 55 32 45 62 32 102 110 44 32 100 101 99 111 100 101
          100 32 97 115 32 97 32 98 117 110 100 108 101 10)))

; The two extension blocks dtn7-rs included, in its order: previous-node
; (type 6, block number 3) and hop count (type 10, block number 2).
(assert-event
 (equal (fn-bpb-block-numbers (fn-bpb-bundle-blocks *bpb-dtn7-decoded*))
        '(3 2)))
(assert-event
 (equal (fn-bpb-block-type (car (fn-bpb-bundle-blocks *bpb-dtn7-decoded*))) 6))
(assert-event
 (equal (fn-bpb-block-type (car (cdr (fn-bpb-bundle-blocks *bpb-dtn7-decoded*))))
        10))

; And fn re-encodes dtn7-rs's bundle byte for byte: the deterministic
; spelling this decoder insists on is the one dtn7-rs emits.
(assert-event (equal (fn-bpb-encode *bpb-dtn7-decoded*) *bpb-dtn7-0-21-0*))

; The bound is applied before the first octet is examined, on a real foreign
; bundle and not only on a fabricated one.
(assert-event
 (equal (fn-cbor-result-value (fn-bpb-decode *bpb-dtn7-0-21-0* 16)) :limit))

; -----------------------------------------------------------------------------
; A witness bundle: fn-a to fn-b, a CRC32C primary block, a hop-count and a
; bundle-age extension block, and a two-octet payload.

(defconst *bpb-eid-a* (cons :dtn '(47 47 102 110 45 97 47)))   ; dtn://fn-a/
(defconst *bpb-eid-b* (cons :dtn '(47 47 102 110 45 98 47)))   ; dtn://fn-b/

(assert-event (fn-bpp-eidp *bpb-eid-a*))
(assert-event (fn-bpp-eidp *bpb-eid-b*))
(assert-event (fn-bpp-eid-node-idp *bpb-eid-a*))

(defconst *bpb-primary*
  (fn-bpp-make-block 0 2 *bpb-eid-b* *bpb-eid-a* *bpb-eid-a*
                     1000 1 3600000 nil nil))

(assert-event (fn-bpp-blockp *bpb-primary*))

(defconst *bpb-hop* (fn-bpb-hop-count-block 2 0 1 (fn-bpp-make-hop-count 32 0)))
(defconst *bpb-age* (fn-bpb-bundle-age-block 3 0 1 0))
(defconst *bpb-prev* (fn-bpb-previous-node-block 4 0 0 *bpb-eid-a*))
(defconst *bpb-payload-block* (fn-bpb-payload-block 2 '(104 105)))

(assert-event (fn-bpb-blockp *bpb-hop*))
(assert-event (fn-bpb-blockp *bpb-age*))
(assert-event (fn-bpb-blockp *bpb-prev*))
(assert-event (fn-bpb-payload-blockp *bpb-payload-block*))

(defconst *bpb-bundle*
  (fn-bpb-make-bundle *bpb-primary* (list *bpb-hop* *bpb-age* *bpb-prev*)
                      *bpb-payload-block*))

(assert-event (fn-bpb-bundlep *bpb-bundle*))

; -----------------------------------------------------------------------------
; Scenario: the round trip is reachable and non-degenerate.

(assert-event (equal (car (fn-bpb-encode *bpb-bundle*)) 159))
(assert-event (fn-cbor-octet-listp (fn-bpb-encode *bpb-bundle*)))
(assert-event (< 60 (len (fn-bpb-encode *bpb-bundle*))))

(assert-event
 (fn-cbor-result-okp (fn-bpb-decode (fn-bpb-encode *bpb-bundle*)
                                    *fn-bpb-max-input*)))

(assert-event
 (equal (fn-cbor-result-value (fn-bpb-decode (fn-bpb-encode *bpb-bundle*)
                                             *fn-bpb-max-input*))
        *bpb-bundle*))

; Non-degenerate: the decoded bundle carries the three extension blocks, and
; the projections read them back through the section 4.4 data decoders.
(assert-event (equal (len (fn-bpb-bundle-blocks *bpb-bundle*)) 3))
(assert-event (equal (fn-bpb-bundle-hop-count *bpb-bundle*)
                     (fn-bpp-make-hop-count 32 0)))
(assert-event (equal (fn-bpb-bundle-age *bpb-bundle*) 0))
(assert-event (equal (fn-bpb-bundle-previous-node *bpb-bundle*) *bpb-eid-a*))
(assert-event (equal (fn-bpb-payload *bpb-bundle*) '(104 105)))

; A CRC-less bundle round-trips too, so the five-element block frame is
; exercised and not only the six-element one.
(defconst *bpb-bundle-nocrc*
  (fn-bpb-make-bundle
   (fn-bpp-make-block 0 0 *bpb-eid-b* *bpb-eid-a* *bpb-eid-a* 1000 2 3600000
                      nil nil)
   nil
   (fn-bpb-payload-block 0 '(104 105))))

(assert-event (fn-bpb-bundlep *bpb-bundle-nocrc*))
(assert-event
 (equal (fn-cbor-result-value (fn-bpb-decode (fn-bpb-encode *bpb-bundle-nocrc*)
                                             *fn-bpb-max-input*))
        *bpb-bundle-nocrc*))
(assert-event (equal (car (fn-bpb-encode-block
                           (fn-bpb-bundle-payload *bpb-bundle-nocrc*)))
                     133))
(assert-event (equal (car (fn-bpb-encode-block *bpb-payload-block*)) 134))

; -----------------------------------------------------------------------------
; Teeth for `fn-bpb-decode-of-encode`, one concrete violating value per
; hypothesis.

; Hypothesis `fn-bpb-bundlep`: a payload block that is not block number 1
; violates RFC 9171 section 4.1, and the forged value does not round-trip.
(defconst *bpb-teeth-payload-misnumbered*
  (fn-bpb-make-bundle *bpb-primary* nil
                      (fn-bpb-make-block 1 7 0 2 '(104 105))))

(assert-event (not (fn-bpb-bundlep *bpb-teeth-payload-misnumbered*)))
(assert-event
 (with-guard-checking :none
  (not (equal (fn-cbor-result-value
               (fn-bpb-decode (fn-bpb-encode *bpb-teeth-payload-misnumbered*)
                              *fn-bpb-max-input*))
              *bpb-teeth-payload-misnumbered*))))

; Hypothesis `fn-bpb-bundlep`, the distinct-numbers conjunct: two canonical
; blocks numbered 2.
(defconst *bpb-teeth-duplicate-numbers*
  (fn-bpb-make-bundle *bpb-primary* (list *bpb-hop* *bpb-hop*)
                      *bpb-payload-block*))

(assert-event (not (fn-bpb-bundlep *bpb-teeth-duplicate-numbers*)))
(assert-event
 (with-guard-checking :none
  (not (fn-cbor-result-okp
        (fn-bpb-decode (fn-bpb-encode *bpb-teeth-duplicate-numbers*)
                       *fn-bpb-max-input*)))))

; Hypothesis `(fn-cbor-at-mostp (fn-bpb-encode bundle) limit)`: the bound is
; applied before the first octet is examined, so a bundle larger than the
; caller's limit is refused as `:limit` and not as anything else.
(assert-event
 (equal (fn-bpb-decode (fn-bpb-encode *bpb-bundle*) 8)
        (fn-cbor-error :limit)))

; -----------------------------------------------------------------------------
; Teeth for the block frame: each refusal has its own reason, and the three
; outcomes a caller reports stay distinct.

; A CRC that does not match the block's own zero-filled encoding.
(defconst *bpb-teeth-crc-broken*
  (append (fn-bpb-front (fn-bpb-encode-block *bpb-hop*))
          (list (mod (+ 1 (fn-bpb-final (fn-bpb-encode-block *bpb-hop*))) 256))))

(assert-event (equal (fn-bpb-decode-block (fn-bpb-encode-block *bpb-hop*))
                     (fn-cbor-ok *bpb-hop* nil)))
(assert-event (equal (fn-cbor-result-value
                      (fn-bpb-decode-block *bpb-teeth-crc-broken*))
                     :crc-mismatch))

; A non-deterministic spelling of the block type code: 0x18 0x01 where 0x01 is
; the shortest form.  RFC 9171 section 4.1 requires the deterministic
; encoding, so this is `:noncanonical` and not `:malformed`.
(assert-event
 (equal (fn-cbor-result-value
         (fn-bpb-decode-block (list 133 24 1 2 0 0 66 104 105)))
        :noncanonical))

; A truncated block.
(assert-event
 (equal (fn-cbor-result-value (fn-bpb-decode-block (list 133 1 1 0)))
        :truncated))

; A declared byte-string length above the per-block bound is refused from the
; length alone: the input here is ten octets, not a mebibyte.  The head is
; 90 = 64 + 26, major type 2 with a four-octet argument (RFC 8949 section
; 3), and 0xFFFFFFFF is above `*fn-bpb-max-data*`.  This assertion had 26
; rather than 90 until 2026-09-20 and had never run, because the book above
; it did not certify; 26 is major type 0, so what it actually measured was
; the refusal below.
(assert-event
 (equal (fn-cbor-result-value
         (fn-bpb-decode-block (list 133 1 1 0 0 90 255 255 255 255)))
        :limit))

; And the same octets with a major-type-0 head where the data byte string
; belongs: a different refusal, kept distinct rather than collapsed.
(assert-event
 (equal (fn-cbor-result-value
         (fn-bpb-decode-block (list 133 1 1 0 0 26 255 255 255 255)))
        :not-a-byte-string))

; A head that is not a five- or six-element definite array.
(assert-event
 (equal (fn-bpb-decode-block (list 159 1 1 0 0 66 104 105))
        (fn-cbor-error :malformed)))

; A bundle with no payload block at all.
; The empty bundle array is `:malformed`, NOT `:primary-block-refused`: the
; break octet is not the start of a CBOR item, so `fn-bpc-dec` refuses before
; `fn-bpp-decode` is ever reached.  This assertion said
; `:primary-block-refused` until 2026-09-20 and had never run.  The witness
; for that reason is the line below it: `(0)` IS a CBOR item, so the scan
; hands it to `fn-bpp-decode`, which is what refuses.
(assert-event
 (equal (fn-bpb-decode (list 159 255) *fn-bpb-max-input*)
        (fn-cbor-error :malformed)))

(assert-event
 (equal (fn-bpb-decode (list 159 0 255) *fn-bpb-max-input*)
        (fn-cbor-error :primary-block-refused)))

; Octets after the break.
(assert-event
 (not (fn-cbor-result-okp
       (fn-bpb-decode (append (fn-bpb-encode *bpb-bundle*) (list 0))
                      *fn-bpb-max-input*))))

; -----------------------------------------------------------------------------
; Block count.  A bundle carrying more canonical blocks than the frame accepts
; is refused by the budget, and the budget is what refuses it.

(assert-event
 (equal (fn-cbor-result-value
         (fn-bpb-decode-blocks (fn-bpb-encode-block *bpb-hop*) 0))
        :too-many-blocks))

; The boundary the round trip found (w10/dtn-3).  A bundle carrying the full
; `*fn-bpb-max-blocks*` canonical blocks is an array of that many PLUS the
; payload block, so a decoder budgeted at `*fn-bpb-max-blocks*` refuses its
; own encoder's output: `fn-bpb-decode-of-encode` is false at exactly this
; value.  `fn-bpb-decode` now budgets `(+ 1 *fn-bpb-max-blocks*)`, and this
; is the witness at the boundary.
(defun fn-bpbt-filler-blocks (n)
  (declare (xargs :guard (and (natp n) (<= n 1000))))
  (if (zp n)
      nil
    (cons (fn-bpb-bundle-age-block (+ 1 (nfix n)) 0 0 0)
          (fn-bpbt-filler-blocks (- (nfix n) 1)))))

(defconst *bpb-full*
  (fn-bpb-make-bundle *bpb-primary* (fn-bpbt-filler-blocks *fn-bpb-max-blocks*)
                      *bpb-payload-block*))

(assert-event (equal (len (fn-bpb-bundle-blocks *bpb-full*))
                     *fn-bpb-max-blocks*))
(assert-event (fn-bpb-bundlep *bpb-full*))
(assert-event (equal (fn-bpb-decode (fn-bpb-encode *bpb-full*)
                                    *fn-bpb-max-input*)
                     (fn-cbor-ok *bpb-full* nil)))

; And one canonical block more is still refused, by the budget, one block
; later: the bound on canonical blocks is not loosened by counting the
; payload.
(defconst *bpb-over-full*
  (fn-bpb-make-bundle *bpb-primary*
                      (fn-bpbt-filler-blocks (+ 1 *fn-bpb-max-blocks*))
                      *bpb-payload-block*))

(assert-event (not (fn-bpb-bundlep *bpb-over-full*)))
(assert-event
 (with-guard-checking :none
  (equal (fn-cbor-result-value
          (fn-bpb-decode (fn-bpb-encode *bpb-over-full*) *fn-bpb-max-input*))
         :too-many-blocks)))
