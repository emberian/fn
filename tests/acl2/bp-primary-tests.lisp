; Witnesses, interoperability vectors and teeth for the BPv7 primary block.
;
; CRC vectors.  RFC 9171 section 4.2.1 names two algorithms and supplies no
; vectors of its own; it points at [CRC16] for the X-25 CRC-16 and at RFC 4960
; for CRC32C.  Two independent sources are used here.
;
;   1. The check values of the two named algorithms over the ASCII string
;      "123456789": 0x906E for CRC-16/IBM-SDLC (X-25) and 0xE3069283 for
;      CRC-32/ISCSI (CRC32C).  These are the catalogue check constants for the
;      exact parameter sets RFC 9171 section 4.2.1 names.
;
;   2. The two worked primary-block CRCs published by the pinned BPv7
;      implementation: crate `bp7` version 0.10.7, which is the version
;      `Cargo.lock` pins for dtn7-rs at revision
;      4daf02d7ea927e9293753b2a5c4497457f6e5a40 (`tests/bp-dtn7/pin.json`).
;      Its `doc/encoding_samples.md` publishes a primary block with CRC 16
;      ending `42 e7ca` and the same block with CRC 32 ending `44 ca4fc368`.
;      The octets below are those published blocks with the CRC field zeroed,
;      which is the input RFC 9171 section 4.3.1 prescribes.
;
;      That sample block's dtn endpoint IDs carry the scheme-specific part
;      without its leading "//".  The same crate's current `eid.rs` encodes the
;      complete SSP (its own decoding test uses `82 01 6c "//node1/test"`), and
;      RFC 9171 section 4.2.5.1.1 requires the complete SSP, so fn's decoder
;      refuses that sample block as a block.  The CRC vector is still exact
;      over those octets, which is what is being checked here; fn's own
;      complete-block vectors follow it.

(in-package "ACL2")

(include-book "../../books/bp-primary-invariants")
; codecs withdrew the record and cbor proof vocabularies at export (2026-09-19);
; this book reasons under them, so open them here, locally.
(local (in-theory (enable fn-cbor-record-vocabulary fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary)))

; -----------------------------------------------------------------------------
; CRC algorithm vectors

(assert-event (equal (fn-bpp-crc16 '(49 50 51 52 53 54 55 56 57)) 36974))
(assert-event (equal (fn-bpp-crc32c '(49 50 51 52 53 54 55 56 57)) 3808858755))
(assert-event (equal (fn-bpp-crc16 nil) 0))
(assert-event (equal (fn-bpp-crc32c nil) 0))

(defconst *bp7-sample-crc16-zeroed*
  '(137 7 0 1 130 1 104 110 50 47 105 110 98 111 120 130 1 98 110 49
    130 1 98 110 49 130 25 9 38 2 26 3 147 135 0 66 0 0))
(defconst *bp7-sample-crc32-zeroed*
  '(137 7 0 2 130 1 104 110 50 47 105 110 98 111 120 130 1 98 110 49
    130 1 98 110 49 130 25 9 38 2 26 3 147 135 0 68 0 0 0 0))

(assert-event (equal (fn-bpp-crc16 *bp7-sample-crc16-zeroed*) 59338))
(assert-event (equal (fn-cbor-u16-bytes 59338) '(231 202)))
(assert-event (equal (fn-bpp-crc32c *bp7-sample-crc32-zeroed*) 3394225000))
(assert-event (equal (fn-cbor-u32-bytes 3394225000) '(202 79 195 104)))

; That sample block is not accepted as a block: its dtn SSPs omit the "//".
(assert-event (not (fn-bpp-dtn-sspp '(110 50 47 105 110 98 111 120))))
(assert-event (fn-bpp-dtn-sspp '(47 47 110 50 47 105 110 98 111 120)))

; -----------------------------------------------------------------------------
; The CBOR vocabulary RFC 9171 section 4.3.1 needs, and nothing else

; Unsigned integers to 2^64-1 (additional information 27), which the original
; profile answers `:unsupported` for.
(assert-event (equal (fn-cbor-decode-exact '(27 255 255 255 255 255 255 255 255))
                     '(:error :unsupported)))
(assert-event (equal (fn-bpc-decode-exact '(27 255 255 255 255 255 255 255 255))
                     (list :ok (cons :uint 18446744073709551615) nil)))
(assert-event (equal (fn-bpc-encode (cons :uint 18446744073709551615))
                     '(27 255 255 255 255 255 255 255 255)))
(assert-event (equal (fn-bpc-decode-exact '(27 0 0 0 1 0 0 0 0))
                     (list :ok (cons :uint 4294967296) nil)))
; A 2^64 value is outside the profile and has no encoding.
(assert-event (not (fn-bpc-valuep (cons :uint 18446744073709551616))))

; Definite text strings and definite arrays of bounded arity.
(assert-event (equal (fn-bpc-decode-exact '(99 97 98 99))
                     (list :ok (cons :text '(97 98 99)) nil)))
(assert-event (equal (fn-bpc-decode-exact '(130 1 2))
                     (list :ok (list :array (cons :uint 1) (cons :uint 2))
                           nil)))
(assert-event (equal (fn-bpc-decode-exact '(130 1 130 2 3))
                     (list :ok (list :array (cons :uint 1)
                                     (list :array (cons :uint 2)
                                           (cons :uint 3)))
                           nil)))

; Non-minimal arguments are refused, not normalised (RFC 8949 section 4.2.1).
(assert-event (equal (fn-bpc-decode-exact '(24 7)) '(:error :noncanonical)))
(assert-event (equal (fn-bpc-decode-exact '(27 0 0 0 0 0 0 0 7))
                     '(:error :noncanonical)))
(assert-event (equal (fn-bpc-decode-exact '(25 0 7)) '(:error :noncanonical)))

; Indefinite lengths, negative integers, maps, tags and floats stay outside.
(assert-event (equal (fn-bpc-decode-exact '(159 1 255)) '(:error :unsupported)))
(assert-event (equal (fn-bpc-decode-exact '(32)) '(:error :unsupported)))
(assert-event (equal (fn-bpc-decode-exact '(160)) '(:error :unsupported)))
(assert-event (equal (fn-bpc-decode-exact '(192 1)) '(:error :unsupported)))
(assert-event (equal (fn-bpc-decode-exact '(250 0 0 0 0)) '(:error :unsupported)))

; Bounds are checked before allocation: an arity of 17 and a claimed text
; length of 2000 are both refused with no element or octet copied.
(assert-event (equal (fn-bpc-decode-exact '(145)) '(:error :limit)))
(assert-event (equal (fn-bpc-decode-exact '(121 7 208)) '(:error :limit)))
(assert-event (equal (fn-bpc-decode-exact '(130 1)) '(:error :truncated)))
(assert-event (equal (fn-bpc-decode-exact '(1 1)) '(:error :trailing)))
(assert-event (equal (fn-bpc-dec :item 0 '(1) 0) '(:error :budget)))

; -----------------------------------------------------------------------------
; A complete primary block: dtn endpoint IDs, CRC-16, not a fragment

(defconst *bpp-dtn-inbox* '(:dtn 47 47 110 50 47 105 110 98 111 120))
(defconst *bpp-dtn-n1* '(:dtn 47 47 110 49 47))

(defconst *bpp-block-a*
  (fn-bpp-make-block 0 1 *bpp-dtn-inbox* *bpp-dtn-n1* *bpp-dtn-n1*
                     2342 2 60000000 nil nil))

(defconst *bpp-octets-a*
  '(137 7 0 1 130 1 106 47 47 110 50 47 105 110 98 111 120
    130 1 101 47 47 110 49 47 130 1 101 47 47 110 49 47
    130 25 9 38 2 26 3 147 135 0 66 3 151))

(assert-event (fn-bpp-blockp *bpp-block-a*))
(assert-event (fn-bpp-flags-conformantp *bpp-block-a*))
(assert-event (fn-bpp-eid-singletonp *bpp-dtn-inbox*))
(assert-event (fn-bpp-eid-node-idp *bpp-dtn-n1*))
(assert-event (not (fn-bpp-eid-node-idp *bpp-dtn-inbox*)))
(assert-event (equal (fn-bpp-encode *bpp-block-a*) *bpp-octets-a*))
(assert-event (equal (fn-bpp-decode *bpp-octets-a*) (list :ok *bpp-block-a*)))
(assert-event (equal (fn-bpp-block-crc *bpp-block-a*) '(3 151)))

; A non-singleton dtn endpoint: the demux begins with '~'.
(assert-event (not (fn-bpp-eid-singletonp '(:dtn 47 47 110 49 47 126 109))))

; -----------------------------------------------------------------------------
; ipn endpoint IDs, CRC32C, and a creation timestamp that needs 64 bits
; (1577836800000 ms after the DTN epoch is 2050-01-01T00:00:00Z)

(defconst *bpp-block-b*
  (fn-bpp-make-block 0 2 '(:ipn 23 42) '(:ipn 23 0) '(:ipn 23 0)
                     1577836800000 7 86400000 nil nil))

(defconst *bpp-octets-b*
  '(137 7 0 2 130 2 130 23 24 42 130 2 130 23 0 130 2 130 23 0
    130 27 0 0 1 111 94 102 232 0 7 26 5 38 92 0 68 87 208 145 118))

(assert-event (fn-bpp-blockp *bpp-block-b*))
(assert-event (fn-bpp-eid-singletonp '(:ipn 23 42)))
(assert-event (fn-bpp-eid-node-idp '(:ipn 23 0)))
(assert-event (not (fn-bpp-eid-node-idp '(:ipn 23 42))))
(assert-event (equal (fn-bpp-encode *bpp-block-b*) *bpp-octets-b*))
(assert-event (equal (fn-bpp-decode *bpp-octets-b*) (list :ok *bpp-block-b*)))

; -----------------------------------------------------------------------------
; A fragment: arity 11, fragment offset and total ADU length present

(defconst *bpp-block-c*
  (fn-bpp-make-block 1 1 *bpp-dtn-inbox* *bpp-dtn-n1* *bpp-dtn-n1*
                     2342 2 60000000 1024 4096))

(defconst *bpp-octets-c*
  '(139 7 1 1 130 1 106 47 47 110 50 47 105 110 98 111 120
    130 1 101 47 47 110 49 47 130 1 101 47 47 110 49 47
    130 25 9 38 2 26 3 147 135 0 25 4 0 25 16 0 66 28 184))

(assert-event (fn-bpp-blockp *bpp-block-c*))
(assert-event (fn-bpp-fragmentp (fn-bpp-flags *bpp-block-c*)))
(assert-event (equal (fn-bpp-encode *bpp-block-c*) *bpp-octets-c*))
(assert-event (equal (fn-bpp-decode *bpp-octets-c*) (list :ok *bpp-block-c*)))

; -----------------------------------------------------------------------------
; The null endpoint and CRC type zero: arity 8, no CRC field

(defconst *bpp-block-d*
  (fn-bpp-make-block 4 0 '(:dtn-none) '(:dtn-none) '(:dtn-none)
                     0 1 3600000 nil nil))

(defconst *bpp-octets-d*
  '(136 7 4 0 130 1 0 130 1 0 130 1 0 130 0 1 26 0 54 238 128))

(assert-event (fn-bpp-blockp *bpp-block-d*))
(assert-event (equal (fn-bpp-encode *bpp-block-d*) *bpp-octets-d*))
(assert-event (equal (fn-bpp-decode *bpp-octets-d*) (list :ok *bpp-block-d*)))
(assert-event (equal (fn-bpp-block-crc *bpp-block-d*) nil))
(assert-event (not (fn-bpp-identifiablep *bpp-block-d*)))
(assert-event (fn-bpp-flags-conformantp *bpp-block-d*))

; The same block with the "must not be fragmented" flag cleared is a valid
; block that violates the section 4.2.3 MUST, and the model says so rather
; than refusing to decode it.
(defconst *bpp-block-d-loose*
  (fn-bpp-make-block 0 0 '(:dtn-none) '(:dtn-none) '(:dtn-none)
                     0 1 3600000 nil nil))
(assert-event (fn-bpp-blockp *bpp-block-d-loose*))
(assert-event (not (fn-bpp-flags-conformantp *bpp-block-d-loose*)))
(assert-event (fn-bpp-result-okp (fn-bpp-decode
                                  (fn-bpp-encode *bpp-block-d-loose*))))

; An administrative record that also requests status reports is likewise a
; decodable block that the conformance predicate rejects.
(assert-event
 (not (fn-bpp-flags-conformantp
       (fn-bpp-make-block 16386 1 *bpp-dtn-inbox* *bpp-dtn-n1* *bpp-dtn-n1*
                          2342 2 60000000 nil nil))))

; -----------------------------------------------------------------------------
; Refusals stay distinct

; A single flipped CRC octet is a CRC mismatch, not a malformed block.
(assert-event
 (equal (fn-bpp-decode
         '(137 7 0 1 130 1 106 47 47 110 50 47 105 110 98 111 120
           130 1 101 47 47 110 49 47 130 1 101 47 47 110 49 47
           130 25 9 38 2 26 3 147 135 0 66 3 150))
        '(:error :crc-mismatch)))

; A non-minimal spelling of the version field is refused at the CBOR level.
(assert-event
 (equal (fn-bpp-decode
         '(137 24 7 0 1 130 1 106 47 47 110 50 47 105 110 98 111 120
           130 1 101 47 47 110 49 47 130 1 101 47 47 110 49 47
           130 25 9 38 2 26 3 147 135 0 66 3 151))
        '(:error :noncanonical)))

; Version 8 is not BPv7.
(assert-event
 (equal (fn-bpp-decode
         '(137 8 0 1 130 1 106 47 47 110 50 47 105 110 98 111 120
           130 1 101 47 47 110 49 47 130 1 101 47 47 110 49 47
           130 25 9 38 2 26 3 147 135 0 66 3 151))
        '(:error :malformed)))

; An arity that does not match the fragment flag and CRC type is malformed:
; the fragment flag is clear, so a ten-item block cannot be right.
(assert-event
 (equal (car (fn-bpp-decode
              '(138 7 0 1 130 1 106 47 47 110 50 47 105 110 98 111 120
                130 1 101 47 47 110 49 47 130 1 101 47 47 110 49 47
                130 25 9 38 2 26 3 147 135 0 25 4 0 66 3 151)))
        :error))

; Trailing octets after a complete block are refused.
(assert-event
 (equal (fn-bpp-decode (append *bpp-octets-a* '(0))) '(:error :trailing)))

; A dtn SSP that is not a conforming dtn-hier-part is malformed.
(assert-event
 (equal (car (fn-bpp-decode
              '(137 7 0 1 130 1 98 110 50 130 1 101 47 47 110 49 47
                130 1 101 47 47 110 49 47 130 25 9 38 2
                26 3 147 135 0 66 0 0)))
        :error))

; -----------------------------------------------------------------------------
; Identity

(assert-event (equal (fn-bpp-adu-key *bpp-block-a*)
                     (list :fn-bp-adu-key *bpp-dtn-n1* 2342 2)))
(assert-event (equal (fn-bpp-adu-key *bpp-block-a*)
                     (fn-bpp-adu-key
                      (fn-bpp-with-destination *bpp-block-a* '(:ipn 9 9)))))
(assert-event (equal (fn-bpp-adu-key *bpp-block-a*)
                     (fn-bpp-adu-key
                      (fn-bpp-with-lifetime *bpp-block-a* 1))))
(assert-event (equal (fn-bpp-adu-key *bpp-block-a*)
                     (fn-bpp-adu-key
                      (fn-bpp-with-crc-type *bpp-block-a* 2))))
; Changing the source or any part of the creation timestamp changes the key.
(assert-event
 (not (equal (fn-bpp-adu-key *bpp-block-a*)
             (fn-bpp-adu-key
              (fn-bpp-make-block 0 1 *bpp-dtn-inbox* *bpp-dtn-inbox*
                                 *bpp-dtn-n1* 2342 2 60000000 nil nil)))))
(assert-event
 (not (equal (fn-bpp-adu-key *bpp-block-a*)
             (fn-bpp-adu-key
              (fn-bpp-make-block 0 1 *bpp-dtn-inbox* *bpp-dtn-n1*
                                 *bpp-dtn-n1* 2343 2 60000000 nil nil)))))
(assert-event
 (not (equal (fn-bpp-adu-key *bpp-block-a*)
             (fn-bpp-adu-key
              (fn-bpp-make-block 0 1 *bpp-dtn-inbox* *bpp-dtn-n1*
                                 *bpp-dtn-n1* 2342 3 60000000 nil nil)))))
; A non-fragment's identity does not use the payload length; a fragment's does.
(assert-event (equal (fn-bpp-bundle-id *bpp-block-a* 11)
                     (fn-bpp-bundle-id *bpp-block-a* 12)))
(assert-event (not (equal (fn-bpp-bundle-id *bpp-block-c* 11)
                          (fn-bpp-bundle-id *bpp-block-c* 12))))

; -----------------------------------------------------------------------------
; Extension blocks (RFC 9171 section 4.4)

(assert-event (fn-bpp-previous-nodep *bpp-dtn-n1*))
(assert-event (not (fn-bpp-previous-nodep *bpp-dtn-inbox*)))
(assert-event (equal (fn-bpp-previous-node-data *bpp-dtn-n1*)
                     '(130 1 101 47 47 110 49 47)))
(assert-event (equal (fn-bpp-data-previous-node '(130 1 101 47 47 110 49 47))
                     *bpp-dtn-n1*))
; A non-node-ID endpoint is refused as a Previous Node value.
(assert-event (equal (fn-bpp-data-previous-node
                      '(130 1 106 47 47 110 50 47 105 110 98 111 120))
                     nil))

(assert-event (equal (fn-bpp-bundle-age-data 1234) '(25 4 210)))
(assert-event (equal (fn-bpp-data-bundle-age '(25 4 210)) 1234))

(assert-event (fn-bpp-hop-countp (fn-bpp-make-hop-count 32 0)))
(assert-event (not (fn-bpp-hop-countp (fn-bpp-make-hop-count 0 0))))
(assert-event (not (fn-bpp-hop-countp (fn-bpp-make-hop-count 256 0))))
(assert-event (equal (fn-bpp-hop-count-data (fn-bpp-make-hop-count 32 0))
                     '(130 24 32 0)))
(assert-event (equal (fn-bpp-data-hop-count '(130 24 32 0))
                     (fn-bpp-make-hop-count 32 0)))
(assert-event (not (fn-bpp-hop-limit-exceededp (fn-bpp-make-hop-count 32 32))))
(assert-event (fn-bpp-hop-limit-exceededp (fn-bpp-make-hop-count 32 33)))

; -----------------------------------------------------------------------------
; Teeth.

; fn-bpc-decode-of-encode
;   without `fn-bpc-shapep`: a value outside the domain has no encoding to
;   decode.
(assert-event
 (with-guard-checking :none
  (and (not (fn-bpc-shapep :item 7))
       (fn-cbor-octet-listp nil) (natp 100) (<= (fn-bpc-cost :item 7) 100)
       (not (equal (fn-bpc-dec :item 0 (append (fn-bpc-enc :item 7) nil) 100)
                   (fn-cbor-ok 7 nil))))))

;   without the budget bound: the decoder refuses rather than looping.  Stated
;   generally, the negated goal sends the prover into the induction on
;   `fn-bpc-dec` it was meant to escape, so the tooth is bitten by an instance
;   instead: the theorem body at flg = :item, x = (:uint . 1), rest = nil and
;   budget = 0 satisfies every surviving hypothesis and is false, because the
;   decoder answers (:error :budget) rather than the value.
(assert-event
 (not (implies (and (fn-bpc-shapep :item '(:uint . 1))
                    (fn-cbor-octet-listp nil)
                    (natp 0))
               (equal (fn-bpc-dec :item 0
                                  (append (fn-bpc-enc :item '(:uint . 1)) nil)
                                  0)
                      (fn-cbor-ok '(:uint . 1) nil)))))

;   without the octet-list hypothesis on the remainder.
;   OPEN: no violating value was found.  The decoder returns the remainder
;   unread, so (fn-bpc-dec :item 0 (append (fn-bpc-enc :item x) rest) budget)
;   is (fn-cbor-ok x rest) for rest = (300) and for rest = a alike (probed
;   2026-09-19).  The hypothesis looks unnecessary in fn-bpc-decode-of-encode
;   (books/bp-primary-cbor.lisp, codecs); recorded for its owner.

; fn-bpc-accepted-input-is-canonical
;   without the success hypothesis: a refused input is not re-encoded.
(assert-event
 (with-guard-checking :none
  (and (not (fn-cbor-result-okp (fn-bpc-decode-exact '(255))))
       (not (equal (fn-bpc-encode (fn-cbor-result-value (fn-bpc-decode-exact '(255))))
                   '(255))))))

; fn-bpp-decode-of-encode
;   without `fn-bpp-blockp`: a malformed record encodes to something the
;   decoder refuses.  Stated generally over a free `b`, the negated goal opens
;   every branch of the encoder and the decoder at once and does not settle, so
;   the tooth is bitten by an instance: b = 0 is not a block, and the round
;   trip on it is false.  The instance is evaluated logically, because 0 is
;   outside `fn-bpp-encode`'s guard -- which is the point.
(assert-event (not (fn-bpp-blockp 0)))
(assert-event
 (with-guard-checking :none
  (not (equal (fn-bpp-decode (fn-bpp-encode 0)) (fn-bpp-ok 0)))))

; fn-bpp-value-block-of-block-value
;   The width hypothesis (and the octet-list one) had no violating value: the
;   reader does not consult the CRC field, so both were dropped from the
;   theorem (books/bp-primary-invariants.lisp, 2026-09-19).  The witness below
;   shows the round trip on a CRC field of the wrong width.
(assert-event
 (equal (fn-bpp-value-block (fn-bpp-block-value *bpp-block-a* '(1 2 3)))
        *bpp-block-a*))

;   without `fn-bpp-blockp`: a non-record has no fields to build the value
;   from, so the reader cannot give the non-record back.  Stated generally
;   over a free `b`, the negated goal opens the builder and the reader on
;   every branch at once and does not settle, so the tooth is bitten by an
;   instance: b = 0 with crc-octets = nil satisfies both surviving hypotheses,
;   because `fn-bpp-crc-type` of 0 is not a CRC type and `fn-bpp-crc-width` of
;   a non-type is 0.  The body is false: the reader answers nil, not 0.  The
;   instance is evaluated logically, because 0 is outside
;   `fn-bpp-block-value`'s guard -- which is the point.
(assert-event
 (with-guard-checking :none
  (equal (fn-bpp-crc-width (fn-bpp-crc-type 0)) 0)))
(assert-event
 (with-guard-checking :none
  (not (implies (and (fn-cbor-octet-listp nil)
                     (equal (len nil)
                            (fn-bpp-crc-width (fn-bpp-crc-type 0))))
                (equal (fn-bpp-value-block (fn-bpp-block-value 0 nil))
                       0)))))

; fn-bpp-accepted-input-is-canonical-by-construction
;   without the success hypothesis: a refused input is not re-encoded.  Stated
;   generally over free `octets`, the negated goal opens the whole decoder and
;   the whole encoder at once and does not settle, so the tooth is bitten by
;   an instance: octets = (1) is refused as malformed, and re-encoding the
;   block the refusal does not carry gives the all-default block's octets, not
;   (1).  Evaluated logically, because that non-block is outside
;   `fn-bpp-encode`'s guard -- which is the point.
(assert-event (not (fn-bpp-result-okp (fn-bpp-decode '(1)))))
(assert-event
 (with-guard-checking :none
  (not (equal (fn-bpp-encode (fn-bpp-result-block (fn-bpp-decode '(1))))
              '(1)))))

; fn-bpp-adu-key-ignores-destination-lifetime-and-crc-type-by-definition
;   without `fn-bpp-blockp`: HYPOTHESIS UNNECESSARY for the conclusion, so
;   this tooth has no witness and is not claimed.  `fn-bpp-adu-key` reads
;   positions 4, 6 and 7 of the record, and `fn-bpp-with-destination`,
;   `fn-bpp-with-lifetime` and `fn-bpp-with-crc-type` copy exactly those three
;   positions through `fn-bpp-make-block`, which is a `list`.  The conclusion
;   therefore holds for every `b`, block or not, and the theorem keeps
;   `fn-bpp-blockp` for its guard, not for its truth.  The fact is proved here
;   rather than asserted, so the claim is checked:
(local
 (defthm fn-bpp-adu-key-ignores-destination-for-any-object
   (equal (fn-bpp-adu-key (fn-bpp-with-destination b d))
          (fn-bpp-adu-key b))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-bpp-adu-key fn-bpp-with-destination
                                      fn-bpp-make-block fn-bpp-source
                                      fn-bpp-creation-time
                                      fn-bpp-sequence)))))

; fn-bpp-previous-node-round-trip
;   without `fn-bpp-previous-nodep`: an endpoint that is not a node ID is not
;   a Previous Node value and does not come back.  Stated generally over a
;   free `e`, the negated goal opens the endpoint encoder and the CBOR decoder
;   at once and does not settle, so the tooth is bitten by an instance: the
;   dtn endpoint //n2/inbox has a non-empty demux, so it is not a node ID, and
;   the round trip on it answers nil.  Evaluated logically, because it is
;   outside `fn-bpp-previous-node-data`'s guard -- which is the point.
(assert-event (not (fn-bpp-previous-nodep *bpp-dtn-inbox*)))
(assert-event
 (with-guard-checking :none
  (not (equal (fn-bpp-data-previous-node
               (fn-bpp-previous-node-data *bpp-dtn-inbox*))
              *bpp-dtn-inbox*))))

; fn-bpp-hop-count-round-trip
;   without `fn-bpp-hop-countp`: a hop limit of zero or over 255 is refused.
;   Stated generally over a free `x`, the negated goal opens the CBOR array
;   encoder and decoder at once and does not settle, so the tooth is bitten by
;   an instance: the hop count with limit 0 is not a hop count, and the round
;   trip on it answers nil.  Evaluated logically, because it is outside
;   `fn-bpp-hop-count-data`'s guard -- which is the point.
(assert-event (not (fn-bpp-hop-countp (fn-bpp-make-hop-count 0 0))))
(assert-event
 (with-guard-checking :none
  (not (equal (fn-bpp-data-hop-count
               (fn-bpp-hop-count-data (fn-bpp-make-hop-count 0 0)))
              (fn-bpp-make-hop-count 0 0)))))
