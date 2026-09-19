; Golden vectors and teeth for the one durable frame grammar.
;
; The FNWF and FNRJ vectors below were generated from the Python encoders in
; `tools/workflow_journal.py` and `tools/receipt_journal.py` as they stood
; before those functions became bridge calls, together with the SHA-256
; trailer each produced.  Asserting them here makes the migration a checked
; byte-for-byte conformance: if the ACL2 grammar disagreed with the durable
; journals already on disk, these forms would fail.
;
; The teeth are concrete refusals, one per decision the decoder makes, plus
; `must-fail` siblings for the hypotheses of the two round-trip keystones
; that a caller could actually drop.

(in-package "ACL2")
(include-book "../../books/frame-invariants")
(include-book "std/testing/must-fail" :dir :system)

(defconst *fn-frame-test-digest*
  '(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15
    16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31))

(defconst *fn-frame-test-other-digest*
  '(31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16
    15 14 13 12 11 10 9 8 7 6 5 4 3 2 1 0))

; -----------------------------------------------------------------------------
; The layout, spelled out

(assert-event
 (equal (fn-frame-encode *fn-frame-magic-store* 1 1 '(1 2 3)
                         *fn-frame-test-digest*)
        (append '(70 78 83 84 1 1 0 0 0 3 1 2 3) *fn-frame-test-digest*)))

(assert-event
 (equal (fn-frame-decode
         (append '(70 78 83 84 1 1 0 0 0 3 1 2 3) *fn-frame-test-digest*)
         *fn-frame-test-digest* *fn-frame-max-store-payload*)
        (fn-frame-ok '(70 78 83 84) 1 1 '(1 2 3))))

; An empty payload is a real accepted value, not a degenerate one: the frame
; is exactly its overhead and decodes to the empty payload.
(assert-event
 (equal (len (fn-frame-encode *fn-frame-magic-store* 1 1 nil
                              *fn-frame-test-digest*))
        *fn-frame-overhead-octets*))

(assert-event
 (equal (fn-frame-decode (fn-frame-encode *fn-frame-magic-store* 1 1 nil
                                          *fn-frame-test-digest*)
                         *fn-frame-test-digest* 16)
        (fn-frame-ok '(70 78 83 84) 1 1 nil)))

(assert-event
 (equal (fn-frame-store-decode
         (fn-frame-store-encode '(88 89 90) *fn-frame-test-digest*)
         *fn-frame-test-digest*)
        (fn-frame-ok '(70 78 83 84) 1 1 '(88 89 90))))

; -----------------------------------------------------------------------------
; Teeth: one refusal per decision the decoder makes

; The supplied digest is not the stored trailer.
(assert-event
 (equal (fn-frame-decode
         (append '(70 78 83 84 1 1 0 0 0 3 1 2 3) *fn-frame-test-digest*)
         *fn-frame-test-other-digest* *fn-frame-max-store-payload*)
        (fn-frame-error :integrity)))

; The header declares one octet more payload than the file holds: a frame cut
; short is `:truncated`, distinct from a length the caller will not accept.
(assert-event
 (equal (fn-frame-decode
         (append '(70 78 83 84 1 1 0 0 0 4 1 2 3) *fn-frame-test-digest*)
         *fn-frame-test-digest* *fn-frame-max-store-payload*)
        (fn-frame-error :truncated)))

; One octet of padding after a well-formed frame is a refusal, never a value
; with something ignored after it.
(assert-event
 (equal (fn-frame-decode
         (append '(70 78 83 84 1 1 0 0 0 3 1 2 3)
                 (append *fn-frame-test-digest* '(0)))
         *fn-frame-test-digest* *fn-frame-max-store-payload*)
        (fn-frame-error :length)))

; The declared length exceeds the caller's cap.  The frame is short enough to
; pass the cons preflight, so this is the declared-length check refusing a
; header that claims more payload than the caller will accept.
(assert-event
 (equal (fn-frame-decode
         (append '(70 78 83 84 1 1 0 0 0 100 1 2 3) *fn-frame-test-digest*)
         *fn-frame-test-digest* 3)
        (fn-frame-error :limit)))

; Too few octets to hold a header and a trailer.
(assert-event
 (equal (fn-frame-decode '(70 78 83 84 1 1 0 0 0 0) *fn-frame-test-digest* 16)
        (fn-frame-error :truncated)))

; A digest of the wrong width is refused before the payload is taken apart.
(assert-event
 (equal (fn-frame-decode
         (append '(70 78 83 84 1 1 0 0 0 3 1 2 3) *fn-frame-test-digest*)
         '(0 1 2) *fn-frame-max-store-payload*)
        (fn-frame-error :digest)))

; An over-long input is refused by the cons preflight.  This witness is not
; even an octet list, and the answer is still `:limit` rather than
; `:malformed`, so no octet was examined and nothing was allocated.
(assert-event
 (equal (fn-frame-decode (make-list 43) *fn-frame-test-digest* 0)
        (fn-frame-error :limit)))

; And the same shape one cons shorter reaches octet validation, so `:limit`
; above separates inputs by the bound rather than by their contents.
(assert-event
 (equal (fn-frame-decode (make-list 42) *fn-frame-test-digest* 0)
        (fn-frame-error :malformed)))

; The store entry point refuses a frame whose magic belongs to another schema
; even when the frame itself is well formed.
(assert-event
 (equal (fn-frame-store-decode
         (fn-frame-encode *fn-frame-magic-workflow* 1 1 '(1 2 3)
                          *fn-frame-test-digest*)
         *fn-frame-test-digest*)
        (fn-frame-error :magic)))

; -----------------------------------------------------------------------------
; Field grammar

(assert-event
 (equal (fn-frame-field-octets :text '(104 105)) '(0 2 104 105)))
(assert-event
 (equal (fn-frame-field-octets :nat 258)
        '(0 0 0 0 0 0 1 2)))
(assert-event
 (equal (fn-frame-field-octets :blob '(255)) '(0 0 0 1 255)))
(assert-event
 (equal (fn-frame-field-octets (cons :enum *fn-frame-phases*) :recovery)
        '(2)))

(assert-event
 (equal (fn-frame-field-parse :text '(0 2 104 105 9))
        (fn-frame-parse-ok '(104 105) '(9))))

; A zero-length text field is refused: the journals never wrote one and a
; decoder that accepted it would admit a value the encoder cannot produce.
(assert-event
 (equal (fn-frame-field-parse :text '(0 0))
        (fn-frame-parse-error :field-length)))

; Invalid UTF-8 inside a text field is refused by the wildmat RFC 3629
; decoder, not by a second table in this book.
(assert-event
 (equal (fn-frame-field-parse :text '(0 1 255))
        (fn-frame-parse-error :malformed-utf8)))

; An enumeration code outside the table is refused.
(assert-event
 (equal (fn-frame-field-parse (cons :enum *fn-frame-phases*) '(3))
        (fn-frame-parse-error :unknown-enumeration)))
(assert-event
 (equal (fn-frame-field-parse (cons :enum *fn-frame-phases*) '(0))
        (fn-frame-parse-error :unknown-enumeration)))

; -----------------------------------------------------------------------------
; Journal records: byte-exact conformance with the Python encoders replaced

; Generated from the pre-migration Python encoders; see HANDOFF.md.
(assert-event (equal (fn-frame-workflow-encode :config (list '(100 116 110 58 47 47 97) '(100 116 110 58 47 47 98) '(112 48) '(100 116 110 58 47 47 99) 3600 '(105 110 99 45 49) '(99 116 120 45 49)) '(133 191 156 215 153 147 95 216 73 187 36 137 24 28 97 242 237 217 202 211 138 131 12 15 207 33 190 244 83 185 103 173))
                     '(70 78 87 70 1 1 0 0 0 53 0 7 100 116 110 58 47 47 97 0 7 100 116 110 58 47 47 98 0 2 112 48 0 7 100 116 110 58 47 47 99 0 0 0 0 0 0 14 16 0 5 105 110 99 45 49 0 5 99 116 120 45 49 133 191 156 215 153 147 95 216 73 187 36 137 24 28 97 242 237 217 202 211 138 131 12 15 207 33 190 244 83 185 103 173)))
(assert-event (equal (fn-frame-workflow-encode :enqueue (list 7 7 '(119 111 114 107 58 97) '(60 97 64 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 62) '(115 104 97 50 53 54 58 97 98) '(97 114 99 104 105 118 101 58 99 100) '(102 111 114 119 97 114 100 58 101 102) '(100 116 110 58 47 47 98) '(112 48) '(116 48)) '(225 68 45 68 1 109 27 175 218 251 19 37 74 187 121 17 39 99 192 163 106 137 192 13 20 56 241 44 88 74 156 75))
                     '(70 78 87 70 1 2 0 0 0 97 0 0 0 0 0 0 0 7 0 0 0 0 0 0 0 7 0 6 119 111 114 107 58 97 0 19 60 97 64 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100 62 0 9 115 104 97 50 53 54 58 97 98 0 10 97 114 99 104 105 118 101 58 99 100 0 10 102 111 114 119 97 114 100 58 101 102 0 7 100 116 110 58 47 47 98 0 2 112 48 0 2 116 48 225 68 45 68 1 109 27 175 218 251 19 37 74 187 121 17 39 99 192 163 106 137 192 13 20 56 241 44 88 74 156 75)))
(assert-event (equal (fn-frame-workflow-encode :transport (list '(119 111 114 107 58 97) '(97 116 116 45 49) 2 :delivered) '(188 162 185 103 48 247 220 3 144 53 178 32 231 238 83 150 50 181 85 151 127 91 103 135 251 166 102 96 6 50 245 233))
                     '(70 78 87 70 1 4 0 0 0 24 0 6 119 111 114 107 58 97 0 5 97 116 116 45 49 0 0 0 0 0 0 0 2 6 188 162 185 103 48 247 220 3 144 53 178 32 231 238 83 150 50 181 85 151 127 91 103 135 251 166 102 96 6 50 245 233)))
(assert-event (equal (fn-frame-workflow-encode :outcome (list 9 9 :recovery :absent) '(13 64 23 147 128 37 248 221 45 6 70 120 81 196 132 195 49 149 66 22 46 33 231 179 188 214 24 41 244 14 103 110))
                     '(70 78 87 70 1 6 0 0 0 18 0 0 0 0 0 0 0 9 0 0 0 0 0 0 0 9 2 4 13 64 23 147 128 37 248 221 45 6 70 120 81 196 132 195 49 149 66 22 46 33 231 179 188 214 24 41 244 14 103 110)))
(assert-event (equal (fn-frame-workflow-encode :retry-request (list '(119 111 114 107 58 97) '(97 116 116 45 49) 18446744073709551615 '(112 48)) '(154 24 170 31 88 207 71 107 90 240 31 116 202 184 233 149 120 138 73 46 147 49 195 128 192 5 254 196 237 122 114 81))
                     '(70 78 87 70 1 7 0 0 0 27 0 6 119 111 114 107 58 97 0 5 97 116 116 45 49 255 255 255 255 255 255 255 255 0 2 112 48 154 24 170 31 88 207 71 107 90 240 31 116 202 184 233 149 120 138 73 46 147 49 195 128 192 5 254 196 237 122 114 81)))
(assert-event (equal (fn-frame-receipt-encode :config (list '(100 116 110 58 47 47 102 110 47 105 110 98 111 120) '(112 48) '(100 116 110 58 47 47 102 110 47 105 115 115 117 101 114)) '(135 245 25 68 251 120 195 150 1 16 180 211 124 193 3 213 14 148 185 175 207 79 30 73 118 87 252 254 52 121 181 154))
                     '(70 78 82 74 1 1 0 0 0 37 0 14 100 116 110 58 47 47 102 110 47 105 110 98 111 120 0 2 112 48 0 15 100 116 110 58 47 47 102 110 47 105 115 115 117 101 114 135 245 25 68 251 120 195 150 1 16 180 211 124 193 3 213 14 148 185 175 207 79 30 73 118 87 252 254 52 121 181 154)))
(assert-event (equal (fn-frame-receipt-encode :request-context (list '(98 105 100 45 49) '(1 2 3) '(255) :authorized) '(35 85 52 250 108 247 59 234 15 37 122 208 152 251 215 29 7 87 12 57 211 190 205 109 161 132 82 25 161 41 150 233))
                     '(70 78 82 74 1 2 0 0 0 20 0 5 98 105 100 45 49 0 0 0 3 1 2 3 0 0 0 1 255 1 35 85 52 250 108 247 59 234 15 37 122 208 152 251 215 29 7 87 12 57 211 190 205 109 161 132 82 25 161 41 150 233)))
(assert-event (equal (fn-frame-receipt-encode :receipt-decision (list '(119 111 114 107 58 97) '(114 99 112 116 45 49) :committed) '(116 28 173 178 196 19 220 231 189 75 208 157 21 222 64 50 213 212 246 91 190 66 168 20 140 231 99 100 213 98 200 85))
                     '(70 78 82 74 1 4 0 0 0 17 0 6 119 111 114 107 58 97 0 6 114 99 112 116 45 49 1 116 28 173 178 196 19 220 231 189 75 208 157 21 222 64 50 213 212 246 91 190 66 168 20 140 231 99 100 213 98 200 85)))

; The same records decode back to their values.
(assert-event
 (equal (fn-frame-workflow-decode
         (fn-frame-workflow-encode :outcome (list 9 9 :recovery :absent)
                                   *fn-frame-test-digest*)
         *fn-frame-test-digest*)
        (fn-frame-ok *fn-frame-magic-workflow* 1 :outcome
                     (list 9 9 :recovery :absent))))

(assert-event
 (equal (fn-frame-receipt-decode
         (fn-frame-receipt-encode :receipt-decision
                                  (list '(119 111 114 107 58 97)
                                        '(114 99 112 116 45 49) :committed)
                                  *fn-frame-test-digest*)
         *fn-frame-test-digest*)
        (fn-frame-ok *fn-frame-magic-receipt* 1 :receipt-decision
                     (list '(119 111 114 107 58 97)
                           '(114 99 112 116 45 49) :committed))))

; An outcome whose phase and result do not belong together is refused by the
; encoder, so a journal cannot contain one.
(assert-event
 (equal (fn-frame-workflow-encode :outcome (list 9 9 :ordinary :committed)
                                  *fn-frame-test-digest*)
        :bad))

; An unknown record kind is refused rather than carried opaquely.
(assert-event
 (equal (fn-frame-workflow-encode :not-a-kind (list 1)
                                  *fn-frame-test-digest*)
        :bad))

; -----------------------------------------------------------------------------
; Inbound bundles: the head is ACL2's, the bulk is opaque host bytes

(assert-event
 (equal (fn-frame-inbound-prefix '(98 105 100) 5)
        '(70 78 66 73 1 1 0 0 0 10 0 3 98 105 100)))

(assert-event
 (equal (fn-frame-inbound-open '(70 78 66 73 1 1 0 0 0 10 0 3 98 105 100)
                               52 *fn-frame-test-digest*
                               *fn-frame-test-digest*)
        (fn-frame-ok *fn-frame-magic-inbound* 1 '(98 105 100) 5)))

(assert-event
 (equal (fn-frame-inbound-open '(70 78 66 73 1 1 0 0 0 10 0 3 98 105 100)
                               52 *fn-frame-test-digest*
                               *fn-frame-test-other-digest*)
        (fn-frame-error :integrity)))

; One octet past the frame the header describes is `:length`; one octet short
; of it is `:truncated`.
(assert-event
 (equal (fn-frame-inbound-open '(70 78 66 73 1 1 0 0 0 10 0 3 98 105 100)
                               53 *fn-frame-test-digest*
                               *fn-frame-test-digest*)
        (fn-frame-error :length)))

(assert-event
 (equal (fn-frame-inbound-open '(70 78 66 73 1 1 0 0 0 10 0 3 98 105 100)
                               51 *fn-frame-test-digest*
                               *fn-frame-test-digest*)
        (fn-frame-error :truncated)))

; -----------------------------------------------------------------------------
; Teeth for the keystone hypotheses a caller could drop

; Without `fn-frame-digestp`, the round trip is false: a host that supplies a
; trailer of the wrong width produces a frame whose declared length no longer
; matches its contents.
(must-fail
 (defthm fn-frame-decode-of-encode-needs-a-digest-shape
   (implies (fn-frame-inputp magic version kind payload max-payload)
            (equal (fn-frame-decode
                    (fn-frame-encode magic version kind payload digest)
                    digest max-payload)
                   (fn-frame-ok magic version kind payload)))))

; Without `fn-frame-inputp`, the round trip is false: a magic of the wrong
; width shifts every later field.
(must-fail
 (defthm fn-frame-decode-of-encode-needs-an-input-shape
   (implies (fn-frame-digestp digest)
            (equal (fn-frame-decode
                    (fn-frame-encode magic version kind payload digest)
                    digest max-payload)
                   (fn-frame-ok magic version kind payload)))))

; Without the supplied digest being the constrained digest of the protected
; prefix, the host's decoder is not the specification decoder.
(must-fail
 (defthm fn-frame-decode-is-open-without-the-crypto-hypothesis
   (equal (fn-frame-decode octets digest max-payload)
          (fn-frame-open octets max-payload))))

; The bound refusal is not vacuous: a short input of the same shape is
; accepted, so `:limit` above separates by the bound and not by the shape.
(assert-event
 (fn-frame-result-okp
  (fn-frame-decode (fn-frame-encode *fn-frame-magic-store* 1 1 '(7)
                                    *fn-frame-test-digest*)
                   *fn-frame-test-digest* 1)))
