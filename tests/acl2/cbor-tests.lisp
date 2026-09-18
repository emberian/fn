; Golden vectors for the experimental fn deterministic CBOR primitive profile.
; Values and expected bytes use RFC 8949's major type 0 and major type 2
; grammar.  These examples test profile rejection as well as CBOR syntax.
(in-package "ACL2")
(include-book "../../books/cbor")

; Accepted unsigned-integer vectors, including every profile argument boundary.
(assert-event (equal (fn-cbor-encode '(:uint . 0)) '(0)))
(assert-event (equal (fn-cbor-encode '(:uint . 23)) '(23)))
(assert-event (equal (fn-cbor-encode '(:uint . 24)) '(24 24)))
(assert-event (equal (fn-cbor-encode '(:uint . 255)) '(24 255)))
(assert-event (equal (fn-cbor-encode '(:uint . 256)) '(25 1 0)))
(assert-event (equal (fn-cbor-encode '(:uint . 65535)) '(25 255 255)))
(assert-event (equal (fn-cbor-encode '(:uint . 65536)) '(26 0 1 0 0)))
(assert-event (equal (fn-cbor-encode '(:uint . 4294967295))
                     '(26 255 255 255 255)))
(assert-event (equal (fn-cbor-decode-exact '(0))
                     '(:ok (:uint . 0) nil)))
(assert-event (equal (fn-cbor-decode-exact '(25 1 244))
                     '(:ok (:uint . 500) nil)))
(assert-event (equal (fn-cbor-decode-exact '(26 255 255 255 255))
                     '(:ok (:uint . 4294967295) nil)))

; Accepted definite-length byte strings.  The payload stays exact octets.
(assert-event (equal (fn-cbor-encode '(:bytes)) '(64)))
(assert-event (equal (fn-cbor-encode '(:bytes 255)) '(65 255)))
(assert-event (equal (fn-cbor-decode-exact '(67 1 2 3))
                     '(:ok (:bytes 1 2 3) nil)))
(assert-event (equal (fn-cbor-decode '(65 255 0))
                     '(:ok (:bytes 255) (0))))
(assert-event (equal (fn-cbor-decode-exact
                      '(88 24 0 1 2 3 4 5 6 7 8 9 10 11
                        12 13 14 15 16 17 18 19 20 21 22 23))
                     '(:ok (:bytes 0 1 2 3 4 5 6 7 8 9 10 11
                                   12 13 14 15 16 17 18 19 20 21 22 23)
                            nil)))

; RFC 8949 deterministic form requires the shortest argument representation.
(assert-event (equal (fn-cbor-decode-exact '(24 0)) '(:error :noncanonical)))
(assert-event (equal (fn-cbor-decode-exact '(25 0 24)) '(:error :noncanonical)))
(assert-event (equal (fn-cbor-decode-exact '(26 0 0 1 0))
                     '(:error :noncanonical)))
(assert-event (equal (fn-cbor-decode-exact '(88 0)) '(:error :noncanonical)))
(assert-event (equal (fn-cbor-decode-exact '(89 0 24)) '(:error :noncanonical)))
(assert-event (equal (fn-cbor-decode-exact '(90 0 1 0 0)) '(:error :limit)))

; Truncation has priority when a required argument or payload octet is absent.
(assert-event (equal (fn-cbor-decode-exact nil) '(:error :truncated)))
(assert-event (equal (fn-cbor-decode-exact '(24)) '(:error :truncated)))
(assert-event (equal (fn-cbor-decode-exact '(25 1)) '(:error :truncated)))
(assert-event (equal (fn-cbor-decode-exact '(65)) '(:error :truncated)))

; Indefinite, unsupported, and malformed forms are never silently accepted.
(assert-event (equal (fn-cbor-decode-exact '(95 64 255)) '(:error :unsupported)))
(assert-event (equal (fn-cbor-decode-exact '(31)) '(:error :unsupported)))
(assert-event (equal (fn-cbor-decode-exact '(32)) '(:error :unsupported)))
(assert-event (equal (fn-cbor-decode-exact '(256)) '(:error :malformed)))
(assert-event (equal (fn-cbor-decode-exact '(0 0)) '(:error :trailing)))

; The primitive profile is intentionally not a general CBOR codec.
(assert-event (equal (fn-cbor-encode '(:uint . 4294967296)) nil))
(assert-event (equal (fn-cbor-encode '(:text . "not-in-profile")) nil))
