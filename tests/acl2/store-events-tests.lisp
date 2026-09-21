; Ground vectors and malformed-tag teeth for the ordered Store event grammar.
(in-package "ACL2")
(include-book "../../books/store-events")

(defconst *fn-se-test-undertake*
  (fn-store-retention-event-make :undertake 1 2 2 "forward-1" "subject-1"
                                 "evidence-1" 7))
(defconst *fn-se-test-undertake-octets*
  (fn-store-event-encode *fn-se-test-undertake*))

(assert-event (fn-store-retention-event-p *fn-se-test-undertake*))
(assert-event
 (equal (fn-store-event-decode-exact *fn-se-test-undertake-octets*)
        (list :ok *fn-se-test-undertake*)))

; The sequence field is a byte string here.  Its cdr happens to be the natural
; 1, so a decoder that strips CBOR tags without checking them would accept it.
(defconst *fn-se-test-wrong-sequence-tag*
  (append
   (fn-cbor-encode (cons :bytes *fn-store-event-magic*))
   (fn-cbor-encode (cons :uint *fn-store-event-version*))
   (fn-cbor-encode (cons :uint *fn-store-event-undertake-code*))
   (fn-cbor-encode (cons :bytes '(1)))
   (fn-cbor-encode (cons :uint 2))
   (fn-cbor-encode (cons :uint 2))
   (fn-cbor-encode (cons :bytes (fn-record-string-octets "forward-1")))
   (fn-cbor-encode (cons :bytes (fn-record-string-octets "subject-1")))
   (fn-cbor-encode (cons :bytes (fn-record-string-octets "evidence-1")))
   (fn-cbor-encode (cons :uint 7))))

(assert-event
 (equal (fn-store-event-decode-exact *fn-se-test-wrong-sequence-tag*)
        '(:error :record)))

; Unknown event kind and trailing items are fail-closed.
(assert-event
 (not (fn-record-result-okp
       (fn-store-event-decode-exact
        (append (fn-cbor-encode (cons :bytes *fn-store-event-magic*))
                (fn-cbor-encode (cons :uint *fn-store-event-version*))
                (fn-cbor-encode (cons :uint 9)))))))
(assert-event
 (not (fn-record-result-okp
       (fn-store-event-decode-exact
        (append *fn-se-test-undertake-octets* '(0))))))
