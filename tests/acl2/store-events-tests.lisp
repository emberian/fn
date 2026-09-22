; Ground vectors and malformed-tag teeth for the ordered Store event grammar.
(in-package "ACL2")
(include-book "../../books/store-events")
(include-book "../../books/codec-attach")

(assert-event (equal (fn-store-publication-ceiling :article) 65538))
(assert-event (equal (fn-store-publication-ceiling :undertake) 4096))
(assert-event (equal (fn-store-publication-ceiling :keyring-snapshot) 131072))
(assert-event (equal (fn-store-publication-ceiling :accepted-statement) 196608))

(defconst *fn-se-test-undertake*
  (fn-store-retention-event-make :undertake 1 2 2 "forward-1" "subject-1"
                                 "evidence-1" 7))
(make-event `(defconst *fn-se-test-undertake-octets* ',(fn-store-event-encode *fn-se-test-undertake*)))

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

; The decoder that examines the sequence tag is the retention one, and it
; refuses with (:error :record) -- the claim this test was written for, at
; 6ab2c783.  fn-store-event-decode-exact then keeps trying the remaining
; kinds (5d497ebe, a different lane, thirteen minutes later) and reports the
; LAST alternative it tried, so at the composed boundary the same input reads
; (:error :accepted-article) with the same refused outcome.  All three are
; asserted: the deciding function's reason, that the composition refuses, and
; the tag the composition currently reports.  A lane that makes the dispatcher
; stop at the kind code it matched will trip the third and should say so.
(assert-event
 (equal (fn-store-retention-event-decode-exact *fn-se-test-wrong-sequence-tag*)
        '(:error :record)))
(assert-event
 (not (fn-record-result-okp
       (fn-store-event-decode-exact *fn-se-test-wrong-sequence-tag*))))
(assert-event
 (equal (fn-store-event-decode-exact *fn-se-test-wrong-sequence-tag*)
        '(:error :accepted-article)))

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
