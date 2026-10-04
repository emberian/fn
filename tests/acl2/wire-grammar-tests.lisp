; Teeth for books/wire-grammar.
;
; Positive witnesses assert every antecedent and the conclusion of the two
; keystones on a concrete grammar (the consumer status reply frame, a tag
; over a :where'd :seq, inside an FNCT frame) and on a tail grammar (a
; :line then :base64-lines).  Hypothesis witnesses, one per hypothesis
; that has one:
;   fn-wg-decode-of-encode
;     delimited-or-empty-rest  a :rest grammar followed by octets: the decoder
;                              takes them into the value;
;     valuep                   a :uint value past the node's HI encodes and
;                              decodes to something else;
;     grammarp                 a :tag with a repeated code: the second arm's
;                              value decodes as the first's.
;     (fn-cbor-octet-listp r): no witness found -- every node reads its own
;                              octets only; kept as the domain of the input.
;   fn-wg-encode-of-decode
;     grammarp                 a :tag with a repeated name decodes two codes
;                              to one value, which re-encodes to one of them.
; and the named refusals: a frame with one trailer bit flipped answers
; (:refused :trailer); a truncated frame answers (:refused :malformed); a
; :where whose fields decode and whose checks fail answers (:refused :where),
; and one whose fields do not decode answers (:refused :malformed).
(in-package "ACL2")
(include-book "../../books/wire-grammar")

(defconst *wgt-status-reply*
  '(:frame (70 78 67 84) 1 9 13
    (:tag 1
     (0 :accepted (:where (:seq (:uint 4 0 4294967295) (:uint 4 0 4294967295)
                                (:uint 4 0 4294967295))
                          (:le 0 1) (:diff 2 1 0)))
     (1 :refused (:seq))
     (2 :uncertain (:seq))
     (3 :fault (:seq)))))

(defconst *wgt-tail*
  '(:seq (:const (70 58 32)) (:line 1 20 :header) (:const (13 10))
         (:base64-lines 4 0 100)))

; Positive: every antecedent and the conclusion, both keystones.
(assert-event
 (let* ((g *wgt-status-reply*) (v '(:accepted (3 10 7))) (r '(1 2 3))
        (e (fn-wg-encode g v)))
   (and (fn-wg-grammarp g) (fn-wg-valuep g v) (fn-cbor-octet-listp r)
        (fn-wg-delimitedp g)
        (equal (fn-wg-decode g (fn-wg-app e r)) (fn-wg-ok v r))
        (fn-cbor-octet-listp e)
        (fn-wg-okp (fn-wg-decode g e))
        (fn-wg-valuep g (fn-wg-value (fn-wg-decode g e)))
        (equal (fn-wg-app (fn-wg-encode g (fn-wg-value (fn-wg-decode g e)))
                          (fn-wg-rest (fn-wg-decode g e)))
               e))))

(assert-event
 (let* ((g *wgt-tail*) (v (list nil '(97 98) nil '(0 1 2 3 4 5 6 7))) (r nil)
        (e (fn-wg-encode g v)))
   (and (fn-wg-grammarp g) (fn-wg-valuep g v) (not (fn-wg-delimitedp g))
        (null r)
        (equal (fn-wg-decode g (fn-wg-app e r)) (fn-wg-ok v r))
        ; "F: ab" CRLF then AAEC CRLF AwQF CRLF BgcA CRLF ... in lines of 4
        (equal (fn-wg-take 6 e) '(70 58 32 97 98 13)))))

; The named refusals.
(assert-event
 (let* ((g *wgt-status-reply*) (e (fn-wg-encode g '(:accepted (3 10 7)))))
   (and (equal (fn-wg-decode g (update-nth 30 (logxor 1 (nth 30 e)) e))
               '(:refused :trailer))
        (equal (fn-wg-decode g (fn-wg-take 20 e)) '(:refused :malformed))
        ; a refused status carries no fields
        (equal (fn-wg-decode g (fn-wg-encode g '(:refused nil)))
               (fn-wg-ok '(:refused nil) nil)))))

; The :where checks refuse a status whose distance is not frontier - ack,
; and one whose ack is past its frontier, by name.
(assert-event
 (let* ((g *wgt-status-reply*))
   (and (not (fn-wg-valuep g '(:accepted (3 10 6))))
        (equal (fn-wg-decode g (fn-wg-encode g '(:accepted (3 10 6))))
               '(:refused :where))
        (not (fn-wg-valuep g '(:accepted (11 10 0))))
        (equal (fn-wg-decode g (fn-wg-encode g '(:accepted (11 10 0))))
               '(:refused :where)))))

; A :where whose fields do not decode is malformed, not a where refusal: the
; checks run only on a decoded value.
(assert-event
 (let ((g '(:where (:seq (:uint 1 0 9) (:uint 1 0 9)) (:le 0 1))))
   (and (fn-wg-grammarp g)
        (equal (fn-wg-decode g '(5 10)) '(:refused :malformed))
        (equal (fn-wg-decode g '(5)) '(:refused :malformed))
        (equal (fn-wg-decode g '(5 4)) '(:refused :where))
        (equal (fn-wg-decode g '(4 5 6)) (fn-wg-ok '(4 5) '(6))))))

; Hypothesis witness (decode-of-encode): delimited-or-empty-rest.
(assert-event
 (let* ((g '(:rest 0 10 :any)) (v '(1)) (r '(2)))
   (and (fn-wg-grammarp g) (fn-wg-valuep g v) (fn-cbor-octet-listp r)
        (not (fn-wg-delimitedp g)) (not (null r))
        (not (equal (fn-wg-decode g (fn-wg-app (fn-wg-encode g v) r))
                    (fn-wg-ok v r))))))

; Hypothesis witness (decode-of-encode): valuep.
(assert-event
 (let* ((g '(:uint 1 0 10)) (v 300) (r nil))
   (and (fn-wg-grammarp g) (not (fn-wg-valuep g v)) (fn-cbor-octet-listp r)
        (fn-wg-delimitedp g)
        (not (equal (fn-wg-decode g (fn-wg-app (fn-wg-encode g v) r))
                    (fn-wg-ok v r))))))

; Hypothesis witness (decode-of-encode): grammarp (repeated tag code).
(assert-event
 (let* ((g '(:tag 1 (0 :a (:seq)) (0 :b (:seq)))) (v '(:b nil)) (r nil))
   (and (not (fn-wg-grammarp g)) (fn-wg-valuep g v) (fn-cbor-octet-listp r)
        (fn-wg-delimitedp g)
        (not (equal (fn-wg-decode g (fn-wg-app (fn-wg-encode g v) r))
                    (fn-wg-ok v r))))))

; Hypothesis witness (encode-of-decode): grammarp (repeated tag name).
(assert-event
 (let* ((g '(:tag 1 (0 :a (:seq)) (1 :a (:seq)))) (xs '(1)))
   (and (not (fn-wg-grammarp g)) (fn-cbor-octet-listp xs)
        (fn-wg-okp (fn-wg-decode g xs))
        (not (equal (fn-wg-app (fn-wg-encode g (fn-wg-value (fn-wg-decode g xs)))
                               (fn-wg-rest (fn-wg-decode g xs)))
                    xs)))))
