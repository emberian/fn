; Witnesses, golden bytes and teeth for books/statement.lisp.
(in-package "ACL2")
(include-book "crypto-seam-tests")
(include-book "../../books/statement-invariants")

(defconst *fn-t-seed-alice* (make-list 32 :initial-element 1))
(defconst *fn-t-seed-bob* (make-list 32 :initial-element 2))
(defconst *fn-t-creator-a* (make-list 32 :initial-element 17))
(defconst *fn-t-pred-1* (make-list 32 :initial-element 34))
(defconst *fn-t-ref-1* (make-list 32 :initial-element 51))
(defconst *fn-t-payload-1* (fn-record-string-octets "hello, lace"))

; -----------------------------------------------------------------------------
; Header golden vector (no digest involved: ref is supplied)

(defconst *fn-t-header-1*
  (fn-stmt-make-header *fn-t-creator-a* 1 2 (list *fn-t-pred-1*) :article
                       *fn-t-ref-1*))

(assert-event (fn-stmt-headerp *fn-t-header-1*))
(assert-event
 (equal (fn-stmt-header-encode *fn-t-header-1*)
        (append '(1)                        ; uint 1: schema
                (cons 88 (cons 32 *fn-t-creator-a*))   ; bstr(32) creator
                '(1)                        ; incarnation 1
                '(2)                        ; sequence 2
                '(1)                        ; one predecessor
                (cons 88 (cons 32 *fn-t-pred-1*))
                '(1)                        ; kind :article = 1
                (cons 88 (cons 32 *fn-t-ref-1*)))))
(assert-event (equal (fn-stmt-header-decode-exact
                      (fn-stmt-header-encode *fn-t-header-1*))
                     (fn-stmt-ok *fn-t-header-1*)))

; Rejections, one per decoder branch.
(assert-event (equal (fn-stmt-header-decode-exact
                      (cons 24 (cons 1 (cdr (fn-stmt-header-encode
                                              *fn-t-header-1*)))))
                     (fn-stmt-error :noncanonical)))
(assert-event (equal (fn-stmt-header-decode-exact
                      (cons 2 (cdr (fn-stmt-header-encode *fn-t-header-1*))))
                     (fn-stmt-error :unknown-version)))
(assert-event (equal (fn-stmt-header-decode-exact
                      (append (fn-stmt-header-encode *fn-t-header-1*) '(0)))
                     (fn-stmt-error :trailing)))
(assert-event (equal (fn-stmt-header-decode-exact
                      (fn-stmt-encode-items
                       (list '(:uint . 1) (cons :bytes *fn-t-creator-a*)
                             '(:uint . 1) '(:uint . 2) '(:uint . 17))))
                     (fn-stmt-error :pred-count)))
(assert-event (equal (fn-stmt-header-decode-exact
                      (fn-stmt-encode-items
                       (list '(:uint . 1) (cons :bytes *fn-t-creator-a*)
                             '(:uint . 1) '(:uint . 2) '(:uint . 2)
                             (cons :bytes *fn-t-pred-1*)
                             (cons :bytes *fn-t-pred-1*)
                             '(:uint . 1) (cons :bytes *fn-t-ref-1*))))
                     (fn-stmt-error :duplicate-pred)))
(assert-event (equal (fn-stmt-header-decode-exact
                      (fn-stmt-encode-items
                       (list '(:uint . 1) (cons :bytes *fn-t-creator-a*)
                             '(:uint . 1) '(:uint . 2) '(:uint . 0)
                             '(:uint . 9) (cons :bytes *fn-t-ref-1*))))
                     (fn-stmt-error :kind)))
(assert-event (equal (fn-stmt-header-decode-exact
                      (fn-stmt-encode-items
                       (list '(:uint . 1) (cons :bytes '(1 2 3)))))
                     (fn-stmt-error :creator)))
(assert-event (equal (fn-stmt-header-decode-exact
                      (make-list 1025 :initial-element 0))
                     (fn-stmt-error :limit)))
(assert-event (equal (fn-stmt-header-decode-exact '(1 88))
                     (fn-stmt-error :truncated)))

; The header is not a statement without a payload matching ref:
(assert-event (not (fn-stmt-p (fn-stmt-make *fn-t-header-1* *fn-t-payload-1*
                                            nil))))

; -----------------------------------------------------------------------------
; Signed statements under the toy realisers

(defun fn-t-stmt-1 ()
  (fn-stmt-sign *fn-t-seed-alice* *fn-t-creator-a* 1 1 nil :article
                *fn-t-payload-1*))
(defun fn-t-stmt-2 ()
  (fn-stmt-sign *fn-t-seed-alice* *fn-t-creator-a* 1 2
                (list (fn-stmt-id (fn-t-stmt-1))) :article
                (fn-record-string-octets "second")))

(assert-event (fn-stmt-p (fn-t-stmt-1)))
(assert-event (fn-stmt-p (fn-t-stmt-2)))
(assert-event (fn-stmt-verifiedp (fn-t-stmt-1)
                                 (fn-sig-public-key *fn-t-seed-alice*)))
; tooth: another key
(assert-event (not (fn-stmt-verifiedp (fn-t-stmt-1)
                                      (fn-sig-public-key *fn-t-seed-bob*))))
; tooth: tampered payload keeps the shape but breaks ref, so not a statement
(assert-event (not (fn-stmt-p (fn-stmt-make (fn-stmt-header (fn-t-stmt-1))
                                            (fn-record-string-octets "hello, lacE")
                                            (fn-stmt-signature (fn-t-stmt-1))))))
; tooth: tampered signature
(assert-event (not (fn-stmt-verifiedp
                    (fn-stmt-make (fn-stmt-header (fn-t-stmt-1))
                                  (fn-stmt-payload (fn-t-stmt-1))
                                  (let ((sig (fn-stmt-signature (fn-t-stmt-1))))
                                    (cons (mod (1+ (car sig)) 256) (cdr sig))))
                    (fn-sig-public-key *fn-t-seed-alice*))))
; tooth: a re-signed header with one changed field has another id
(assert-event (not (equal (fn-stmt-id (fn-t-stmt-1)) (fn-stmt-id (fn-t-stmt-2)))))
(assert-event (equal (fn-stmt-preds (fn-t-stmt-2))
                     (list (fn-stmt-id (fn-t-stmt-1)))))

; Round trip and canonicality on the whole statement.
(assert-event (equal (fn-stmt-decode-exact (fn-stmt-encode (fn-t-stmt-1)))
                     (fn-stmt-ok (fn-t-stmt-1))))
(assert-event (equal (fn-stmt-decode-exact (fn-stmt-encode (fn-t-stmt-2)))
                     (fn-stmt-ok (fn-t-stmt-2))))
(assert-event (equal (fn-stmt-encode
                      (fn-stmt-value
                       (fn-stmt-decode-exact (fn-stmt-encode (fn-t-stmt-2)))))
                     (fn-stmt-encode (fn-t-stmt-2))))
; The decoded statement still verifies: the bytes carry the signature.
(assert-event (fn-stmt-verifiedp
               (fn-stmt-value (fn-stmt-decode-exact (fn-stmt-encode (fn-t-stmt-2))))
               (fn-sig-public-key *fn-t-seed-alice*)))
; tooth: a non-statement encodes to nothing and nothing decodes to no statement
(assert-event (equal (fn-stmt-encode '(not a statement)) nil))
(assert-event (not (fn-stmt-okp (fn-stmt-decode-exact nil))))
; tooth: trailing octet on a whole statement
(assert-event (equal (fn-stmt-decode-exact
                      (append (fn-stmt-encode (fn-t-stmt-1)) '(0)))
                     (fn-stmt-error :trailing)))
; tooth: payload swapped in the bytes fails ref binding
(assert-event
 (equal (fn-stmt-decode-exact
         (fn-stmt-encode-items
          (append (fn-stmt-header-items (fn-stmt-header (fn-t-stmt-1)))
                  (list (cons :bytes (fn-record-string-octets "other"))
                        (cons :bytes (fn-stmt-signature (fn-t-stmt-1)))))))
        (fn-stmt-error :payload-ref)))

; -----------------------------------------------------------------------------
; Receipts: the payload names a policy term, not a boolean.

(defconst *fn-t-obligation* (fn-record-string-octets "archive:example"))

(defun fn-t-receipt-1 ()
  (fn-stmt-make-receipt (fn-stmt-id (fn-t-stmt-1)) *fn-t-obligation*
                        (fn-digest-tagged '(112) '(1))
                        (fn-digest-tagged '(101) '(2))))

(assert-event (fn-stmt-receipt-p (fn-t-receipt-1)))
(assert-event (equal (fn-stmt-receipt-decode-exact
                      (fn-stmt-receipt-encode (fn-t-receipt-1)))
                     (fn-stmt-ok (fn-t-receipt-1))))
(assert-event (equal (fn-stmt-receipt-term (fn-t-receipt-1))
                     (cons (fn-digest-tagged '(112) '(1))
                           (fn-digest-tagged '(101) '(2)))))
; teeth: each field's shape
(assert-event (not (fn-stmt-receipt-p
                    (fn-stmt-make-receipt '(1) *fn-t-obligation*
                                          (fn-digest-tagged '(112) '(1))
                                          (fn-digest-tagged '(101) '(2))))))
(assert-event (not (fn-stmt-receipt-p
                    (fn-stmt-make-receipt (fn-stmt-id (fn-t-stmt-1)) nil
                                          (fn-digest-tagged '(112) '(1))
                                          (fn-digest-tagged '(101) '(2))))))
(assert-event (not (fn-stmt-receipt-p
                    (fn-stmt-make-receipt (fn-stmt-id (fn-t-stmt-1))
                                          *fn-t-obligation* t
                                          (fn-digest-tagged '(101) '(2))))))
; The receipt codec's fuel is exactly its four items, so a trailing octet
; (a fifth, well-formed uint item) is refused as one item too many.
(assert-event (equal (fn-stmt-receipt-decode-exact
                      (append (fn-stmt-receipt-encode (fn-t-receipt-1)) '(0)))
                     (fn-stmt-error :too-many-items)))
(assert-event (equal (fn-stmt-receipt-decode-exact
                      (fn-stmt-encode-items (list '(:bytes 1 2 3))))
                     (fn-stmt-error :subject)))

; A receipt statement: kind :receipt, payload the receipt bytes.
(defun fn-t-receipt-stmt ()
  (fn-stmt-sign *fn-t-seed-bob* (make-list 32 :initial-element 5) 1 1 nil
                :receipt (fn-stmt-receipt-encode (fn-t-receipt-1))))
(assert-event (fn-stmt-p (fn-t-receipt-stmt)))
(assert-event (equal (fn-stmt-kind (fn-t-receipt-stmt)) :receipt))
(assert-event (equal (fn-stmt-receipt-decode-exact
                      (fn-stmt-payload (fn-t-receipt-stmt)))
                     (fn-stmt-ok (fn-t-receipt-1))))
