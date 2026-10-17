(in-package "ACL2")
(include-book "../../books/nntp-overview")

; Literal positive witness of the actual renderer's clean-line theorem,
; including both metadata fields above ten digits, not a 10 GiB allocation.
(defconst *npwt-wide-over* '(:ok (83) (70) (68) (60 109 62) nil
                           123456789012345678901234567890 10000000000))
(defconst *npwt-wide-line*
  '(55 9 83 9 70 9 68 9 60 109 62 9 9
    49 50 51 52 53 54 55 56 57 48 49 50 51 52 53 54 55 56 57 48
    49 50 51 52 53 54 55 56 57 48 9 49 48 48 48 48 48 48 48 48 48 48))

(assert-event
 (and (fn-nov-overviewp *npwt-wide-over*)
      (fn-nov-clean-linep (fn-nov-line 7 *npwt-wide-over*))
      (equal (fn-nov-line 7 *npwt-wide-over*) *npwt-wide-line*)))

; Retained hypotheses are empty for the unconditional full-decimal
; cleanliness lemma. Exact digits are checked at zero and the former limit.
(assert-event
 (and (fn-nov-clean-fieldp (fn-nntp-decimal 0))
      (equal (fn-nntp-decimal 0) '(48))
      (equal (fn-nov-line 7 '(:ok (83) (70) (68) (60 109 62) nil 123 2))
             '(55 9 83 9 70 9 68 9 60 109 62 9 9 49 50 51 9 50))
      (equal (fn-nntp-decimal 9999999999) '(57 57 57 57 57 57 57 57 57 57))
      (equal (fn-nntp-decimal 10000000000) '(49 48 48 48 48 48 48 48 48 48 48))))

; Initial status-number rendering retains its separate bounded behavior.
(assert-event (equal (fn-nntp-decimal-field 10000000000) '(48)))

; Removing the overview shape admits an embedded LF and breaks cleanliness.
(assert-event
 (let ((over '(:ok (10) nil nil nil nil 10000000000 10000000000)))
   (and (not (fn-nov-overviewp over))
        (not (fn-nov-clean-linep (fn-nov-line 7 over))))))

; Semantic line framing consumes the actual rendered row once, with exact
; CRLF and the block terminator; wide metadata introduces no extra field.
(assert-event
 (equal (fn-nntp-multi nil "224 overview" (list (fn-nov-line 7 *npwt-wide-over*)))
        (fn-nntp-make-result nil
         (list (fn-nntp-reply-effect
                (append (fn-nntp-string-octets "224 overview") '(13 10)
                        *npwt-wide-line* '(13 10 46 13 10)))))))
