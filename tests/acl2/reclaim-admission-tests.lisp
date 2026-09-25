; fn: witnesses and teeth for books/reclaim-admission.lisp (D13, STO-014,
; PRF-088): a tombstone-shaped payload is refused where every served ingress
; asks, and contributes nothing to the statement index.
(in-package "ACL2")
(include-book "../../books/reclaim-admission")
(include-book "../../books/store-reclaim")
(include-book "std/testing/must-fail" :dir :system)
; A verified article (*stxt-r1*) and the keyring it verifies under.
(include-book "stx-transit-tests")

(defconst *ra-article* '(72 58 32 120 13 10 13 10 98 111 100 121)) ; "H: x" CRLF CRLF "body"
(defconst *ra-tomb* (fn-rcl-tombstone-of *ra-article* (fn-record-string-octets "<a1@x>")))

; Keystone witness: the tombstone the Store writes for a real article is
; refused as not an article; the article it replaced is admitted
; (carrier-absent, the legacy Store path).
(assert-event (fn-rcl-tombstonep *ra-tomb*))
(assert-event (equal (fn-pa-carrier-form *ra-tomb*) '(:refused :article)))
(assert-event (equal (fn-pa-carrier-form *ra-article*) :absent))
; Tooth (tombstonep): without it an admitted article is a counterexample.
(must-fail (assert-event (equal (fn-pa-carrier-form *ra-article*) '(:refused :article))))

; fn-rca-nul-first-octet-is-not-an-article.  Witness: the article with its
; first octet replaced by NUL.  Tooth (first octet NUL): the article parses.
(assert-event (not (fn-article-result-okp (fn-article-parse (cons 0 (cdr *ra-article*))))))
(must-fail (assert-event (not (fn-article-result-okp (fn-article-parse *ra-article*)))))

; fn-rca-nul-line-is-no-field.  Witness and tooth over "H: x".
(assert-event (not (fn-article-line-okp (fn-article-new-field '(0 58 32 120)))))
(must-fail (assert-event (not (fn-article-line-okp (fn-article-new-field '(72 58 32 120))))))

; fn-rcl-tombstone-contributes-nothing.  Witness: the tombstone under the
; keyring that verifies *stxt-r1*.  Tooth (tombstonep): *stxt-r1* itself
; contributes its statement.
(assert-event (equal (fn-stx-delta *ra-tomb* *stxt-keyring*) nil))
(must-fail (assert-event (equal (fn-stx-delta (fn-article-payload *stxt-r1*) *stxt-keyring*)
                                nil)))
