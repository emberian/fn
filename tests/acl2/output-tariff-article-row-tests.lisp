; Witnesses and teeth for books/output-tariff-article-row.lisp: the ARTICLE
; tariff read from the row the factory serves.  The fixture is the
; served-catalog tests' (three committed articles, views are counts); every
; witness is ground and proved by evaluation; a must-fail form follows the
; affirmative check of what it omits.
(in-package "ACL2")
(include-book "../../books/output-tariff-article-row")
(include-book "must-fail-checked")

(defconst *tar-p0* (append (fn-record-string-octets "Subject: a") '(13 10 13 10 65 13 10)))
(defconst *tar-p1* (append (fn-record-string-octets "Subject: bb") '(13 10 13 10 66 66 13 10)))
(defconst *tar-p2* (append (fn-record-string-octets "Subject: c") '(13 10 13 10 67 13 10)))
(defconst *tar-w0* (fn-record-make 0 1 1 "<a@x>" *tar-p0* '("fn.test") "o" "s" "e" 1 5))
(defconst *tar-w1* (fn-record-make 1 2 2 "<b@x>" *tar-p1* '("fn.test" "fn.other") "o" "s" "e" 1 5))
(defconst *tar-w2* (fn-record-make 2 3 3 "<c@x>" *tar-p2* '("fn.test") "o" "s" "e" 1 5))

(defun tar-held (w handle numbers)
  (fn-held-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                (fn-record-msgid w) handle (fn-record-groups w) (fn-record-obligation-id w)
                (fn-record-content-subject w) (fn-record-release-evidence w)
                (fn-record-charge w) (fn-record-stamp w)
                (fn-held-facts-of (fn-record-payload w))
                (fn-held-context-of (fn-record-payload w) nil 0) numbers nil))

(defconst *tar-a* (list *tar-p0* *tar-p1* *tar-p2*))
(defconst *tar-r0* (fn-cat-assign (tar-held *tar-w0* 0 nil) nil))
(defconst *tar-r1* (fn-cat-assign (tar-held *tar-w1* 1 nil) (list *tar-r0*)))
(defconst *tar-r2* (fn-cat-assign (tar-held *tar-w2* 2 nil) (list *tar-r0* *tar-r1*)))
(defconst *tar-c* (list *tar-r0* *tar-r1* *tar-r2*))
; A session: its group fn.test and current article 3 (the accessors read
; the second and third fields, books/nntp-session.lisp).
(defconst *tar-session* '(:session "fn.test" 3))

; The length the producer reads is the stored octets' length, per row.
(defthm tar-number-charges
  (and (equal (len *tar-p0*) 17) (equal (len *tar-p1*) 19)
       (equal (fn-tariff-article-number-charge "fn.test" 1 nil *tar-a* *tar-c*) 17)
       (equal (fn-tariff-article-number-charge "fn.test" 2 nil *tar-a* *tar-c*) 19)
       (equal (fn-tariff-article-number-charge "fn.other" 1 nil *tar-a* *tar-c*) 19)
       (equal (fn-tariff-article-number-charge "fn.test" 9 nil *tar-a* *tar-c*) 0))
  :rule-classes nil)

; KEYSTONE witness: at the view where row 2 is visible the served octets are
; exactly the charge; at a view where it is not, nothing is served and the
; charge still names the row (an upper bound at every view, never under).
(defthm tar-prices-the-served-row-witness
  (and (equal (len (fn-nntp-article-bytes (fn-scat-number-article "fn.test" 3 3 *tar-a* *tar-c*) *tar-a*))
              (fn-tariff-article-number-charge "fn.test" 3 nil *tar-a* *tar-c*))
       (consp (fn-scat-number-article "fn.test" 3 3 *tar-a* *tar-c*))
       (equal (fn-scat-number-article "fn.test" 3 2 *tar-a* *tar-c*) nil)
       (equal (fn-tariff-article-number-charge "fn.test" 3 nil *tar-a* *tar-c*) 17))
  :rule-classes nil)

; Teeth: the charge is NOT the length served at every view (the row is not
; served at view 2), so a statement without the visibility arm is false.
(must-fail-checked
 (defthm tar-teeth-charge-is-not-view-length
   (equal (len (fn-nntp-article-bytes (fn-scat-number-article "fn.test" 3 2 *tar-a* *tar-c*) *tar-a*))
          (fn-tariff-article-number-charge "fn.test" 3 nil *tar-a* *tar-c*))
   :rule-classes nil))

; The Message-ID form: the longest row carrying it.
(defthm tar-msgid-charges
  (and (equal (fn-tariff-article-msgid-charge "<b@x>" nil *tar-a* *tar-c*) 19)
       (equal (fn-tariff-article-msgid-charge "<z@x>" nil *tar-a* *tar-c*) 0)
       (<= (len (fn-nntp-article-bytes (fn-scat-msgid-article "<b@x>" 3 *tar-a* *tar-c*) *tar-a*))
           (fn-tariff-article-msgid-charge "<b@x>" nil *tar-a* *tar-c*)))
  :rule-classes nil)

; The row's forms: a number, the current article, a Message-ID, and the
; forms that name no row.
(defthm tar-row-charges
  (and (equal (fn-tariff-article-row-charge *tar-session* '((50)) nil *tar-a* *tar-c*) 19)
       (equal (fn-tariff-article-row-charge *tar-session* nil nil *tar-a* *tar-c*) 17)
       (equal (fn-tariff-article-row-charge *tar-session* '((60 98 64 120 62)) nil *tar-a* *tar-c*) 19)
       (equal (fn-tariff-article-row-charge '(:session nil nil) '((50)) nil *tar-a* *tar-c*) 0)
       (equal (fn-tariff-article-row-charge *tar-session* '((49) (50)) nil *tar-a* *tar-c*) 0)
       (equal (fn-tariff-article-descriptor
               (fn-tariff-article-row-charge *tar-session* '((50)) nil *tar-a* *tar-c*))
              (list :tariff :article (fn-tariff-article-octets 19))))
  :rule-classes nil)

; With an Xref server, a row in two groups is charged the two renders of the
; compatibility form; a row in one group too, its Xref line still prepended.
(defthm tar-xref-charges
  (let ((plain (fn-tariff-article-number-charge "fn.test" 2 nil *tar-a* *tar-c*))
        (xref (fn-tariff-article-number-charge "fn.test" 2 '(110 101 119 115) *tar-a* *tar-c*)))
    (and (equal plain 19)
         (< 0 (fn-tariff-article-xref-octets '(110 101 119 115)
                                             (fn-cat-row-article 1 *tar-a* *tar-c*)))
         (equal xref (+ (* 2 19)
                        (fn-tariff-article-xref-octets '(110 101 119 115)
                                                       (fn-cat-row-article 1 *tar-a* *tar-c*))
                        146))))
  :rule-classes nil)
