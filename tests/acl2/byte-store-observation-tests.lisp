(in-package "ACL2")
(include-book "../../books/byte-store-observation")

; Renaming a physical inode does not change a visible file observation.
(assert-event
 (let ((left '(:byte-store 4 ((1 . (10 11)))
                            ((:root . (("a" . 1))) (:transactions) (:staging))
                            nil 2))
       (right '(:byte-store 4 ((73 . (10 11)))
                             ((:root . (("a" . 73))) (:transactions) (:staging))
                             nil 74)))
   (fn-bso-served-image-agree left right)))

; A changed octet, a missing publication name, and a broken hard-link alias
; must all be visible to the relation.  The alias check uses two names so a
; comparison of transaction counts alone cannot pass it.
(assert-event
 (let* ((base '(:byte-store 4 ((1 . (10 11)))
                             ((:root . (("a" . 1)))
                              (:transactions . (("1.txn" . 1) ("2.txn" . 1)))
                              (:staging)) nil 2))
        (corrupt '(:byte-store 4 ((73 . (10 12)))
                               ((:root . (("a" . 73)))
                                (:transactions . (("1.txn" . 73) ("2.txn" . 73)))
                                (:staging)) nil 74))
        (missing '(:byte-store 4 ((73 . (10 11)))
                               ((:root . (("a" . 73)))
                                (:transactions . (("1.txn" . 73)))
                                (:staging)) nil 74))
        (alias '(:byte-store 4 ((73 . (10 11)) (74 . (10 11)))
                             ((:root . (("a" . 73)))
                              (:transactions . (("1.txn" . 73) ("2.txn" . 74)))
                              (:staging)) nil 75)))
   (and (not (fn-bso-served-image-agree base corrupt))
        (not (fn-bso-served-image-agree base missing))
        (not (fn-bso-served-image-agree base alias)))))
