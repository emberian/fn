; Teeth for books/node-secret.lisp (SEC-006, PRF-210): HMAC-SHA256 against
; RFC 4231, HKDF-SHA256 against RFC 5869, the info-label separation
; fn-ns-expand-input-separates-info with a witness and one removal per
; hypothesis, and the key file's round trip fn-ns-file-parse-of-render.
(in-package "ACL2")
(include-book "../../books/node-secret")
(include-book "must-fail-checked")

(defun nst-codes (cs)
  (if (consp cs) (cons (char-code (car cs)) (nst-codes (cdr cs))) nil))
(defun nst-octets (s) (nst-codes (coerce s 'list)))
(defun nst-hex (octets)
  (if (consp octets)
      (let ((d "0123456789abcdef"))
        (concatenate 'string (string (char d (floor (car octets) 16)))
                     (string (char d (mod (car octets) 16)))
                     (nst-hex (cdr octets))))
    ""))
(defun nst-range (lo hi) (declare (xargs :measure (nfix (- hi lo))))
  (if (and (natp lo) (natp hi) (< lo hi)) (cons lo (nst-range (1+ lo) hi)) nil))

; RFC 4231 test cases 2 and 6 (a key over the block length is hashed first).
(assert-event
 (equal (nst-hex (fn-ns-hmac-sha256 (nst-octets "Jefe")
                                    (nst-octets "what do ya want for nothing?")))
        "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"))
(assert-event
 (equal (nst-hex (fn-ns-hmac-sha256
                  (make-list 131 :initial-element 170)
                  (nst-octets "Test Using Larger Than Block-Size Key - Hash Key First")))
        "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"))

; RFC 5869 appendix A, test cases 1 and 3 (SHA-256): PRK and the first
; 32 octets of OKM (T(1)).
(assert-event
 (and (equal (nst-hex (fn-ns-hkdf-extract (nst-range 0 13) (make-list 22 :initial-element 11)))
             "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5")
      (equal (nst-hex (fn-ns-hkdf-sha256-32 (nst-range 0 13) (make-list 22 :initial-element 11)
                                            (nst-range 240 250)))
             "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf")))
(assert-event
 (and (equal (nst-hex (fn-ns-hkdf-extract nil (make-list 22 :initial-element 11)))
             "19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04")
      (equal (nst-hex (fn-ns-hkdf-sha256-32 nil (make-list 22 :initial-element 11) nil))
             "8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d")))

; The info labels are the ones the review names.
(assert-event (equal *fn-ns-cancel-lock-info* (nst-octets "fn/cancel-lock/v1")))
(assert-event (equal *fn-ns-posting-account-info* (nst-octets "fn/posting-account/v1")))
(assert-event (equal (fn-ns-secret-width) 32))

; A ring of two epochs: epoch 2 current, epoch 1 retained.
(defconst *nst-e1* (fn-ns-create-entry (nst-octets "hbox.ember.software")
                                       (make-list 32 :initial-element 7)))
(defconst *nst-e2* (fn-ns-rotate-entry *nst-e1* nil (make-list 32 :initial-element 9)))
(defconst *nst-ring* (list *nst-e2* *nst-e1*))
(assert-event (and (fn-ns-entryp *nst-e1*) (fn-ns-entryp *nst-e2*)
                   (equal (fn-ns-entry-epoch *nst-e1*) 1)
                   (equal (fn-ns-entry-epoch *nst-e2*) 2)
                   (equal (fn-ns-entry-identity *nst-e2*) (nst-octets "hbox.ember.software"))
                   (fn-ns-ringp *nst-ring*)
                   (not (fn-ns-ringp (list *nst-e1* *nst-e2*)))   ; epochs must decrease
                   (not (fn-ns-ringp nil))))
; The default identity.
(assert-event (equal (fn-ns-entry-identity (fn-ns-create-entry nil (make-list 32 :initial-element 7)))
                     (nst-octets "local")))

; fn-ns-expand-input-separates-info.  Witness: the two labels the node uses.
(assert-event
 (and (true-listp *fn-ns-cancel-lock-info*) (true-listp *fn-ns-posting-account-info*)
      (not (equal *fn-ns-cancel-lock-info* *fn-ns-posting-account-info*))
      (not (equal (fn-ns-expand-input *fn-ns-cancel-lock-info*)
                  (fn-ns-expand-input *fn-ns-posting-account-info*)))
      ; and the purpose keys of one entry differ
      (not (equal (fn-ns-cancel-lock-key *nst-e2*) (fn-ns-posting-account-key *nst-ring*)))))
; Removal of "distinct": equal labels expand the same input.
(assert-event
 (and (true-listp *fn-ns-cancel-lock-info*)
      (equal (fn-ns-expand-input *fn-ns-cancel-lock-info*)
             (fn-ns-expand-input *fn-ns-cancel-lock-info*))))
; Removal of true-listp: labels differing only in their final cdr expand
; the same input.
(assert-event
 (let ((i1 '(102 110 . 5)) (i2 '(102 110 . 6)))
   (and (true-listp nil) (not (true-listp i1)) (not (equal i1 i2))
        (equal (fn-ns-expand-input i1) (fn-ns-expand-input i2)))))
(must-fail-checked
 (defthm nst-separation-needs-distinct-labels
   (implies (and (true-listp i1) (true-listp i2))
            (not (equal (fn-ns-expand-input i1) (fn-ns-expand-input i2))))))

; The derived keys are bound to the node identity and the epoch: another
; identity or another root gives another key.
(assert-event
 (and (not (equal (fn-ns-cancel-lock-key *nst-e1*)
                  (fn-ns-cancel-lock-key (fn-ns-make-entry 1 (nst-octets "other")
                                                           (make-list 32 :initial-element 7)))))
      (not (equal (fn-ns-cancel-lock-key *nst-e1*) (fn-ns-cancel-lock-key *nst-e2*)))))

; fn-ns-file-parse-of-render: witness, and the parse refuses what is not a
; v1 file of one entry.
(defconst *nst-file* (fn-ns-file-render *nst-e2*))
(assert-event (and (fn-ns-entryp *nst-e2*)
                   (equal (len *nst-file*) (+ 18 4 2 19 32))
                   (equal (fn-ns-file-parse *nst-file*) *nst-e2*)))
(assert-event (null (fn-ns-file-parse (cdr *nst-file*))))                 ; bad magic
(assert-event (null (fn-ns-file-parse (append *nst-file* '(0)))))         ; 33-octet root
(assert-event (null (fn-ns-file-parse (butlast *nst-file* 1))))           ; 31-octet root
(assert-event (null (fn-ns-file-parse (make-list 61 :initial-element 0))))
; Removal of fn-ns-entryp: a v1 file naming epoch 0 is no entry, and the
; parse refuses it.
(assert-event
 (let ((e (fn-ns-make-entry 0 nil (make-list 32 :initial-element 7))))
   (and (not (fn-ns-entryp e))
        (null (fn-ns-file-parse (append *fn-ns-file-magic* '(0 0 0 0) '(0 0)
                                        (make-list 32 :initial-element 7)))))))
