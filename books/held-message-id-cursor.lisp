; Paid validation of the SAME immutable held-row MsgID string. One character
; per action; no octet-list conversion or new size limit on the served path.
(in-package "ACL2")
(include-book "catalog-message-id-shape")
(include-book "acceptance-alloc")

(defun fn-hmid-at (i xs)
  (declare (xargs :guard (natp i) :measure (nfix i)))
  (if (zp i) (fn-ag-car xs) (fn-hmid-at (- i 1) (fn-ag-cdr xs))))

(defun fn-hmid-byte-ok (byte at length)
  (declare (xargs :guard t))
  (and (integerp byte) (<= 33 byte) (<= byte 126)
       (if (zp (nfix at)) (equal byte 60)
         (if (equal at (- (nfix length) 1)) (equal byte 62)
           (not (equal byte 62))))))

(defun fn-hmid-char-ok (text at)
  (declare (xargs :guard t))
  (and (stringp text) (natp at) (< at (length text))
       (fn-hmid-byte-ok (char-code (char text at)) at (length text))))

; (:held-msgid SAME-string position length prefix-valid).
(defun fn-hmid-begin (text)
  (declare (xargs :guard t))
  (let ((length (if (stringp text) (length text) 0)))
    (if (and (stringp text) (<= 3 length)
             (<= length *fn-nntp-max-message-id-octets*))
        (list :held-msgid text 0 length t)
      (list :held-msgid (if (stringp text) text "") length length nil))))

(defun fn-hmid-cursorp (cursor)
  (declare (xargs :guard t))
  (and (true-listp cursor) (equal (len cursor) 5)
       (equal (fn-hmid-at 0 cursor) :held-msgid)
       (stringp (fn-hmid-at 1 cursor))
       (natp (fn-hmid-at 2 cursor)) (natp (fn-hmid-at 3 cursor))
       (equal (fn-hmid-at 3 cursor) (length (fn-hmid-at 1 cursor)))
       (<= (fn-hmid-at 2 cursor) (fn-hmid-at 3 cursor))
       (booleanp (fn-hmid-at 4 cursor))))

(defun fn-hmid-status (cursor)
  (declare (xargs :guard t))
  (if (equal (fn-hmid-at 2 cursor) (fn-hmid-at 3 cursor))
      (if (fn-hmid-at 4 cursor) :valid :invalid) :yield))

(defun fn-hmid-one (cursor)
  (declare (xargs :guard (fn-hmid-cursorp cursor)))
  (let ((text (fn-hmid-at 1 cursor)) (at (fn-hmid-at 2 cursor))
        (length (fn-hmid-at 3 cursor)) (valid (fn-hmid-at 4 cursor)))
    (if (<= length at) cursor
      (list :held-msgid text (+ 1 at) length
            (and valid (fn-hmid-char-ok text at))))))

(defun fn-hmid-suffix-ok (text at)
  (declare (xargs :measure
                  (nfix (- (if (stringp text) (length text) 0) (nfix at)))
                  :guard t))
  (if (and (stringp text) (natp at) (< at (length text)))
      (and (fn-hmid-char-ok text at) (fn-hmid-suffix-ok text (+ 1 at)))
    t))

; Semantic carry is proof vocabulary only; ONE never computes the original
; converting reference or scans this suffix.
(defun fn-hmid-ready-p (cursor)
  (declare (xargs :guard t))
  (and (fn-hmid-cursorp cursor)
       (equal (and (fn-hmid-at 4 cursor)
                   (fn-hmid-suffix-ok (fn-hmid-at 1 cursor)
                                      (fn-hmid-at 2 cursor)))
              (fn-scat-msgid-idp (fn-hmid-at 1 cursor)))))

(defthm fn-hmid-begin-cursorp
  (fn-hmid-cursorp (fn-hmid-begin text))
  :hints (("Goal" :in-theory
           (enable fn-hmid-cursorp fn-hmid-begin fn-hmid-at fn-ag-car fn-ag-cdr))))

(defthm fn-hmid-one-preserves-cursorp
  (implies (fn-hmid-cursorp cursor)
           (fn-hmid-cursorp (fn-hmid-one cursor)))
  :hints (("Goal" :in-theory
           (enable fn-hmid-cursorp fn-hmid-one fn-hmid-at fn-ag-car fn-ag-cdr
                   fn-hmid-char-ok fn-hmid-byte-ok))))

(defthm fn-hmid-one-preserves-original-predicate-carry
  (implies (fn-hmid-ready-p cursor)
           (fn-hmid-ready-p (fn-hmid-one cursor)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((fn-hmid-suffix-ok (fn-hmid-at 1 cursor)
                                      (fn-hmid-at 2 cursor)))
           :in-theory
           (e/d (fn-hmid-ready-p fn-hmid-one fn-hmid-cursorp
                 fn-hmid-at fn-ag-car fn-ag-cdr)
                (fn-hmid-suffix-ok fn-hmid-char-ok fn-scat-msgid-idp)))))

(defthm fn-hmid-completed-status-is-original-predicate
  (implies (and (fn-hmid-ready-p cursor)
                (equal (fn-hmid-at 2 cursor) (fn-hmid-at 3 cursor)))
           (equal (equal (fn-hmid-status cursor) :valid)
                  (fn-scat-msgid-idp (fn-hmid-at 1 cursor))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((fn-hmid-suffix-ok (fn-hmid-at 1 cursor)
                                      (fn-hmid-at 2 cursor)))
           :in-theory
           (e/d (fn-hmid-ready-p fn-hmid-cursorp fn-hmid-status)
                (fn-hmid-at fn-hmid-char-ok fn-scat-msgid-idp)))))

(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defun fn-hmid-token-check (token at length)
   (declare (xargs :guard t))
   (if (consp token)
       (and (fn-hmid-byte-ok (car token) at length)
            (fn-hmid-token-check (cdr token) (+ 1 (nfix at)) length))
     t)))

(local
 (defthm fn-hmid-token-tail-reference
   (implies (and (true-listp token) (consp token) (posp at)
                 (equal length (+ at (len token))))
            (equal (fn-hmid-token-check token at length)
                   (and (fn-nntp-printable-tokenp token)
                        (fn-nntp-message-id-tailp token))))
   :hints (("Goal" :induct (fn-hmid-token-check token at length)
            :in-theory (enable fn-hmid-token-check fn-hmid-byte-ok
                               fn-nntp-printable-tokenp fn-nntp-message-id-tailp)))))

(local
 (defthm fn-hmid-token-full-reference
   (implies (and (true-listp token) (<= 3 (len token))
                 (<= (len token) *fn-nntp-max-message-id-octets*))
            (equal (fn-hmid-token-check token 0 (len token))
                   (fn-nntp-message-id-tokenp token)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hmid-token-tail-reference
                             (token (cdr token)) (at 1) (length (len token))))
            :in-theory (enable fn-hmid-token-check fn-hmid-byte-ok
                               fn-nntp-message-id-tokenp fn-nntp-printable-tokenp)))))

(local
 (defthm fn-hmid-string-octets-length
   (equal (len (fn-nntp-string-octets-aux chars)) (len chars))
   :hints (("Goal" :induct (fn-nntp-string-octets-aux chars)
            :in-theory (enable fn-nntp-string-octets-aux)))))

(local
 (defthm fn-hmid-string-octets-tail
   (equal (nthcdr n (fn-nntp-string-octets-aux chars))
          (fn-nntp-string-octets-aux (nthcdr n chars)))
   :hints (("Goal" :induct (nthcdr n chars)
            :in-theory (enable fn-nntp-string-octets-aux nthcdr)))))

(local
 (defthm fn-hmid-char-tail-next
   (implies (and (natp at) (< at (len chars)))
            (equal (fn-nntp-string-octets-aux (nthcdr at chars))
                   (cons (char-code (nth at chars))
                         (fn-nntp-string-octets-aux (nthcdr (+ 1 at) chars)))))
   :hints (("Goal" :induct (nthcdr at chars)
            :in-theory (enable fn-nntp-string-octets-aux nthcdr nth)))))

(local
 (defthm fn-hmid-string-tail-next
   (implies (and (stringp text) (natp at) (< at (length text)))
            (equal (nthcdr at (fn-nntp-string-octets text))
                   (cons (char-code (char text at))
                         (nthcdr (+ 1 at) (fn-nntp-string-octets text)))))
   :hints (("Goal" :use ((:instance fn-hmid-char-tail-next
                                    (chars (coerce text 'list))))
            :in-theory (enable fn-nntp-string-octets length char)))))

(local
 (defthm fn-hmid-token-check-of-cons
   (equal (fn-hmid-token-check (cons byte rest) at length)
          (and (fn-hmid-byte-ok byte at length)
               (fn-hmid-token-check rest (+ 1 (nfix at)) length)))
   :hints (("Goal" :in-theory (enable fn-hmid-token-check)))))

(local
 (defthm fn-hmid-chars-tail-empty
   (implies (and (true-listp chars) (natp at) (<= (len chars) at))
            (equal (nthcdr at chars) nil))
   :hints (("Goal" :induct (nthcdr at chars)
            :in-theory (enable nthcdr len true-listp)))))

(local
 (defthm fn-hmid-string-tail-empty
   (implies (and (stringp text) (natp at) (<= (length text) at))
            (equal (nthcdr at (fn-nntp-string-octets text)) nil))
   :hints (("Goal" :use ((:instance fn-hmid-chars-tail-empty
                                    (chars (coerce text 'list))))
            :in-theory (enable fn-nntp-string-octets length
                               fn-nntp-string-octets-aux)))))

(local
 (defthm fn-hmid-suffix-is-original-token-check
   (implies (and (stringp text) (natp at))
            (equal (fn-hmid-suffix-ok text at)
                   (fn-hmid-token-check
                    (nthcdr at (fn-nntp-string-octets text)) at (length text))))
   :hints (("Goal" :induct (fn-hmid-suffix-ok text at)
            :expand ((fn-hmid-token-check nil at (length text)))
            :in-theory
            (e/d (fn-hmid-suffix-ok fn-hmid-char-ok)
                 (fn-hmid-token-check fn-nntp-string-octets-aux nthcdr
                  fn-nntp-string-octets fn-hmid-byte-ok length char))))))

(local
 (defthm fn-hmid-string-octets-true-list
   (true-listp (fn-nntp-string-octets-aux chars))
   :hints (("Goal" :induct (fn-nntp-string-octets-aux chars)
            :in-theory (enable fn-nntp-string-octets-aux)))))

(local
 (defthm fn-hmid-full-string-reference
   (implies (and (stringp text) (<= 3 (length text))
                 (<= (length text) *fn-nntp-max-message-id-octets*))
            (equal (fn-hmid-suffix-ok text 0) (fn-scat-msgid-idp text)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hmid-token-full-reference
                             (token (fn-nntp-string-octets text)))
                  (:instance fn-hmid-suffix-is-original-token-check (at 0)))
            :in-theory
            (e/d (fn-scat-msgid-idp fn-nntp-string-octets length)
                 (fn-nntp-string-octets-aux fn-hmid-suffix-ok
                  fn-hmid-token-check fn-nntp-message-id-tokenp))))) )

(defthm fn-hmid-begin-establishes-original-predicate-carry
  (fn-hmid-ready-p (fn-hmid-begin text))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hmid-full-string-reference))
           :in-theory
           (e/d (fn-hmid-ready-p fn-hmid-begin fn-hmid-cursorp fn-hmid-at
                 fn-ag-car fn-ag-cdr fn-scat-msgid-idp fn-nntp-string-octets
                 fn-nntp-message-id-tokenp length)
                (fn-hmid-suffix-ok fn-nntp-string-octets-aux
                 fn-nntp-printable-tokenp fn-nntp-message-id-tailp)))))
