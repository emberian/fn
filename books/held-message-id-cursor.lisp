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

(defun-nx fn-hmid-suffix-ok (text at)
  (declare (xargs :measure
                  (nfix (- (if (stringp text) (length text) 0) (nfix at)))
                  :verify-guards nil))
  (if (and (stringp text) (natp at) (< at (length text)))
      (and (fn-hmid-char-ok text at) (fn-hmid-suffix-ok text (+ 1 at)))
    t))

; Semantic carry is proof vocabulary only; ONE never computes the original
; converting reference or scans this suffix.
(defun-nx fn-hmid-ready-p (cursor)
  (declare (xargs :verify-guards nil))
  (and (fn-hmid-cursorp cursor)
       (equal (and (fn-hmid-at 4 cursor)
                   (fn-hmid-suffix-ok (fn-hmid-at 1 cursor)
                                      (fn-hmid-at 2 cursor)))
              (fn-scat-msgid-idp (fn-hmid-at 1 cursor)))))
