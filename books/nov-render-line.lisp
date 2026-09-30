; Exact original NOV tuple accessors and line renderer, RFC 3977 section 8.3.2.
; Extracted verbatim from nntp-responses for the actual OVER row join.
(in-package "ACL2")
(include-book "nntp-session")

(defun fn-nov-okp (x)
  (mbe :logic (equal (car x) :ok) :exec (equal (fn-ag-car x) :ok)))
(defun fn-nov-subject (x)
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-nov-from (x)
  (mbe :logic (car (cdr (cdr x))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(defun fn-nov-date (x)
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))
(defun fn-nov-msgid (x)
  (mbe :logic (car (cdr (cdr (cdr (cdr x)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))
(defun fn-nov-references (x)
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr x))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                                          (fn-ag-cdr x))))))))
(defun fn-nov-bytes (x)
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr x)))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                                          (fn-ag-cdr (fn-ag-cdr x)))))))))
(defun fn-nov-lines (x)
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr x))))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                                          (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))))) 

; The eight mandatory fields of RFC 3977 section 8.3.2, TAB separated, in
; order.  No ninth field is emitted: this profile holds no Xref or other
; overview metadata, and section 8.3.2 makes subsequent fields optional.
(defun fn-nov-line (number over)
  (fn-nntp-append-pieces
   (list (fn-nntp-decimal-field number) '(9)
         (fn-nov-subject over) '(9)
         (fn-nov-from over) '(9)
         (fn-nov-date over) '(9)
         (fn-nov-msgid over) '(9)
         (fn-nov-references over) '(9)
         (fn-nntp-decimal (fn-nov-bytes over)) '(9)
         (fn-nntp-decimal (fn-nov-lines over)))))

(verify-guards fn-nov-okp)
(verify-guards fn-nov-subject)
(verify-guards fn-nov-from)
(verify-guards fn-nov-date)
(verify-guards fn-nov-msgid)
(verify-guards fn-nov-references)
(verify-guards fn-nov-bytes)
(verify-guards fn-nov-lines)
(verify-guards fn-nov-line)
