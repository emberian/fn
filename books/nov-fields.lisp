;; fn: the overview fields of an article's view (RFC 3977 section 8.3.2),
;; moved out of books/nntp-responses.lisp (lane served-columns, 2026-09-27)
;; so that the intern decides the overview COLUMNS with the same functions
;; the served readers render them with: books/catalog-record.lisp fn-hnov-of
;; (the held row's facts) and books/nntp-responses.lisp fn-nov-overview both
;; call fn-nov-header-content.  Definitions unchanged.
;;
;; Every overview field comes from the proved article view in books/article.lisp
;; through its header lookup; the section 8.3.2 transformation is applied
;; once, by fn-nov-scrub: CRLF pairs are removed (undoing folding and the
;; terminating CRLF) and each remaining TAB, NUL, LF or CR becomes a single
;; space.  The resulting field therefore carries none of TAB, CR, LF or NUL, so
;; it can neither split a line nor invent a ninth field.

(in-package "ACL2")
(include-book "article-fields")
(include-book "acceptance-alloc")

(defconst *fn-nov-subject-name* '(115 117 98 106 101 99 116))
(defconst *fn-nov-from-name* '(102 114 111 109))
(defconst *fn-nov-date-name* '(100 97 116 101))
(defconst *fn-nov-message-id-name* '(109 101 115 115 97 103 101 45 105 100))
(defconst *fn-nov-references-name* '(114 101 102 101 114 101 110 99 101 115))

(defun fn-nov-scrub-byte (byte)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (integerp byte) (<= 1 byte) (<= byte 255)
           (not (equal byte 9)) (not (equal byte 13)) (not (equal byte 10)))
      byte
    32))

(defun fn-nov-scrub (bytes)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count bytes)))
  (if (consp bytes)
      (if (and (equal (fn-ag-car bytes) 13)
               (consp (fn-ag-cdr bytes))
               (equal (fn-ag-car (fn-ag-cdr bytes)) 10))
          (fn-nov-scrub (fn-ag-cdr (fn-ag-cdr bytes)))
        (cons (fn-nov-scrub-byte (fn-ag-car bytes))
              (fn-nov-scrub (fn-ag-cdr bytes))))
    nil))

; RFC 3977 section 8.3.2: the field is the header content, that is, the header
; name and its following colon and space removed.  The parsed view's unfolded
; value begins immediately after the colon.
(defun fn-nov-value-content (value)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp value) (equal (fn-ag-car value) 32))
      (fn-ag-cdr value)
    value))

(defun fn-nov-header-content (view name)
  (declare (xargs :guard (fn-article-syntax-p view) :verify-guards nil))
  (let ((fields (fn-article-get-headers view name)))
    (if (consp fields)
        (fn-nov-scrub (fn-nov-value-content
                       (fn-article-field-unfolded-value (car fields))))
      nil)))


(local
 (defthm fn-nov-get-headers-aux-car-true-listp
   (implies (and (fn-article-field-listp fields)
                 (consp (fn-article-get-headers-aux fields name)))
            (true-listp (car (fn-article-get-headers-aux fields name))))
   :hints (("Goal" :use fn-af-guard-get-headers-aux-car-fieldp
            :in-theory (e/d (fn-article-fieldp) (fn-af-guard-get-headers-aux-car-fieldp))))))

(local
 (defthm fn-nov-get-headers-car-is-a-field
   (implies (and (fn-article-syntax-p view)
                 (consp (fn-article-get-headers view name)))
            (and (fn-article-fieldp (car (fn-article-get-headers view name)))
                 (true-listp (car (fn-article-get-headers view name)))))
   :hints (("Goal" :in-theory (enable fn-article-get-headers fn-article-syntax-p)))))

(verify-guards fn-nov-scrub-byte)

(verify-guards fn-nov-scrub)

(verify-guards fn-nov-value-content)

; The article accessors stay closed here so that
; fn-nov-get-headers-car-is-a-field (local, above) is what discharges
; the field obligation; opening fn-article-get-headers buries it.
(verify-guards fn-nov-header-content
  :hints (("Goal" :in-theory (disable fn-article-get-headers
                                      fn-article-syntax-p))))

