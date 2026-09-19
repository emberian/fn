; The overview projection of RFC 3977 sections 8.3 and 8.4.
;
; Section 8.3.2 fixes a transformation, not a format: every field is the
; header content with all CRLF pairs removed and each remaining TAB - and, the
; section adds, each NUL, LF and CR - replaced by a single space.  That
; transformation is what makes an overview line safe: a field that still
; carried a TAB would invent a field boundary, and a field that still carried
; CR or LF would split the line and so split the response.
;
; This book proves that of the actual renderer.  `fn-nov-scrub' produces a
; clean field for ANY input octets, with no hypothesis at all; a header the
; article does not carry produces the empty field; the two metadata items are
; the exact retained octet count and the exact retained body line count; and
; the eight-field line is clean, so books/nntp-effects.lisp can read it back as
; a block line of a well-formed response.
(in-package "ACL2")
(include-book "nntp")

; -----------------------------------------------------------------------------
; A clean overview field

(defun fn-nov-field-octetp (byte)
  (declare (xargs :guard t))
  (and (integerp byte) (<= 1 byte) (<= byte 255)
       (not (equal byte 9)) (not (equal byte 13)) (not (equal byte 10))))

(defun fn-nov-clean-fieldp (bytes)
  (declare (xargs :guard t))
  (if (consp bytes)
      (and (fn-nov-field-octetp (car bytes))
           (fn-nov-clean-fieldp (cdr bytes)))
    (null bytes)))

; A line is clean when it carries no CR, LF or NUL; TAB separates its fields.
(defun fn-nov-line-octetp (byte)
  (declare (xargs :guard t))
  (and (integerp byte) (<= 1 byte) (<= byte 255)
       (not (equal byte 13)) (not (equal byte 10))))

(defun fn-nov-clean-linep (bytes)
  (declare (xargs :guard t))
  (if (consp bytes)
      (and (fn-nov-line-octetp (car bytes))
           (fn-nov-clean-linep (cdr bytes)))
    (null bytes)))

(defun fn-nov-clean-line-listp (lines)
  (declare (xargs :guard t))
  (if (consp lines)
      (and (fn-nov-clean-linep (car lines))
           (fn-nov-clean-line-listp (cdr lines)))
    (null lines)))

(defthm fn-nov-clean-field-is-a-clean-line
  (implies (fn-nov-clean-fieldp bytes)
           (fn-nov-clean-linep bytes)))

(defthm fn-nov-clean-line-of-append
  (implies (and (fn-nov-clean-linep x) (fn-nov-clean-linep y))
           (fn-nov-clean-linep (append x y))))

(defthm fn-nov-clean-line-true-listp
  (implies (fn-nov-clean-linep x) (true-listp x)))

; -----------------------------------------------------------------------------
; The section 8.3.2 transformation is total

(defthm fn-nov-scrub-is-clean
  (fn-nov-clean-fieldp (fn-nov-scrub bytes)))

(defthm fn-nov-scrub-removes-crlf-pairs
  (equal (fn-nov-scrub (append '(13 10) rest))
         (fn-nov-scrub rest)))

(defthm fn-nov-scrub-of-nil
  (equal (fn-nov-scrub nil) nil))

; -----------------------------------------------------------------------------
; A header the article does not carry gives the empty field

(defthm fn-nov-missing-header-is-empty
  (implies (not (consp (fn-article-get-headers view name)))
           (equal (fn-nov-header-content view name) nil)))

(defthm fn-nov-header-content-is-clean
  (fn-nov-clean-fieldp (fn-nov-header-content view name)))

; -----------------------------------------------------------------------------
; A projected overview record

(defun fn-nov-overviewp (over)
  (declare (xargs :guard t))
  (and (true-listp over)
       (equal (len over) 8)
       (equal (car over) :ok)
       (fn-nov-clean-fieldp (fn-nov-subject over))
       (fn-nov-clean-fieldp (fn-nov-from over))
       (fn-nov-clean-fieldp (fn-nov-date over))
       (fn-nov-clean-fieldp (fn-nov-msgid over))
       (fn-nov-clean-fieldp (fn-nov-references over))
       (natp (fn-nov-bytes over))
       (natp (fn-nov-lines over))))

(defthm fn-nov-overview-is-an-overview
  (implies (fn-nov-okp (fn-nov-overview article))
           (fn-nov-overviewp (fn-nov-overview article))))

; The two metadata items are computed from the exact retained octets, never
; from a normalized or re-encoded copy.
(defthm fn-nov-bytes-is-the-retained-octet-count
  (implies (fn-nov-okp (fn-nov-overview article))
           (equal (fn-nov-bytes (fn-nov-overview article))
                  (len (fn-article-payload article)))))

(defthm fn-nov-lines-counts-the-retained-body-lines
  (implies (fn-nov-okp (fn-nov-overview article))
           (equal (fn-nov-lines (fn-nov-overview article))
                  (fn-nov-body-line-count (fn-article-payload article)))))

; -----------------------------------------------------------------------------
; The rendered line

(defthm fn-nov-string-octets-aux-true-listp
  (true-listp (fn-nntp-string-octets-aux chars)))

(defthm fn-nov-decimal-token-is-clean
  (implies (and (fn-nntp-decimal-tokenp token) (true-listp token))
           (fn-nov-clean-fieldp token)))

(defthm fn-nov-decimal-field-is-clean
  (fn-nov-clean-fieldp (fn-nntp-decimal-field number)))

(defthm fn-nov-append-pieces-of-cons
  (equal (fn-nntp-append-pieces (cons x y))
         (append x (fn-nntp-append-pieces y))))

; RFC 3977 section 8.3.2: eight fields separated by TAB, carrying no CR, LF or
; NUL anywhere.  The TABs are the separators the renderer itself writes; no
; field can contribute one.
(defthm fn-nov-line-is-a-clean-line
  (implies (fn-nov-overviewp over)
           (fn-nov-clean-linep (fn-nov-line number over)))
  :hints (("Goal" :in-theory (disable fn-nov-subject fn-nov-from fn-nov-date
                                      fn-nov-msgid fn-nov-references
                                      fn-nov-bytes fn-nov-lines))))

(defthm fn-nov-lines-for-numbers-are-clean
  (fn-nov-clean-line-listp (fn-nov-lines-for-numbers group numbers articles)))

(defthm fn-nov-fmt-lines-are-clean
  (fn-nov-clean-line-listp (fn-nov-fmt-octet-lines texts)))

(verify-guards fn-nov-field-octetp)
(verify-guards fn-nov-clean-fieldp)
(verify-guards fn-nov-line-octetp)
(verify-guards fn-nov-clean-linep)
(verify-guards fn-nov-clean-line-listp)
(verify-guards fn-nov-overviewp)
