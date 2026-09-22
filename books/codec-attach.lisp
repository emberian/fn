; fn: every codec seam's attachment, in one include.
;
; Each codec seam (plan 2026-09-22 §4.1) constrains its codec's public names
; and has an attachment book that makes them evaluate.  A book that evaluates
; ground terms reaching any codec -- the saved image, a test book with ground
; vectors, a Python host session -- includes this one book, so a seam added
; later reaches every evaluator by one line here.  No proof book above the
; seams includes it: `defattach' changes no theorem, and a proof book that
; included it would carry the implementations it is meant not to see.

(in-package "ACL2")
(include-book "records-attach")
(include-book "statement-attach")

; A constant computed through a seam.  ACL2 evaluates a `defconst' body
; without attachments, so `(defconst *x* (fn-record-encode r))' fails with
; "cannot ev the call of non-executable function" even where this book is
; included.  A `make-event' expansion is evaluated with them: the constant
; below is the value the attached codec computes, written into the book's
; certificate as a quoted literal.  It is a test book's datum, not a
; theorem: a proof about it reasons about the literal, and an exact-byte
; fact a proof needs still comes from the concrete codec book.
(defmacro fn-defconst-attached (name form)
  `(make-event (list 'defconst ',name (list 'quote ,form))))
