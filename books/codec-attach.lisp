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
