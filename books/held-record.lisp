; fn: the held record's SHAPE (records-flip, 2026-09-27; D33; PKT-635).
;
; Two views of one record.  The WIRE record is `fn-record-p'
; (books/records-shape.lisp): an octet-list payload, the codec's domain.
; The HELD record is what the store's history, the acceptance state and the
; catalog retain: the same eleven positions, read by the SAME positional
; accessors (`fn-record-sequence' .. `fn-record-stamp' are `mbe' selectors
; with guard t, so they read either view), with the payload position holding
; a natural, a HANDLE into the arena (books/payload-arena.lisp), and four
; positions after it:
;
;   11 facts     (octets body-start body-lines control)  decided ONCE from the bytes at intern
;   12 context   (verdict delta generation)        decided at intern under the keyring in force
;   13 numbers   ((group . n) ...)                 assigned by the catalog's commit; nil before
;   14 withdrawn nil | (at . by)                   the version at which a cancel withdrew it
;
; Its recognizer is `fn-held-p', never `fn-record-p': the predicate that
; means "contains octets" is not reused to mean "contains an integer".
;
; This book is the shape alone, so that books/store-events.lisp can name
; `fn-held-p' as the history's article disjunct without the arena, the lace
; parser or the served splitter.  What is decided FROM bytes (the facts of a
; payload, the context under a keyring, alpha through the arena, the intern)
; is books/catalog-record.lisp, which includes this one.
;
; The retained accepted-statement event is `fn-hstxa-p': the wire composite
; (`fn-stxa-p', books/stx-accept-records.lisp; kept whole for the identity
; fold, which verifies its statement) beside its article INTERNED as a held
; record.  A bare `fn-stxa-p' is never a retained event: replaying one would
; hand the composite's octet list to `fn-accept-prepare', which after the
; flip refuses everything but a handle.
(in-package "ACL2")
(include-book "held-record-shape")
(include-book "stx-accept-records")

; -----------------------------------------------------------------------------
; The retained accepted-statement event.

(defun fn-hstxa-p (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 3)
       (eq (car x) :hstxa)
       (fn-stxa-p (car (cdr x)))
       (fn-held-p (car (cdr (cdr x))))))

(include-book "held-composite-fields")





(defthm fn-hstxa-accessors-of-make
  (and (equal (fn-hstxa-stxa (fn-hstxa-make stxa held)) stxa)
       (equal (fn-hstxa-held (fn-hstxa-make stxa held)) held)))

(defthm fn-hstxa-p-of-make
  (equal (fn-hstxa-p (fn-hstxa-make stxa held))
         (and (fn-stxa-p stxa) (fn-held-p held))))

(defthm fn-hstxa-p-fields
  (implies (fn-hstxa-p x)
           (and (fn-stxa-p (fn-hstxa-stxa x))
                (fn-held-p (fn-hstxa-held x))))
  :rule-classes (:rewrite :forward-chaining))

(defthm fn-hstxa-p-forward-shape
  (implies (fn-hstxa-p x)
           (and (consp x) (true-listp x) (equal (len x) 3) (eq (car x) :hstxa)))
  :rule-classes :forward-chaining)

(in-theory (disable fn-hstxa-p fn-hstxa-make fn-hstxa-stxa fn-hstxa-held))

; -----------------------------------------------------------------------------
; Proof vocabulary: the held record's recognizer and shape, opened by a book
; that reasons about a row's fields, the way `fn-record-shape-vocabulary'
; (books/records-shape.lisp) is for the wire record.
; Withdrawn on include, like the wire record's recognizer (books/records-shape
; .lisp): opened, fn-held-p unfolds fifteen field recognizers, two of them
; recursive (fn-lace-p, fn-held-numbersp), and a goal that merely dispatches
; on the event kind then carries them all (books/replay.lisp's first theorem
; ran past 300 s with it open, run-20260927T035647Z-7bc9).  The forward
; shape facts (consp, true-listp) stay: fn-held-p-forward-shape and the
; field facts fn-held-p-fields.  A book that reasons about a row's fields
; enables fn-held-vocabulary locally.
(in-theory (disable (:d fn-held-p) (:d fn-held-shapep) (:d fn-held-numbersp)
                    (:d fn-held-withdrawnp) (:d fn-hf-p) (:d fn-hf-shapep)
                    (:d fn-hf-startp) (:d fn-hc-p) (:d fn-hc-shapep) (:d fn-hc-anyp) (:d fn-hc-verdictp)))

(deftheory fn-held-vocabulary
  '((:d fn-held-p) (:d fn-held-shapep) (:d fn-held-numbersp) (:d fn-held-withdrawnp)
    (:d fn-hf-p) (:d fn-hf-shapep) (:d fn-hf-startp)
    (:d fn-hc-p) (:d fn-hc-shapep) (:d fn-hc-anyp) (:d fn-hc-verdictp)
    (:d fn-hstxa-p) (:d fn-hstxa-make) (:d fn-hstxa-stxa) (:d fn-hstxa-held)))
