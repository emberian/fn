; fn: the wire composite a HISTORY event carries, in either vocabulary
; (records-flip wave, lane flip-L3, 2026-09-27).
;
; After the records flip the Store history retains an accepted statement as
; the composite ROW `fn-hstxa-p' (books/held-record.lisp): the wire composite
; (`fn-stxa-p') beside its article interned as a held record.  A function
; that reads a statement's composite out of the history (its verdict event,
; its authored source, its txid, its carried charge) reads the composite the
; row carries; a wire composite handed to it directly (a fresh acceptance,
; before the intern) is read as before.  This is the one unwrapping, so every
; such function handles the retained composite exactly as it handles the
; wire one.  Its relation to ALPHA (`fn-row-wire-of', books/store-intern.lisp)
; is books/history-fold-refinement.lisp.
(in-package "ACL2")
(include-book "held-record")

(defun fn-hw-composite (e)
  (declare (xargs :guard t))
  (if (fn-hstxa-p e) (fn-hstxa-stxa e) e))

(defthm fn-hw-composite-of-a-row
  (implies (fn-hstxa-p e)
           (equal (fn-hw-composite e) (fn-hstxa-stxa e))))

(defthm fn-hw-composite-of-a-wire-event
  (implies (not (fn-hstxa-p e))
           (equal (fn-hw-composite e) e)))

; A row's composite is a wire composite, and a wire composite is its own.
(defthm fn-stxa-p-of-hw-composite
  (implies (or (fn-hstxa-p e) (fn-stxa-p e))
           (fn-stxa-p (fn-hw-composite e))))

(in-theory (disable fn-hw-composite))
