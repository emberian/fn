; fn: the catalog may take a sealed POST payload (lane arena-forget,
; 2026-10-03; the leak family of a reclaim that seals before it decides).
;
; host/native/owner.lisp fnn-owner-attempt sealed the POST's buffer and
; THEN asked the catalog to prepare the row naming it
; (host/owner-host.lisp fn-owner-cat-prepare-sealed).  That prepare refuses
; :recovery-required when the index writer holds a ticket that is not
; finished, or a prepared catalog commit is pending -- conditions that held
; before the seal -- and the sealed payload stayed in the arena, named by no
; row, for the life of the process.  The host now asks this word, a pure
; function of the ticket and the pending commit, BEFORE the seal, under the
; same owner-mutex hold, and seals nothing when it answers nil.
;
; KEYSTONE fn-cat-may-seal-is-the-prepare-gate: the word is exactly the
; negation of the prepare's :recovery-required test, so after it answers t
; the prepare reaches its produced arm (whose :not-sealed and :pending are
; unreachable over a seal at count - 1, books/served-catalog-owner.lisp).

(in-package "ACL2")
(include-book "index-writer-ticket")

(defun fn-cat-may-seal (ticket pending)
  (declare (xargs :guard t))
  (and (fn-iwt-idlep ticket)
       (not pending)
       t))

(defthm fn-cat-may-seal-is-the-prepare-gate
  (iff (fn-cat-may-seal ticket pending)
       (not (or (not (fn-iwt-idlep ticket)) pending))))
