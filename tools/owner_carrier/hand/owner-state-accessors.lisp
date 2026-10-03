; Exact owner state accessors shared by host transitions and their proofs.
; The owner lives in its own stobj (books/owner-carrier.lisp); the readers
; take FN-OWNER-ST.  No state effects, new decision, or invariant
; revalidation is introduced.
(in-package "ACL2")
(include-book "owner-config")
(include-book "owner-carrier")

(defun fn-owner-core (fn-owner-st)
  (declare (xargs :stobjs fn-owner-st))
  (fn-ocfg-owner (fn-owner-ocfg fn-owner-st)))

(defun fn-owner-store (fn-owner-st)
  (declare (xargs :stobjs fn-owner-st))
  (fn-own-store (fn-owner-core fn-owner-st)))

; Definitional aliases, not cited keystones. They preserve the projection
; rewriting the host guard proofs used before these definitions moved.
(defthm fn-owner-core-is-configured-owner-by-definition
  (equal (fn-owner-core fn-owner-st) (fn-ocfg-owner (fn-owner-ocfg fn-owner-st)))
  :hints (("Goal" :in-theory (enable fn-owner-core))))

(defthm fn-owner-store-is-configured-store-by-definition
  (equal (fn-owner-store fn-owner-st)
         (fn-own-store (fn-ocfg-owner (fn-owner-ocfg fn-owner-st))))
  :hints (("Goal" :in-theory (enable fn-owner-store))))

(in-theory (disable fn-owner-core fn-owner-store))
