; The generator in a late world (gate-b-2's robustness finding): a record
; instance (the :tree, write-once, scalar and generic paths were admitted
; there too in the gate-b-4 hbox REPL, left out here for D26) declared after the whole of the paged catalog's world
; (books/catalog-paged.lisp, the largest world that includes the
; generator), so no theory the catalog leaves behind may break a generated
; proof.  Its reservation export is the identity.

(in-package "ACL2")
(include-book "../../books/catalog-paged")

(def-representation lw-rec (a :u64) (m :octets))

(defthm lw-reserve-is-identity
  (equal (lw-rec-reserve rows octets lw-rec) lw-rec)
  :rule-classes nil)
