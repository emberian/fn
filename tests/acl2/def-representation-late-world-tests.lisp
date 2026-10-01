; The generator in a late world (gate-b-2's robustness finding): a record
; and a scalar instance (the two foundations' paths; the :tree, write-once
; and generic paths were admitted there too in the gate-b-4 hbox REPL, left
; out here for D26) declared after the whole of the paged catalog's world
; (books/catalog-paged.lisp, the largest world that includes the
; generator), so no theory the catalog leaves behind may break a generated
; proof.  Each instance's reservation export is the identity.

(in-package "ACL2")
(include-book "../../books/catalog-paged")

(def-representation lw-rec (a :u64) (m :octets))
(def-representation lw-scalar (v :octets) :scalar t)

(defthm lw-reserve-is-identity
  (and (equal (lw-rec-reserve rows octets lw-rec) lw-rec)
       (equal (lw-scalar-reserve rows octets lw-scalar) lw-scalar))
  :rule-classes nil)
