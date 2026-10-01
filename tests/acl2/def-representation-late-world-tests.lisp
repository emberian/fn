; The generator in a late world (gate-b-2's robustness finding): every kind
; of instance -- a record, one with a :tree field and write-once, a scalar,
; a generic -- declared after the whole of the paged catalog's world
; (books/catalog-paged.lisp, the largest world that includes the
; generator), so no theory the catalog leaves behind may break a generated
; proof.  Each instance's reservation export is the identity.

(in-package "ACL2")
(include-book "../../books/catalog-paged")

(def-representation lw-rec (a :u64) (m :octets))
(def-representation lw-tree (a :u64) (b (:nat 32)) (m :octets) (t1 :tree) :write-once t)
(def-representation lw-scalar (v :octets) :scalar t)
(def-representation lw-gen (a :u64) (m :octets) :generic t)

(defthm lw-reserve-is-identity
  (and (equal (lw-rec-reserve rows octets lw-rec) lw-rec)
       (equal (lw-tree-reserve rows octets lw-tree) lw-tree)
       (equal (lw-scalar-reserve rows octets lw-scalar) lw-scalar))
  :rule-classes nil)
