; fn: the paged catalog's row store (stage 3 of
; planning/design-store-representation-2026-10-01.md), one declaration of
; books/def-representation.lisp, in its own book so that its generated
; events and the catalog's refinement (books/catalog-paged.lisp) each
; certify within the D26 budget (lane paged-catalog-4, 2026-10-01).
;
; The columns carry the positions of a held record the executable reads
; without a decode; `aux' is the REMAINDER as one tree in the pool
; (books/def-representation-tree.lisp).  WRITE-ONCE: no octets or tree
; field has a set export, so the pool is written only by an append and its
; fill is the load of the rows (fn-crow$c-fill-is-load-of-*): a withdrawal
; writes its three columns, never the pool (Codex r21 F1).

(in-package "ACL2")
(include-book "def-representation")
(include-book "def-representation-tree")

(def-representation fn-crow
  (seq :u64) (txid :u64) (gen :u64) (payload :u64) (charge :u64) (stamp :u64)
  (msgid :octets)
  (wpres :bool) (wat :u64) (wby :u64)
  (esc :bool)
  (aux :tree)
  :write-once t)
