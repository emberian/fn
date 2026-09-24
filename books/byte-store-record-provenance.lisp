; K6: the actual P-RECORD program must publish exactly the whole frame it
; wrote and fenced, not merely a record with matching decoded fields.
;
; The proofs live in three books, each certified on its own so that none
; carries the whole include closure and all of the K6/K0 events at once
; (the ten-second rule, docs/proofs.md): the byte-store programs, their
; join to the Store node, and the configured-owner callbacks.  This book
; is what dependents include; it exports their union, in which the proof
; steps a later part reuses are disabled.
(in-package "ACL2")
(include-book "byte-store-record-provenance-bytes")
(include-book "byte-store-record-provenance-node")
(include-book "byte-store-record-provenance-owner")
