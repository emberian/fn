; fn prototype (lane proto-adt-2, 2026-09-27): the topic projection's
; accepted-statement table as an ADT type (books/proto/adt-topic-accepted.lisp
; bridges it to the model).  The declaration lives in its own book so its
; generated proofs run in the library's theory, not the model's: in a world
; that also includes books/topic-history-prefix the same declaration costs
; 18 s instead of 6 (the includer's rules reach the generated proofs).

(in-package "ACL2")
(include-book "adt-keyed")

(defadt-keyed stxa :order :stack :key sequence
  (sequence :u32) (txid :u32) (generation :u32) (keyring-generation :u32)
  (profile :octets) (content-subject :octets) (article-record :octets) (verdict-event :octets)
  (authored-source (:alt :legacy (:octets)))
  (authored-id (:alt nil (:octets))))
