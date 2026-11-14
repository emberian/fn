; Concrete per-capability transport storage, generated once by defcolumns.
(in-package "ACL2")
(include-book "columns")
(fn2-book-layer :a)

(defcolumns fn2-tls-transport
 ((cap :u32) (nonce :u60) (slot :u32) (generation :u60)
  (seed-total :u32) (seed-capacity :u32) (quantum :u32)
  (window :u32) (alive :bool) (cleanup-credit :bool)
  (handle-id :u64 :why "Opaque library allocation identity, never protocol identity or an arithmetic address.")
  (budget :u32) (serial :u60) (copied :u32) (fed :u32)
  (input-length :u32) (input-offset :u32)
  (output-length :u32) (output-offset :u32)
  ;; SSL status: 0 complete, 1 WANT_READ, 2 WANT_WRITE, 5 must-call.
  (ssl-status :u8) (terminal :u8)
  ;; Action: 0 none, 1 copy, 2 seed feed, 3 input feed, 4 drain,
  ;; 5 send, 6 recv, 7 handshake, 8 allocate, 9 free. I/O spans are bounded by quantum.
  (pending :u8) (offset :u32) (requested :u32)
  ;; Exact physical return before normalization. Signed code is represented
  ;; by sign + magnitude; raw errno/count never substitute for one another.
  (raw-negative :bool) (raw-code :u64 :why "Exact opaque allocation address or signed primitive return magnitude.") (raw-count :u32) (raw-errno :u32))
 :rows-bound 2)

; One generated reader theory, shared by guards and ownership proofs.
(make-event
 (let* ((row (fn2-decl-row '(:columns fn2-tls-transport) (w state)))
        (readers (fn2-columns-projection-readers 'fn2-tls-transport
                   (fn2-decl-get :columns row))))
  (value `(deftheory fn2-tls-transport-readers
            ',(cons 'fn2-tls-transport-rows readers)))))
