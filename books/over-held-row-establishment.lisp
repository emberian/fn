; Internal selected-row constructor domain. Registered source/visibility and
; actual QPG ownership remain separate producer obligations.
(in-package "ACL2")
(include-book "over-held-row-carry")

(local
 (defthm fn-ohr-digit-run-is-octets
  (implies (and (true-listp bytes) (fn-nntp-decimal-tokenp bytes))
           (fn-cbor-octet-listp bytes))
  :hints (("Goal" :induct (fn-nntp-decimal-tokenp bytes)
           :in-theory (enable fn-nntp-decimal-tokenp fn-nntp-decimal-digitp
                              fn-cbor-octet-listp fn-cbor-octetp)))))

(local
 (defthm fn-ohr-number-piece-shape
  (fn-npw-partp (fn-nntp-decimal-field number) fn-arena)
  :hints (("Goal" :in-theory
           (enable fn-npw-partp fn-nntp-decimal-field
                   fn-nntp-decimal-tokenp fn-nntp-decimal-digitp)))))

(local
 (defthm fn-ohr-cached-pieces-shape
  (implies (fn-hnov-p (fn-hf-nov facts))
           (fn-npw-piecesp (fn-npw-column-pieces number facts octets) fn-arena))
  :hints (("Goal" :in-theory
           (e/d (fn-npw-column-pieces fn-npw-piecesp fn-npw-partp
                 fn-hnov-p fn-hnov-internals)
                (fn-nntp-decimal-field))))))

(defthm fn-ohr-selected-row-begin-establishes-carried-row-domain
 (implies (and (true-listp range)
               (natp (fn-record-payload row))
               (< (fn-record-payload row) (fn-arena-count fn-arena))
               (or (not (fn-hf-nov (fn-held-facts row)))
                   (fn-hnov-p (fn-hf-nov (fn-held-facts row)))))
          (fn-ohr-carried-p
            (fn-ohr-selected-row-begin range origin row fn-arena) fn-arena))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lpc-begin-ready
          (h (fn-record-payload row))
          (n (fn-arena-payload-len (fn-record-payload row) fn-arena)) (pin origin))
        (:instance fn-lpc-begin-establishes-bounds
          (h (fn-record-payload row))
          (n (fn-arena-payload-len (fn-record-payload row) fn-arena)) (pin origin)))
  :in-theory
  (e/d (fn-ohr-selected-row-begin fn-ohr-carried-p fn-obc-row-ready
        fn-obc-make fn-obc-begin fn-obc-next-range fn-ovw-cursor
        fn-npw-piecesp fn-npw-partp fn-ovw-status)
       (fn-lpc-ready-p fn-lpc-cursor-bounds-p fn-lpc-begin
        fn-npw-column-pieces fn-hf-nov fn-hnov-p fn-hnov-ok fn-hnov-tomb
        fn-record-payload fn-held-facts fn-arena-count-is-len
        fn-arena-payload-len-is-len-nth)))))
