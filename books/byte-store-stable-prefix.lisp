; K5: every modeled crash preserves the exact durable transaction prefix.
; The second inequality excludes a second or synthetic transaction.  Both
; claims are conditional on the existing byte/kernel relation; proving that
; arbitrary native programs establish it remains K0.
(in-package "ACL2")
(include-book "byte-store-scan")

(local
 (defthm fn-bs-k5-len-of-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(defthm fn-bs-related-durable-records-true-list
  (implies (fn-bs-store-relation bs ks)
           (true-listp (fn-bs-durable-records bs)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 (:instance fn-bs-read-records-is-a-true-list
                            (s (fn-bs-durable bs)) (n 0)
                            (count (len (fn-bs-durable-names bs :transactions)))))
           :in-theory (enable fn-bs-durable-records))))

(defthm fn-bs-stable-prefix-retained-by-byte-crash
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-crash-imagep bs image))
           (and (fn-sf-prefixp
                 (fn-bs-durable-records bs)
                 (fn-bs-scan-records (fn-bs-scan-store image)))
                (<= (len (fn-bs-scan-records (fn-bs-scan-store image)))
                    (1+ (len (fn-bs-durable-records bs))))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-crash-image-scan-records
                 fn-bs-store-crash-image-scans
                 fn-bs-store-relation-unfolds
                 fn-bs-related-durable-records-true-list
                 fn-bs-crash-image-reads-the-linked-record
                 (:instance fn-bs-scan-okp-unfolds (s image))
                 (:instance fn-sf-prefixp-reflexive
                            (xs (fn-bs-durable-records bs)))
                 (:instance fn-sf-prefixp-append
                            (xs (fn-bs-durable-records bs))
                            (ys (fn-bs-read-records
                                 image
                                 (len (fn-bs-durable-names bs :transactions))
                                 (1+ (len (fn-bs-durable-names bs :transactions))))))
                 (:instance fn-bs-read-records-len
                            (s image)
                            (n (len (fn-bs-durable-names bs :transactions)))
                            (count (1+ (len (fn-bs-durable-names bs :transactions))))))
           :in-theory (disable fn-bs-store-relation fn-bs-crash-imagep
                               fn-bs-scan-store fn-bs-read-records
                               fn-bs-durable-records fn-bs-durable-names
                               fn-sf-prefixp))))
