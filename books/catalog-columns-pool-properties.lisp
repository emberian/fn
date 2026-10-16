; Exact counts of the native paged byte-pool writers; these are not cost counters.
(in-package "ACL2")
(include-book "catalog-columns-writer-frames")

(local (defthm fn-lbpc-len-append-singleton
 (equal (len (append x (list value))) (+ 1 (len x)))
 :hints (("Goal" :induct (len x) :in-theory (union-theories (theory 'ground-zero) '(binary-append len))))))

(local (defthm fn-lbpc-overview-count-of-store-update
 (equal (fn-lbc-overview-pool-count (update-fn-lbc-overview-store value fn-lbc)) (len value))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-overview-pool-count fn-lbc-overview-store update-fn-lbc-overview-store fn-lbc-overview-octets-count-is-len fn-dm-nth-update-nth (:executable-counterpart nfix) (:executable-counterpart equal)))))))

(local (defthm fn-lbpc-overview-count-by-store
 (equal (fn-lbc-overview-pool-count fn-lbc) (len (fn-lbc-overview-store fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-overview-pool-count fn-lbc-overview-octets-count-is-len))))))

(defthm fn-lbc-overview-pool-count-of-append
 (equal (fn-lbc-overview-pool-count (fn-lbc-overview-pool-append bytes fn-lbc))
        (+ (len bytes) (fn-lbc-overview-pool-count fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-overview-pool-append bytes fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-overview-pool-append fn-lbc-overview-store update-fn-lbc-overview-store fn-dm-nth-update-nth fn-lbpc-overview-count-of-store-update fn-lbpc-overview-count-by-store
   fn-lbc-overview-octets-append-is-append fn-lbpc-len-append-singleton len
   associativity-of-+ commutativity-of-+)))) )

(local (defthm fn-lbpc-msgid-count-of-store-update
 (equal (fn-lbc-msgid-pool-count (update-fn-lbc-msgid-store value fn-lbc)) (len value))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid-pool-count fn-lbc-msgid-store update-fn-lbc-msgid-store fn-lbc-msgid-octets-count-is-len fn-dm-nth-update-nth (:executable-counterpart nfix) (:executable-counterpart equal)))))))

(local (defthm fn-lbpc-msgid-count-by-store
 (equal (fn-lbc-msgid-pool-count fn-lbc) (len (fn-lbc-msgid-store fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-msgid-pool-count fn-lbc-msgid-octets-count-is-len))))))

(defthm fn-lbc-msgid-pool-count-of-append
 (equal (fn-lbc-msgid-pool-count (fn-lbc-msgid-pool-append bytes fn-lbc))
        (+ (len bytes) (fn-lbc-msgid-pool-count fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-msgid-pool-append bytes fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-msgid-pool-append fn-lbc-msgid-store update-fn-lbc-msgid-store fn-dm-nth-update-nth fn-lbpc-msgid-count-of-store-update fn-lbpc-msgid-count-by-store
   fn-lbc-msgid-octets-append-is-append fn-lbpc-len-append-singleton len
   associativity-of-+ commutativity-of-+)))) )
