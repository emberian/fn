; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-log-next-entry-type")

(local (defthm fn-lblss-len-append
 (equal (len (append a b)) (+ (len a) (len b)))
 :hints (("Goal" :induct (len a) :in-theory (enable binary-append len)))))

(local (defthm fn-lblss-proper-append
 (implies (true-listp b) (true-listp (append a b)))
 :hints (("Goal" :induct (len a) :in-theory (enable binary-append true-listp)))))

(local (defthm fn-lblss-nthcdr-length-prefix
 (equal (nthcdr (len a) (append a b)) b)
 :hints (("Goal" :induct (len a) :in-theory (enable nthcdr binary-append len)))))

(local (defthm fn-lblss-take-length-prefix
 (implies (true-listp a) (equal (take (len a) (append a b)) a))
 :hints (("Goal" :induct (len a) :in-theory (enable take binary-append len true-listp)))))

(local (defthm fn-lblss-take-length-self
 (implies (true-listp a) (equal (take (len a) a) a))
 :hints (("Goal" :induct (len a) :in-theory (enable take len true-listp)))))

(local (defthm fn-lblss-nthcdr-plus-prefix
 (implies (natp n) (equal (nthcdr (+ (len a) n) (append a b)) (nthcdr n b)))
 :hints (("Goal" :induct (len a) :in-theory (enable nthcdr binary-append len)))))

(local (defthm fn-lblss-fix-proper
 (implies (true-listp a) (equal (true-list-fix a) a))
 :hints (("Goal" :induct (len a) :in-theory (enable true-list-fix true-listp)))))

(local (defthm fn-lblss-append-associative
 (equal (append (append a b) c) (append a b c))
 :hints (("Goal" :induct (len a) :in-theory (enable binary-append)))))

(local (defthm fn-lblss-nthcdr-three-prefixes
 (equal (nthcdr (+ (len a) (len b) (len c)) (append a b c d)) d)
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lblss-nthcdr-plus-prefix (n (+ (len b) (len c))) (b (append b c d)))
       (:instance fn-lblss-nthcdr-plus-prefix (a b) (n (len c)) (b (append c d))))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lblss-nthcdr-length-prefix))))))

(defthm fn-lb-log-sealed-prefix-is-verified
 (implies (true-listp prefix)
 (fn-arx-entry-ok (append prefix (fn-blake3-stobj prefix)) (len prefix)))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-arx-entry-ok fn-lblss-fix-proper fn-lblss-proper-append fn-lblss-len-append
 fn-lblss-take-length-prefix fn-lblss-nthcdr-length-prefix
 fn-blake3-stobj-satisfies-fn-frame-digest-length
 fn-blake3-stobj-satisfies-fn-frame-digest-octet-listp fn-cbor-octet-listp-implies-true-listp)))))

(defthm fn-lb-log-appended-range-byte-slice
 (implies (true-listp payload)
 (equal (take (len (fn-lb-log-model-next-range payload))
  (nthcdr (+ (len (cadr segment)) (len (fn-lb-log-model-pre row payload)))
   (cadr (fn-lb-log-model-append-to-segment row payload segment))))
  (fn-lb-log-model-next-range payload)))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-lblss-nthcdr-three-prefixes fn-lblss-append-associative fn-lb-log-append-to-segment-bytes-by-definition fn-lb-log-model-next-prefix
 fn-lblss-nthcdr-plus-prefix fn-lblss-nthcdr-length-prefix fn-lblss-take-length-prefix
 fn-lb-log-next-range-true-listp)))))

(defthm fn-lb-log-appended-home-byte-slice
 (implies (fn-cat-rowp row)
 (equal (take (len (fn-lb-log-model-home-frame row))
  (nthcdr (+ (len (cadr segment)) (len (fn-lb-log-model-pre row payload))
             (len (fn-lb-log-model-next-range payload)))
   (cadr (fn-lb-log-model-append-to-segment row payload segment))))
  (fn-lb-log-model-home-frame row)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lblss-nthcdr-three-prefixes
 (a (cadr segment)) (b (fn-lb-log-model-pre row payload))
 (c (fn-lb-log-model-next-range payload))
 (d (append (fn-lb-log-model-home-frame row)
            (fn-blake3-stobj (fn-lb-log-model-next-prefix row payload))))))
 :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-lblss-append-associative fn-lb-log-append-to-segment-bytes-by-definition fn-lb-log-model-next-prefix
 fn-lblss-nthcdr-plus-prefix fn-lblss-nthcdr-length-prefix fn-lblss-take-length-prefix
 fn-lb-log-model-home-frame-true-listp)))))

(defthm fn-lb-log-appended-entry-byte-slice
 (implies (fn-cat-rowp row)
 (equal (take (+ (len (fn-lb-log-model-next-prefix row payload)) 32)
   (nthcdr (len (cadr segment)) (cadr (fn-lb-log-model-append-to-segment row payload segment))))
  (append (fn-lb-log-model-next-prefix row payload)
          (fn-blake3-stobj (fn-lb-log-model-next-prefix row payload)))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lblss-take-length-self
 (a (append (fn-lb-log-model-next-prefix row payload)
             (fn-blake3-stobj (fn-lb-log-model-next-prefix row payload))))))
 :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-lblss-nthcdr-three-prefixes fn-lblss-append-associative fn-lb-log-append-to-segment-bytes-by-definition fn-lblss-nthcdr-length-prefix
 fn-lblss-proper-append fn-lblss-len-append
 fn-lb-log-next-prefix-true-listp fn-blake3-stobj-satisfies-fn-frame-digest-length
 fn-blake3-stobj-satisfies-fn-frame-digest-octet-listp fn-cbor-octet-listp-implies-true-listp)))))
