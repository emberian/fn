; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-log-sealed-slices")

(local (defthm fn-lblar-range-in-append
 (equal (fn-lb-log-model-range-in-entries off count (append entries tail))
        (or (fn-lb-log-model-range-in-entries off count entries)
            (fn-lb-log-model-range-in-entries off count tail)))
 :hints (("Goal" :induct (len entries)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-range-in-entries binary-append)))) ))

(local (defthm fn-lblar-new-entry-covers-interval
 (implies (and (fn-cat-rowp row) (fn-cbor-octet-listp payload)
               (natp off) (natp count) (<= (len (cadr segment)) off)
               (<= (+ off count) (+ (len (cadr segment)) (len (fn-lb-log-model-next-prefix row payload)) 32)))
 (fn-lb-log-model-range-in-entries off count
  (caddr (fn-lb-log-model-append-to-segment row payload segment))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-next-entry-well-typed))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-append-to-segment-directory-by-definition fn-lblar-range-in-append
 fn-lb-log-model-range-in-entries fn-lb-log-next-entry-entry-offset-by-definition
 fn-lb-log-next-entry-protected-length-by-definition))))))

(local (defthm fn-lblar-appended-segment-present
 (consp (fn-lb-log-model-append-to-segment row payload segment))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-log-model-append-to-segment (:executable-counterpart consp))))) :rule-classes :type-prescription))

(local (defthm fn-lblar-len-append
 (equal (len (append a b)) (+ (len a) (len b)))
 :hints (("Goal" :induct (len a) :in-theory (enable binary-append len)))))

(defthm fn-lb-log-read-appended-interval
 (implies (and (fn-cat-rowp row) (fn-cbor-octet-listp payload)
               (natp off) (natp count)
               (<= (len (cadr (fn-lb-log-model-segment target log))) off)
               (<= (+ off count)
                (+ (len (cadr (fn-lb-log-model-segment target log)))
                   (len (fn-lb-log-model-next-prefix row payload)) 32)))
 (equal (fn-lb-log-model-read-range target off count (fn-lb-log-model-append row payload target log))
        (take count (nthcdr off
          (cadr (fn-lb-log-model-append-to-segment row payload
           (list target (cadr (fn-lb-log-model-segment target log))
                        (caddr (fn-lb-log-model-segment target log)))))))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lblar-new-entry-covers-interval
        (segment (list target (cadr (fn-lb-log-model-segment target log))
                              (caddr (fn-lb-log-model-segment target log))))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-read-range fn-lb-log-segment-of-append
 fn-lb-log-append-to-segment-bytes-by-definition fn-lblar-len-append
 fn-blake3-stobj-satisfies-fn-frame-digest-length (:type-prescription fn-lblar-appended-segment-present))))))
