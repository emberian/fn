; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-log-appended-range")

(local (defthm fn-lblnr-len-append
 (equal (len (append a b)) (+ (len a) (len b)))
 :hints (("Goal" :induct (len a) :in-theory (enable binary-append len)))))

(defthm fn-lb-log-next-prefix-length
 (equal (len (fn-lb-log-model-next-prefix row payload))
  (+ (len (fn-lb-log-model-pre row payload)) (len (fn-lb-log-model-next-range payload))
     (len (fn-lb-log-model-home-frame row))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-next-prefix fn-lblnr-len-append)))))

(defthm fn-lb-log-read-new-payload-interval
 (implies (and (fn-cat-rowp row) (fn-cbor-octet-listp payload))
 (equal (fn-lb-log-model-read-range target (+ (len (cadr (fn-lb-log-model-segment target log))) (len (fn-lb-log-model-pre row payload))) (len (fn-lb-log-model-next-range payload))
         (fn-lb-log-model-append row payload target log)) (fn-lb-log-model-next-range payload)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-read-appended-interval (off (+ (len (cadr (fn-lb-log-model-segment target log))) (len (fn-lb-log-model-pre row payload)))) (count (len (fn-lb-log-model-next-range payload))))
       (:instance fn-lb-log-appended-range-byte-slice (segment (list target (cadr (fn-lb-log-model-segment target log)) (caddr (fn-lb-log-model-segment target log))))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-next-prefix-length fn-cbor-octet-listp-implies-true-listp)))))

(defthm fn-lb-log-read-new-home-interval
 (implies (and (fn-cat-rowp row) (fn-cbor-octet-listp payload))
 (equal (fn-lb-log-model-read-range target (+ (len (cadr (fn-lb-log-model-segment target log))) (len (fn-lb-log-model-pre row payload)) (len (fn-lb-log-model-next-range payload))) (len (fn-lb-log-model-home-frame row))
         (fn-lb-log-model-append row payload target log)) (fn-lb-log-model-home-frame row)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-read-appended-interval (off (+ (len (cadr (fn-lb-log-model-segment target log))) (len (fn-lb-log-model-pre row payload)) (len (fn-lb-log-model-next-range payload)))) (count (len (fn-lb-log-model-home-frame row))))
       (:instance fn-lb-log-appended-home-byte-slice (segment (list target (cadr (fn-lb-log-model-segment target log)) (caddr (fn-lb-log-model-segment target log))))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-next-prefix-length fn-cbor-octet-listp-implies-true-listp)))))

(defthm fn-lb-log-read-new-sealed-entry-interval
 (implies (and (fn-cat-rowp row) (fn-cbor-octet-listp payload))
 (equal (fn-lb-log-model-read-range target (len (cadr (fn-lb-log-model-segment target log))) (+ (len (fn-lb-log-model-next-prefix row payload)) 32)
         (fn-lb-log-model-append row payload target log)) (append (fn-lb-log-model-next-prefix row payload) (fn-blake3-stobj (fn-lb-log-model-next-prefix row payload)))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-read-appended-interval (off (len (cadr (fn-lb-log-model-segment target log)))) (count (+ (len (fn-lb-log-model-next-prefix row payload)) 32)))
       (:instance fn-lb-log-appended-entry-byte-slice (segment (list target (cadr (fn-lb-log-model-segment target log)) (caddr (fn-lb-log-model-segment target log))))))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-next-prefix-length fn-cbor-octet-listp-implies-true-listp)))))
