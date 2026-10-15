; Logical octet views of the actual native paged pools, with read/effect refinements.
; STRIP-CARS is a proof-only view of each one-field record store; served reads
; use the native accessors. A bounded old span is unchanged by pool append.
(in-package "ACL2")
(include-book "catalog-columns-pool-properties")

(local (defthm fn-lbpm-len-strip-cars
 (equal (len (strip-cars xs)) (len xs))
 :hints (("Goal" :induct (len xs) :in-theory (enable strip-cars len)))))

(local (defthm fn-lbpm-nth-strip-cars
 (equal (nth i (strip-cars xs)) (car (nth i xs)))
 :hints (("Goal" :induct (nth i xs) :in-theory (enable strip-cars nth)))))

(local (defthm fn-lbpm-strip-cars-append
 (equal (strip-cars (append xs ys)) (append (strip-cars xs) (strip-cars ys)))
 :hints (("Goal" :induct (len xs) :in-theory (enable strip-cars binary-append)))))

(local (defthm fn-lbpm-nth-when-too-large
 (implies (and (natp i) (<= (len xs) i)) (equal (nth i xs) nil))
 :hints (("Goal" :induct (nth i xs) :in-theory (enable nth len)))))

(local (defthm fn-lbpm-nth-zero-by-definition
 (equal (nth 0 xs) (car xs)) :hints (("Goal" :in-theory (enable nth)))))

(local (defthm fn-lbpm-append-associative
 (equal (append (append xs ys) zs) (append xs (append ys zs)))
 :hints (("Goal" :induct (len xs) :in-theory (enable binary-append)))))

(defun-nx fn-lbc-msgid-pool-model (fn-lbc)
 (strip-cars (nth *fn-lbc-msgid-store* fn-lbc)))

(defthm fn-lbc-msgid-pool-count-is-model-length
 (equal (fn-lbc-msgid-pool-count fn-lbc) (len (fn-lbc-msgid-pool-model fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-msgid-pool-count fn-lbc-msgid-pool-model fn-lbc-msgid-store fn-lbc-msgid-octets-count-is-len fn-lbpm-len-strip-cars)))))

(defthm fn-lbc-msgid-pool-octet-is-model-nth
 (equal (fn-lbc-msgid-pool-octet i fn-lbc)
        (if (natp i) (nth i (fn-lbc-msgid-pool-model fn-lbc)) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-msgid-pool-octet fn-lbc-msgid-pool-model fn-lbc-msgid-store fn-lbc-msgid-pool-count fn-lbc-msgid-octets-count-is-len
     fn-lbc-msgid-octets-get-octet fn-lbc-msgid-octets$a-get-octet
     fn-lbpm-nth-strip-cars fn-lbpm-nth-zero-by-definition fn-lbpm-nth-when-too-large)))))

(local (defthm fn-lbpm-msgid-model-of-store-update
 (equal (fn-lbc-msgid-pool-model (update-fn-lbc-msgid-store value fn-lbc)) (strip-cars value))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-msgid-pool-model update-fn-lbc-msgid-store nth fn-dm-nth-update-nth))))))

(defthm fn-lbc-msgid-pool-append-is-model-append
 (equal (fn-lbc-msgid-pool-model (fn-lbc-msgid-pool-append bytes fn-lbc))
        (append (fn-lbc-msgid-pool-model fn-lbc) (true-list-fix bytes)))
 :hints (("Goal" :induct (fn-lbc-msgid-pool-append bytes fn-lbc) :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-msgid-pool-append fn-lbc-msgid-pool-model fn-lbc-msgid-store update-fn-lbc-msgid-store nth fn-dm-nth-update-nth
     fn-lbc-msgid-octets-append-is-append fn-lbpm-strip-cars-append
     fn-lbpm-append-associative strip-cars true-list-fix binary-append)))))

(defun-nx fn-lbc-overview-pool-model (fn-lbc)
 (strip-cars (nth *fn-lbc-overview-store* fn-lbc)))

(defthm fn-lbc-overview-pool-count-is-model-length
 (equal (fn-lbc-overview-pool-count fn-lbc) (len (fn-lbc-overview-pool-model fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-overview-pool-count fn-lbc-overview-pool-model fn-lbc-overview-store fn-lbc-overview-octets-count-is-len fn-lbpm-len-strip-cars)))))

(defthm fn-lbc-overview-pool-octet-is-model-nth
 (equal (fn-lbc-overview-pool-octet i fn-lbc)
        (if (natp i) (nth i (fn-lbc-overview-pool-model fn-lbc)) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-overview-pool-octet fn-lbc-overview-pool-model fn-lbc-overview-store fn-lbc-overview-pool-count fn-lbc-overview-octets-count-is-len
     fn-lbc-overview-octets-get-octet fn-lbc-overview-octets$a-get-octet
     fn-lbpm-nth-strip-cars fn-lbpm-nth-zero-by-definition fn-lbpm-nth-when-too-large)))))

(local (defthm fn-lbpm-overview-model-of-store-update
 (equal (fn-lbc-overview-pool-model (update-fn-lbc-overview-store value fn-lbc)) (strip-cars value))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-overview-pool-model update-fn-lbc-overview-store nth fn-dm-nth-update-nth))))))

(defthm fn-lbc-overview-pool-append-is-model-append
 (equal (fn-lbc-overview-pool-model (fn-lbc-overview-pool-append bytes fn-lbc))
        (append (fn-lbc-overview-pool-model fn-lbc) (true-list-fix bytes)))
 :hints (("Goal" :induct (fn-lbc-overview-pool-append bytes fn-lbc) :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-overview-pool-append fn-lbc-overview-pool-model fn-lbc-overview-store update-fn-lbc-overview-store nth fn-dm-nth-update-nth
     fn-lbc-overview-octets-append-is-append fn-lbpm-strip-cars-append
     fn-lbpm-append-associative strip-cars true-list-fix binary-append)))))

(local (defthm fn-lbpm-nth-append-prefix
 (implies (and (natp i) (< i (len xs)))
          (equal (nth i (append xs ys)) (nth i xs)))
 :hints (("Goal" :induct (nth i xs) :in-theory (enable nth binary-append len)))))

(defthm fn-lbc-msgid-pool-count-natural
 (natp (fn-lbc-msgid-pool-count fn-lbc)) :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-msgid-pool-count-is-model-length)))))

(defthm fn-lbc-msgid-pool-octet-of-append-prefix
 (implies (and (natp i) (< i (fn-lbc-msgid-pool-count fn-lbc)))
          (equal (fn-lbc-msgid-pool-octet i (fn-lbc-msgid-pool-append bytes fn-lbc)) (fn-lbc-msgid-pool-octet i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-msgid-pool-octet-is-model-nth fn-lbc-msgid-pool-append-is-model-append fn-lbc-msgid-pool-count-is-model-length
     fn-lbpm-nth-append-prefix)))))

(defthm fn-lbc-msgid-pool-range-of-append-prefix
 (implies (and (natp off) (natp n) (<= (+ off n) (fn-lbc-msgid-pool-count fn-lbc)))
          (equal (fn-lbc-msgid-pool-range off n (fn-lbc-msgid-pool-append bytes fn-lbc)) (fn-lbc-msgid-pool-range off n fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-msgid-pool-range off n fn-lbc) :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-msgid-pool-range fn-lbc-msgid-pool-octet-of-append-prefix fn-lbc-msgid-pool-count-of-append
     (:type-prescription fn-lbc-msgid-pool-count-natural))))))

(defthm fn-lbc-overview-pool-count-natural
 (natp (fn-lbc-overview-pool-count fn-lbc)) :rule-classes :type-prescription
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-overview-pool-count-is-model-length)))))

(defthm fn-lbc-overview-pool-octet-of-append-prefix
 (implies (and (natp i) (< i (fn-lbc-overview-pool-count fn-lbc)))
          (equal (fn-lbc-overview-pool-octet i (fn-lbc-overview-pool-append bytes fn-lbc)) (fn-lbc-overview-pool-octet i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-overview-pool-octet-is-model-nth fn-lbc-overview-pool-append-is-model-append fn-lbc-overview-pool-count-is-model-length
     fn-lbpm-nth-append-prefix)))))

(defthm fn-lbc-overview-pool-range-of-append-prefix
 (implies (and (natp off) (natp n) (<= (+ off n) (fn-lbc-overview-pool-count fn-lbc)))
          (equal (fn-lbc-overview-pool-range off n (fn-lbc-overview-pool-append bytes fn-lbc)) (fn-lbc-overview-pool-range off n fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-overview-pool-range off n fn-lbc) :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-overview-pool-range fn-lbc-overview-pool-octet-of-append-prefix fn-lbc-overview-pool-count-of-append
     (:type-prescription fn-lbc-overview-pool-count-natural))))))

(local (defthm fn-lbpm-strip-cars-true-listp
 (true-listp (strip-cars xs)) :rule-classes :type-prescription
 :hints (("Goal" :induct (len xs) :in-theory (enable strip-cars true-listp)))))

(defthm fn-lbc-msgid-pool-model-true-listp
 (true-listp (fn-lbc-msgid-pool-model fn-lbc)) :rule-classes :type-prescription
 :hints (("Goal" :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-msgid-pool-model (:type-prescription fn-lbpm-strip-cars-true-listp))))))

(defthm fn-lbc-overview-pool-model-true-listp
 (true-listp (fn-lbc-overview-pool-model fn-lbc)) :rule-classes :type-prescription
 :hints (("Goal" :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-overview-pool-model (:type-prescription fn-lbpm-strip-cars-true-listp))))))
