; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-msgid-row-effect")

(defthm fn-lbc-msgid-pool-range-by-model
 (implies (and (natp off) (natp n))
  (equal (fn-lbc-msgid-pool-range off n fn-lbc)
   (if (<= (+ off n) (len (fn-lbc-msgid-pool-model fn-lbc)))
    (take n (nthcdr off (fn-lbc-msgid-pool-model fn-lbc))) nil)))
 :hints (("Goal" :do-not-induct t :cases ((<= (+ off n) (fn-lbc-msgid-pool-count fn-lbc)))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-msgid-pool-range fn-lbc-msgid-pool-range-is-model-slice
     fn-lbc-msgid-pool-count-is-model-length)))))

(defthm fn-lbc-msgid-pool-range-of-same-model
 (implies (and (natp off) (natp n)
               (equal (fn-lbc-msgid-pool-model new) (fn-lbc-msgid-pool-model fn-lbc)))
  (equal (fn-lbc-msgid-pool-range off n new) (fn-lbc-msgid-pool-range off n fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-msgid-pool-range-by-model)))))

(defthm fn-lbc-msgid-range-of-append-row-new
 (equal (fn-lbc-msgid-pool-range (fn-lbc-msgid-pool-count fn-lbc)
          (len (fn-record-string-octets (fn-record-msgid row)))
          (fn-lbc-append-row row log fn-lbc))
        (true-list-fix (fn-record-string-octets (fn-record-msgid row))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-msgid-pool-range-of-same-model
    (new (fn-lbc-append-row row log fn-lbc))
    (fn-lbc (fn-lbc-msgid-pool-append (fn-record-string-octets (fn-record-msgid row)) fn-lbc))
    (off (fn-lbc-msgid-pool-count fn-lbc))
    (n (len (fn-record-string-octets (fn-record-msgid row))))))
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-msgid-pool-model-of-append-row fn-lbc-msgid-pool-append-is-model-append
     fn-lbc-msgid-pool-range-of-appended-bytes
     (:type-prescription fn-lbc-msgid-pool-count-natural))))))

(defthm fn-lbc-row-msgid-has-native-text-type
 (implies (fn-cat-rowp row)
  (and (fn-lbc-text-smallp (fn-record-msgid row))
       (<= (len (fn-record-string-octets (fn-record-msgid row))) *fn-record-max-msgid*)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-cat-rowp fn-held-accessors-are-the-wire-accessors fn-record-msgidp
     fn-record-ascii-stringp fn-record-nonempty-at-mostp fn-lbc-text-smallp
     fn-record-ascii-implies-octets)))))

(local (defthm fn-lbmrid-nfix-when-natural
 (implies (natp x) (equal (nfix x) x))
 :hints (("Goal" :in-theory (enable nfix)))))

(defthm fn-lbc-msgid-of-append-row-new
 (implies (fn-cat-rowp row)
  (equal (fn-lbc-msgid (fn-lbc-count fn-lbc) (fn-lbc-append-row row log fn-lbc))
         (fn-record-msgid row)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-row-msgid-has-native-text-type))
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-msgid fn-lbc-msgid-offset-of-append-row-new fn-lbc-msgid-length-of-append-row-new
     fn-lbmrid-nfix-when-natural fn-lbc-msgid-range-of-append-row-new
     fn-lbc-small-text-byte-round-trip (:type-prescription fn-lbc-msgid-pool-count-natural)))
   '((:definition nfix) (:definition true-list-fix) (tau-system))))))
