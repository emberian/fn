; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-membership-run-readback")

(defthm fn-lbc-group-name-has-native-text-type
 (implies (fn-record-group-namep text) (fn-lbc-text-smallp text))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-record-group-namep fn-record-ascii-stringp fn-lbc-text-smallp fn-record-ascii-implies-octets)))))

(defthm fn-lbc-group-list-has-native-text-type
 (implies (fn-record-group-listp texts) (fn-lb-column-text-listp texts))
 :hints (("Goal" :induct (fn-record-group-listp texts)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-record-group-listp fn-lb-column-text-listp fn-lbc-group-name-has-native-text-type)))))

(defthm fn-lbc-row-groups-have-native-text-type
 (implies (fn-cat-rowp row) (fn-lb-column-text-listp (fn-record-groups row)))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-cat-rowp fn-record-groups-validp fn-record-groupsp
     fn-held-accessors-are-the-wire-accessors fn-lbc-group-list-has-native-text-type)))))
