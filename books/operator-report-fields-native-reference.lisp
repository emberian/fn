; Literal report primitive join. Including this book requires matching NLS
; evidence; the small helper's source proof alone does not prove this join.
(in-package "ACL2")
(include-book "operator-report-fields-text")
(include-book "native-live-status-words")
(local (include-book "arithmetic-5/top" :dir :system))

(defthm fn-orf-decimal-is-nls-digits
  (implies (posp n)
           (equal (fn-orf-decimal n acc) (fn-nls-digits n acc)))
  :hints (("Goal" :induct (fn-orf-decimal n acc)
           :in-theory (disable (:definition fn-orf-decimal) fn-nls-digits floor mod)
           :expand ((fn-orf-decimal n acc) (fn-nls-digits n acc)
                    (fn-nls-digits 0 (cons (+ 48 n) acc))))))

(defthm fn-orf-nat-reference-is-nls-nat
  (implies (natp n)
           (equal (fn-orf-decimal n nil) (fn-nls-nat n)))
  :hints (("Goal" :in-theory (disable fn-orf-decimal fn-nls-digits))))

(defthm fn-orf-text-reference-is-nls-text
  (implies (stringp text)
           (equal (fn-orf-text-tail text 0) (fn-nls-text text)))
  :hints (("Goal" :in-theory (disable fn-orf-text-tail
                                     fn-record-string-octets))))

(local (defthm fn-orf-nls-digits-listp
  (implies (true-listp acc) (true-listp (fn-nls-digits n acc)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-nls-digits n acc)
           :in-theory (disable floor mod)))))
(local (defthm fn-orf-nls-nat-listp
  (true-listp (fn-nls-nat n)) :rule-classes :type-prescription))

(defun fn-orf-nls-reference (fields)
  (declare (xargs :guard (fn-orf-fieldsp fields)
                  :guard-hints (("Goal" :in-theory (disable fn-nls-digits
                                                           fn-nls-nat)))))
  (if (consp fields)
      (append (if (eq (caar fields) :text)
                  (fn-nls-text (cadar fields)) (fn-nls-nat (cadar fields)))
              (fn-orf-nls-reference (cdr fields)))
    nil))

(defthm fn-orf-reference-is-nls-reference
  (implies (fn-orf-fieldsp fields)
           (equal (fn-orf-reference fields) (fn-orf-nls-reference fields)))
  :hints (("Goal" :induct (fn-orf-reference fields)
           :in-theory (disable fn-orf-decimal fn-orf-text-tail
                               fn-nls-nat fn-nls-text))))

(defthm fn-orf-complete-output-is-nls-reference
  (implies (fn-orf-fieldsp fields)
           (equal (fn-orf-run (fn-orf-start fields))
                  (fn-orf-nls-reference fields)))
  :hints (("Goal" :in-theory (disable fn-orf-run fn-orf-start
                                     fn-orf-nls-reference fn-orf-reference))))
