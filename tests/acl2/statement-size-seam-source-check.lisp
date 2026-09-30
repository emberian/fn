(in-package "ACL2")
(include-book "../../books/statement-codec")
(encapsulate
  (((fn-stmt-encode-items *) => *
    :formals (items) :guard (fn-stmt-item-listp items))
   ((fn-stmt-decode-items-bounded * * * *) => *
    :formals (fuel octets outer-budget item-budget)
    :guard (and (natp fuel) (natp outer-budget) (natp item-budget)))
   ((fn-stmt-decode-items-sized-bounded * * * *) => (mv * *)
    :formals (fuel octets outer-budget item-budget)
    :guard (and (natp fuel) (natp outer-budget) (natp item-budget)))
   ((fn-stmt-decode-prefix-items-bounded * * * *) => *
    :formals (count octets outer-budget item-budget)
    :guard (and (natp count) (natp outer-budget) (natp item-budget))))

  (local (value-triple :implementation-already-loaded))

  (local (defun fn-stmt-encode-items (items)
           (declare (xargs :guard (fn-stmt-item-listp items)))
           (fn-stmt-encode-items-impl items)))

  (local (defun fn-stmt-decode-items-bounded (fuel octets outer-budget item-budget)
           (declare (xargs :guard (and (natp fuel) (natp outer-budget)
                                       (natp item-budget))))
           (fn-stmt-decode-items-bounded-impl fuel octets outer-budget item-budget)))

  (local (defun fn-stmt-decode-items-sized-bounded (fuel octets outer-budget item-budget)
           (declare (xargs :guard (and (natp fuel) (natp outer-budget)
                                       (natp item-budget))))
           (fn-stmt-decode-items-sized-bounded-impl fuel octets outer-budget item-budget)))

  (defthm fn-stmt-sized-result-is-existing
    (equal (mv-nth 0 (fn-stmt-decode-items-sized-bounded
                      fuel octets outer-budget item-budget))
           (fn-stmt-decode-items-bounded fuel octets outer-budget item-budget))
    :rule-classes nil
    :hints (("Goal" :use fn-stmt-sized-bounded-projection-by-definition)))

  (defthm fn-stmt-sized-lengths-correspond
    (implies (fn-stmt-okp
              (mv-nth 0 (fn-stmt-decode-items-sized-bounded
                         fuel octets outer-budget item-budget)))
             (fn-stmt-item-sizes-correspondsp
              (fn-stmt-value
               (mv-nth 0 (fn-stmt-decode-items-sized-bounded
                          fuel octets outer-budget item-budget)))
              (mv-nth 1 (fn-stmt-decode-items-sized-bounded
                         fuel octets outer-budget item-budget))))
    :hints (("Goal" :use fn-stmt-sized-bounded-lengths-correspond)))

  (local (defun fn-stmt-decode-prefix-items-bounded (count octets outer-budget item-budget)
           (declare (xargs :guard (and (natp count) (natp outer-budget)
                                       (natp item-budget))))
           (fn-stmt-decode-prefix-items-bounded-impl count octets outer-budget
                                                     item-budget)))

  (defthm fn-stmt-encode-items-of-atom
    (implies (not (consp items))
             (equal (fn-stmt-encode-items items) nil))
    :hints (("Goal" :use fn-stmt-impl-encode-items-of-atom)))

  (defthm fn-stmt-encode-items-of-cons
    (equal (fn-stmt-encode-items (cons item items))
           (append (fn-cbor-encode item) (fn-stmt-encode-items items)))
    :hints (("Goal" :use fn-stmt-impl-encode-items-of-cons)))

  (defthm fn-stmt-decode-items-bounded-of-encode
    (implies (and (fn-stmt-item-listp items)
                  (natp fuel)
                  (<= (len items) fuel)
                  (<= (len (fn-stmt-encode-items items)) *fn-cbor-max-input*))
             (equal (fn-stmt-decode-items-bounded
                     fuel (fn-stmt-encode-items items)
                     *fn-cbor-max-input* *fn-cbor-max-bytes*)
                    (fn-stmt-ok items)))
    :hints (("Goal" :use fn-stmt-impl-decode-items-bounded-of-encode)))

  (defthm fn-stmt-decode-items-bounded-canonical
    (implies (fn-stmt-okp (fn-stmt-decode-items-bounded
                           fuel octets *fn-cbor-max-input* *fn-cbor-max-bytes*))
             (equal (fn-stmt-encode-items
                     (fn-stmt-value (fn-stmt-decode-items-bounded
                                     fuel octets
                                     *fn-cbor-max-input* *fn-cbor-max-bytes*)))
                    octets))
    :hints (("Goal" :use fn-stmt-impl-decode-items-bounded-canonical)))

  (defthm fn-stmt-decode-items-bounded-items
    (implies (fn-stmt-okp (fn-stmt-decode-items-bounded
                           fuel octets *fn-cbor-max-input* *fn-cbor-max-bytes*))
             (fn-stmt-item-listp
              (fn-stmt-value (fn-stmt-decode-items-bounded
                              fuel octets
                              *fn-cbor-max-input* *fn-cbor-max-bytes*))))
    :hints (("Goal" :use fn-stmt-impl-decode-items-bounded-items))))
(defun fn-stmt-decode-items (fuel octets)
  (declare (xargs :guard (natp fuel)))
  (fn-stmt-decode-items-bounded fuel octets
                                *fn-cbor-max-input* *fn-cbor-max-bytes*))
(defthm fn-stmt-encode-items-when-consp
  (implies (consp items)
           (equal (fn-stmt-encode-items items)
                  (append (fn-cbor-encode (car items))
                          (fn-stmt-encode-items (cdr items)))))
  :hints (("Goal" :use ((:instance fn-stmt-encode-items-of-cons
                                   (item (car items)) (items (cdr items))))
           :in-theory (disable fn-stmt-encode-items-of-cons))))
(local (in-theory (enable fn-cbor-invariants-vocabulary
                          fn-record-invariants-vocabulary)))
(defthm fn-stmt-encode-items-is-octet-list
  (fn-cbor-octet-listp (fn-stmt-encode-items items))
  :hints (("Goal" :induct (len items))))
(defthm fn-stmt-encode-items-is-true-list
  (true-listp (fn-stmt-encode-items items))
  :hints (("Goal" :induct (len items))))
(defthm fn-stmt-encode-items-of-append
  (equal (fn-stmt-encode-items (append a b))
         (append (fn-stmt-encode-items a) (fn-stmt-encode-items b)))
  :hints (("Goal" :induct (len a))))
(local (in-theory (disable fn-cbor-invariants-vocabulary
                           fn-record-invariants-vocabulary)))
(in-theory (disable fn-stmt-encode-items-when-consp))
(defthm fn-stmt-decode-items-of-encode-items
  (implies (and (fn-stmt-item-listp items)
                (natp fuel)
                (<= (len items) fuel)
                (<= (len (fn-stmt-encode-items items)) *fn-cbor-max-input*))
           (equal (fn-stmt-decode-items fuel (fn-stmt-encode-items items))
                  (fn-stmt-ok items)))
  :hints (("Goal" :use fn-stmt-decode-items-bounded-of-encode
           :in-theory (e/d (fn-stmt-decode-items)
                           (fn-stmt-decode-items-bounded-of-encode
                            fn-stmt-encode-items-when-consp)))))
(defthm fn-stmt-encode-items-of-decode-items
  (implies (fn-stmt-okp (fn-stmt-decode-items fuel octets))
           (equal (fn-stmt-encode-items
                   (fn-stmt-value (fn-stmt-decode-items fuel octets)))
                  octets))
  :hints (("Goal" :use fn-stmt-decode-items-bounded-canonical
           :in-theory (e/d (fn-stmt-decode-items)
                           (fn-stmt-decode-items-bounded-canonical
                            fn-stmt-encode-items-when-consp)))))
(defthm fn-stmt-decode-items-value-is-item-list
  (implies (fn-stmt-okp (fn-stmt-decode-items fuel octets))
           (fn-stmt-item-listp
            (fn-stmt-value (fn-stmt-decode-items fuel octets))))
  :hints (("Goal" :use fn-stmt-decode-items-bounded-items
           :in-theory (e/d (fn-stmt-decode-items)
                           (fn-stmt-decode-items-bounded-items)))))
(defattach (fn-stmt-encode-items fn-stmt-encode-items-impl)
           (fn-stmt-decode-items-bounded fn-stmt-decode-items-bounded-impl)
           (fn-stmt-decode-items-sized-bounded
            fn-stmt-decode-items-sized-bounded-impl)
           (fn-stmt-decode-prefix-items-bounded
            fn-stmt-decode-prefix-items-bounded-impl)
           :hints (("Goal"
                    :use (fn-stmt-impl-encode-items-of-atom
                          fn-stmt-impl-encode-items-of-cons
                          fn-stmt-impl-decode-items-bounded-of-encode
                          fn-stmt-impl-decode-items-bounded-canonical
                          fn-stmt-impl-decode-items-bounded-items
                          fn-stmt-sized-bounded-projection-by-definition
                          fn-stmt-sized-bounded-lengths-correspond)
                    :in-theory (theory 'minimal-theory))))
