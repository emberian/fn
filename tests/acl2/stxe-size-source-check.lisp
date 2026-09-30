(in-package "ACL2")
(include-book "../../books/defrecord")
(include-book "../../books/acceptance-alloc")
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

(defun fn-stmt-uint-item-p (x)
  (declare (xargs :guard t))
  (and (consp x)
       (equal (car x) :uint)
       (fn-record-uint32p (cdr x))))

(defun fn-stmt-bytes-item-p (x)
  (declare (xargs :guard t))
  (and (consp x)
       (equal (car x) :bytes)
       (fn-cbor-octet-listp (cdr x))))

(defconst *fn-stx-verdicts* '(:verified :unverified :absent :carried :revoked))

(defconst *fn-stxe-magic* '(102 110 45 101))

(defconst *fn-stxe-version* 0)

(defconst *fn-stxe-kind* 2)

(defconst *fn-stxe-max-octets* 65538)

(defconst *fn-stxe-max-profile* 64)

(defconst *fn-stxe-max-detail* 8192)

(defun fn-stxe-tokenp (x)
  (declare (xargs :guard t))
  (member-equal x *fn-stx-verdicts*))

(defun fn-stxe-token-code (x)
  (declare (xargs :guard t))
  (cond ((equal x :verified) 1)
        ((equal x :unverified) 2)
        ((equal x :absent) 3)
        ((equal x :carried) 4)
        ((equal x :revoked) 5)
        (t 0)))

(defun fn-stxe-code-token (x)
  (declare (xargs :guard t))
  (cond ((equal x 1) :verified)
        ((equal x 2) :unverified)
        ((equal x 3) :absent)
        ((equal x 4) :carried)
        ((equal x 5) :revoked)
        (t nil)))

(defun fn-stxe-bounded-octetsp (x bound)
  (declare (xargs :guard (natp bound)))
  (and (fn-cbor-octet-listp x) (consp x) (<= (len x) bound)))

(fn-defrecord fn-stxe
  :constructor (fn-stxe-make sequence txid generation msgid token detail
                             keyring-generation profile)
  :fields ((fn-stxe-sequence fn-record-uint32p)
           (fn-stxe-txid fn-record-uint32p)
           (fn-stxe-generation fn-record-uint32p)
           (fn-stxe-msgid fn-record-msgidp)
           (fn-stxe-token fn-stxe-tokenp)
           (fn-stxe-detail
            (fn-stxe-bounded-octetsp (fn-stxe-detail x)
                                     *fn-stxe-max-detail*))
           (fn-stxe-keyring-generation fn-record-uint32p)
           (fn-stxe-profile
            (fn-stxe-bounded-octetsp (fn-stxe-profile x)
                                     *fn-stxe-max-profile*)))
  :recognizer fn-stxe-p)

(defun fn-stxe-items-p (items)
  (declare (xargs :guard t))
  (and (true-listp items) (equal (len items) 11)
       (fn-stmt-bytes-item-p (nth 0 items))
       (equal (fn-cbor-ag-cdr (nth 0 items)) *fn-stxe-magic*)
       (fn-stmt-uint-item-p (nth 1 items))
       (equal (fn-cbor-ag-cdr (nth 1 items)) *fn-stxe-version*)
       (fn-stmt-uint-item-p (nth 2 items))
       (equal (fn-cbor-ag-cdr (nth 2 items)) *fn-stxe-kind*)
       (fn-stmt-uint-item-p (nth 3 items))
       (fn-stmt-uint-item-p (nth 4 items))
       (fn-stmt-uint-item-p (nth 5 items))
       (fn-stmt-bytes-item-p (nth 6 items))
       (fn-record-msgidp (fn-record-octets-string (fn-cbor-ag-cdr (nth 6 items))))
       (fn-stmt-uint-item-p (nth 7 items))
       (fn-stxe-tokenp (fn-stxe-code-token (fn-cbor-ag-cdr (nth 7 items))))
       (fn-stmt-bytes-item-p (nth 8 items))
       (fn-stxe-bounded-octetsp (fn-cbor-ag-cdr (nth 8 items)) *fn-stxe-max-detail*)
       (fn-stmt-uint-item-p (nth 9 items))
       (fn-stmt-bytes-item-p (nth 10 items))
       (fn-stxe-bounded-octetsp (fn-cbor-ag-cdr (nth 10 items)) *fn-stxe-max-profile*)))

(defun fn-stxe-of-items (items)
  (declare (xargs :guard t))
  (if (not (fn-stxe-items-p items))
      (fn-stmt-error :statement-verdict)
    (fn-stmt-ok
     (fn-stxe-make (fn-cbor-ag-cdr (nth 3 items))
                   (fn-cbor-ag-cdr (nth 4 items))
                   (fn-cbor-ag-cdr (nth 5 items))
                   (fn-record-octets-string (fn-cbor-ag-cdr (nth 6 items)))
                   (fn-stxe-code-token (fn-cbor-ag-cdr (nth 7 items)))
                   (fn-cbor-ag-cdr (nth 8 items))
                   (fn-cbor-ag-cdr (nth 9 items))
                   (fn-cbor-ag-cdr (nth 10 items))))))

(defun fn-stxe-size-at (n sizes)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (consp sizes)
      (if (zp n) (car sizes) (fn-stxe-size-at (1- n) (cdr sizes)))
    nil))

(defun fn-stxe-decode-exact-sized (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-at-mostp octets *fn-stxe-max-octets*))
      (mv (fn-stmt-error :limit) nil)
    (mv-let (decoded sizes)
      (fn-stmt-decode-items-sized-bounded
       11 octets *fn-cbor-max-input* *fn-cbor-max-bytes*)
      (if (not (fn-stmt-okp decoded))
          (mv decoded nil)
        (let ((result (fn-stxe-of-items (fn-stmt-value decoded))))
          (mv result
              (if (fn-stmt-okp result)
                  (list (fn-stxe-size-at 6 sizes)
                        (fn-stxe-size-at 8 sizes)
                        (fn-stxe-size-at 10 sizes))
                nil)))))))

(defun fn-stxe-decode-exact (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-at-mostp octets *fn-stxe-max-octets*))
      (fn-stmt-error :limit)
    (let ((decoded (fn-stmt-decode-items 11 octets)))
      (if (not (fn-stmt-okp decoded))
          decoded
        (fn-stxe-of-items (fn-stmt-value decoded))))))

(defthm fn-stxe-sized-result-is-existing-by-definition
  (equal (mv-nth 0 (fn-stxe-decode-exact-sized octets))
         (fn-stxe-decode-exact octets))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-stmt-sized-result-is-existing
                            (fuel 11) (outer-budget *fn-cbor-max-input*)
                            (item-budget *fn-cbor-max-bytes*)))
           :in-theory (e/d (fn-stxe-decode-exact-sized fn-stxe-decode-exact
                            fn-stmt-decode-items)
                           (fn-stxe-of-items
                            fn-stmt-okp fn-stmt-value fn-cbor-at-mostp)))))

(local (defun fn-stxe-provenance-induct (n items sizes)
 (if (or (zp n) (atom items)) (list items sizes)
  (fn-stxe-provenance-induct (1- n) (cdr items) (if (consp sizes) (cdr sizes) nil)))))

(local (defthm fn-stxe-provenance-at
 (implies (and (natp n) (fn-stmt-item-sizes-correspondsp items sizes))
  (equal (fn-stxe-size-at n sizes)
         (if (equal (car (nth n items)) :bytes) (len (cdr (nth n items))) nil)))
 :hints (("Goal" :induct (fn-stxe-provenance-induct n items sizes)
          :in-theory (enable fn-stxe-provenance-induct fn-stxe-size-at
                             fn-stmt-item-sizes-correspondsp nth)))))

(local (defthm fn-stxe-octet-chars-length
 (equal (len (fn-record-octets-chars xs)) (len xs))
 :hints (("Goal" :in-theory (enable fn-record-octets-chars)))))

(local (defthm fn-stxe-octet-chars-characters
 (character-listp (fn-record-octets-chars xs))
 :hints (("Goal" :in-theory (enable fn-record-octets-chars)))))

(local (defthm fn-stxe-octets-string-length
 (implies (fn-cbor-octet-listp xs)
          (equal (length (fn-record-octets-string xs)) (len xs)))
 :hints (("Goal" :in-theory (e/d (fn-record-octets-string length)
                                (fn-record-octets-chars))))))

(defthm fn-stxe-sized-byte-lengths-correspond
 (implies (fn-stmt-okp (mv-nth 0 (fn-stxe-decode-exact-sized octets)))
  (equal (mv-nth 1 (fn-stxe-decode-exact-sized octets))
         (let ((e (fn-stmt-value (mv-nth 0 (fn-stxe-decode-exact-sized octets)))))
           (list (length (fn-stxe-msgid e))
                 (len (fn-stxe-detail e)) (len (fn-stxe-profile e))))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-stmt-sized-lengths-correspond
                          (fuel 11) (outer-budget *fn-cbor-max-input*)
                          (item-budget *fn-cbor-max-bytes*)))
          :in-theory (e/d (fn-stxe-decode-exact-sized fn-stxe-of-items
                            fn-stxe-items-p fn-stxe-make fn-stxe-msgid
                            fn-stxe-detail fn-stxe-profile fn-stmt-ok fn-stmt-okp
                            fn-stmt-value fn-stmt-bytes-item-p fn-cbor-ag-cdr)
                           (fn-record-octets-string fn-stxe-size-at
                            fn-stmt-item-sizes-correspondsp
                            fn-cbor-octet-listp fn-cbor-at-mostp)))))

(defun fn-stxe-items (e)
  (declare (xargs :guard (fn-stxe-p e)))
  (list (cons :bytes *fn-stxe-magic*)
        (cons :uint *fn-stxe-version*)
        (cons :uint *fn-stxe-kind*)
        (cons :uint (fn-stxe-sequence e))
        (cons :uint (fn-stxe-txid e))
        (cons :uint (fn-stxe-generation e))
        (cons :bytes (fn-record-string-octets (fn-stxe-msgid e)))
        (cons :uint (fn-stxe-token-code (fn-stxe-token e)))
        (cons :bytes (fn-stxe-detail e))
        (cons :uint (fn-stxe-keyring-generation e))
        (cons :bytes (fn-stxe-profile e))))
(assert-event
 (let* ((e (fn-stxe-make 1 2 3 "<a@b>" :carried '(7 8) 4 '(9)))
        (bytes (fn-stmt-encode-items (fn-stxe-items e)))
        (result (mv-list 2 (fn-stxe-decode-exact-sized bytes))))
  (and (equal (car result) (fn-stxe-decode-exact bytes))
       (equal (car result) (fn-stmt-ok e))
       (equal (cadr result) '(5 2 1)))))
(assert-event
 (let ((result (mv-list 2 (fn-stxe-decode-exact-sized '(66 7)))))
  (and (not (fn-stmt-okp (car result))) (null (cadr result)))))
