(in-package "ACL2")
(include-book "byte-store-observation")
(include-book "byte-store-scan")
(include-book "store-observed")

; A source that returned :file octets at a visible name and a target with the
; same visible entry give the decoder the same octets, regardless of inode IDs.
(defthm fn-bso-entry-agreement-preserves-file-kind
  (implies (equal (fn-bso-entry a dir name) (fn-bso-entry b dir name))
           (equal (fn-bs-inop (fn-bs-lookup a dir name))
                  (fn-bs-inop (fn-bs-lookup b dir name))))
  :hints (("Goal" :in-theory (enable fn-bso-entry))))

(defthm fn-bso-entry-agreement-preserves-file-content
  (implies (and (equal (fn-bso-entry a dir name) (fn-bso-entry b dir name))
                (fn-bs-inop (fn-bs-lookup a dir name)))
           (equal (fn-bs-content a (fn-bs-lookup a dir name))
                  (fn-bs-content b (fn-bs-lookup b dir name))))
  :hints (("Goal" :in-theory (enable fn-bso-entry))))

(defthm fn-bso-names-agree-member
  (implies (and (fn-bso-names-agree names a b dir)
                (member-equal name names))
           (equal (fn-bso-entry a dir name)
                  (fn-bso-entry b dir name)))
  :hints (("Goal" :induct (fn-bso-names-agree names a b dir))))

(defthm fn-bso-directory-agree-member
  (implies (and (fn-bso-directory-agree a b dir)
                (member-equal name (fn-bs-names a dir)))
           (equal (fn-bso-entry a dir name)
                  (fn-bso-entry b dir name)))
  :hints (("Goal" :in-theory (enable fn-bso-directory-agree))))

(defthm fn-bso-assoc-key-is-a-name
  (implies (assoc-equal key entries)
           (member-equal key (strip-cars entries))))

(defthm fn-bso-natural-value-has-assoc
  (implies (natp (cdr (assoc-equal key entries)))
           (assoc-equal key entries))
  :hints (("Goal" :cases ((assoc-equal key entries)))))

(defthm fn-bso-file-lookup-is-a-name
  (implies (fn-bs-inop (fn-bs-lookup s dir name))
           (member-equal name (fn-bs-names s dir)))
  :hints (("Goal" :in-theory (enable fn-bs-lookup fn-bs-names))))

(defthm fn-bso-directory-agreement-preserves-file-kind
  (implies (and (fn-bso-directory-agree a b dir)
                (fn-bs-inop (fn-bs-lookup a dir name)))
           (fn-bs-inop (fn-bs-lookup b dir name)))
  :hints (("Goal"
           :use ((:instance fn-bso-directory-agree-member)
                 (:instance fn-bso-file-lookup-is-a-name (s a))
                 (:instance fn-bso-entry-agreement-preserves-file-kind))
           :in-theory (disable fn-bso-directory-agree-member
                               fn-bso-file-lookup-is-a-name
                               fn-bso-entry-agreement-preserves-file-kind))))

(defthm fn-bso-directory-agreement-preserves-file-content
  (implies (and (fn-bso-directory-agree a b dir)
                (fn-bs-inop (fn-bs-lookup a dir name)))
           (equal (fn-bs-content a (fn-bs-lookup a dir name))
                  (fn-bs-content b (fn-bs-lookup b dir name))))
  :hints (("Goal"
           :use ((:instance fn-bso-directory-agree-member)
                 (:instance fn-bso-file-lookup-is-a-name (s a))
                 (:instance fn-bso-entry-agreement-preserves-file-content))
           :in-theory (disable fn-bso-directory-agree-member
                               fn-bso-file-lookup-is-a-name
                               fn-bso-entry-agreement-preserves-file-content))))

(defun fn-bso-txn-prefix-entry-agreesp (a b n count)
  (declare (xargs :guard t :verify-guards nil
                  :measure (nfix (- (nfix count) (nfix n)))))
  (if (or (not (natp n)) (not (natp count)) (>= n count))
      t
    (and (equal (fn-bso-entry a :transactions (fn-bs-txn-name n))
                (fn-bso-entry b :transactions (fn-bs-txn-name n)))
         (fn-bso-txn-prefix-entry-agreesp a b (1+ n) count))))

(defthm fn-bso-read-records-under-entry-agreement
  (implies (fn-bso-txn-prefix-entry-agreesp a b n count)
           (equal (fn-bs-read-records a n count)
                  (fn-bs-read-records b n count)))
  :hints (("Goal" :induct (fn-bso-txn-prefix-entry-agreesp a b n count)
           :in-theory (e/d (fn-bs-read-records fn-bs-record-of)
                           (fn-bs-lookup fn-bs-content fn-bs-record-of-octets)))))

(defthm fn-bso-directory-agreement-covers-canonical-prefix
  (implies (and (fn-bso-directory-agree a b :transactions)
                (equal (fn-bs-names a :transactions) (fn-bs-txn-names count))
                (natp n) (natp count))
           (fn-bso-txn-prefix-entry-agreesp a b n count))
  :hints (("Goal" :induct (fn-bso-txn-prefix-entry-agreesp a b n count)
           :in-theory (disable fn-bs-txn-names))))

(defthm fn-bso-served-agreement-has-root
  (implies (fn-bso-served-image-agree a b)
           (fn-bso-directory-agree a b :root))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable fn-bso-served-image-agree))))

(defthm fn-bso-served-agreement-has-transactions
  (implies (fn-bso-served-image-agree a b)
           (fn-bso-directory-agree a b :transactions))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable fn-bso-served-image-agree))))

; The source image is one the model can scan.  This is the intended positive
; cut domain; a malformed source can fail for a key absent from both images,
; and the visible relation does not assign a meaning to that fault code.
(defthm fn-bso-served-agreement-preserves-scan
  (implies (and (fn-bso-served-image-agree model physical)
                (equal (fn-bs-names model :transactions)
                       (fn-bs-names physical :transactions))
                (fn-bs-scan-okp (fn-bs-scan-store model)))
           (equal (fn-bs-scan-store physical)
                  (fn-bs-scan-store model)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bso-served-agreement-has-transactions
                            (a model) (b physical))
                 (:instance fn-bso-directory-agreement-covers-canonical-prefix
                            (a model) (b physical) (n 0)
                            (count (len (fn-bs-names model :transactions))))
                 (:instance fn-bso-read-records-under-entry-agreement
                            (a model) (b physical) (n 0)
                            (count (len (fn-bs-names model :transactions)))))
           :in-theory (e/d (fn-bs-scan-store fn-bs-scan-okp
                                      fn-bs-contiguous-namesp)
                                     (fn-bso-served-image-agree
                                      fn-bso-directory-agree fn-bs-inop)))))

; The served reopen consumes the scanner's frontier and record stream.  This
; is a congruence consequence of the scanner keystone, not a separate
; transition simulation theorem.
(defthm fn-bso-served-agreement-preserves-open-by-scan
  (implies (and (fn-bso-served-image-agree model physical)
                (equal (fn-bs-names model :transactions)
                       (fn-bs-names physical :transactions))
                (fn-bs-scan-okp (fn-bs-scan-store model)))
           (equal (fn-sn-open-observed
                   groups capacity
                   (fn-bs-scan-frontier (fn-bs-scan-store physical))
                   (fn-bs-scan-records (fn-bs-scan-store physical)))
                  (fn-sn-open-observed
                   groups capacity
                   (fn-bs-scan-frontier (fn-bs-scan-store model))
                   (fn-bs-scan-records (fn-bs-scan-store model)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bso-served-agreement-preserves-scan))
           :in-theory nil)))
