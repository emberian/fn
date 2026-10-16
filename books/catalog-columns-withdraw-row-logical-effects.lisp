; Logical row effects that match the resident withdrawal update.
(in-package "ACL2")
(include-book "catalog-columns-withdraw-row")

(defthm fn-lbcwd-logical-row-type-of-withdrawal
 (implies (and (fn-cat-rowp row) (fn-held-withdrawnp withdrawn))
  (fn-cat-rowp (fn-held-with-withdrawn row withdrawn)))
 :hints (("Goal" :do-not-induct t :in-theory (enable fn-cat-rowp fn-held-with-withdrawn))))

(defthm fn-lbcwd-logical-key-of-withdrawal-by-definition
 (and (equal (fn-record-sequence (fn-held-with-withdrawn row withdrawn)) (fn-record-sequence row))
      (equal (fn-record-payload (fn-held-with-withdrawn row withdrawn)) (fn-record-payload row))
      (equal (fn-record-msgid (fn-held-with-withdrawn row withdrawn)) (fn-record-msgid row)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-held-with-withdrawn fn-held-make fn-record-sequence fn-record-payload fn-record-msgid fn-cbor-ag-car fn-cbor-ag-cdr)))))

(defthm fn-lbcwd-logical-homes-of-withdrawal-by-definition
 (equal (fn-lb-log-model-homes (fn-held-with-withdrawn row withdrawn)) (fn-lb-log-model-homes row))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
  '(fn-lb-log-model-homes fn-held-with-withdrawn fn-held-make
    fn-record-obligation-id fn-record-content-subject fn-record-release-evidence
    fn-held-context fn-held-facts fn-cbor-ag-car fn-cbor-ag-cdr)))))

(defthm fn-lbcwd-logical-home-frame-of-withdrawal-by-definition
 (implies (and (fn-cat-rowp row) (fn-held-withdrawnp withdrawn))
  (equal (fn-lb-log-model-home-frame (fn-held-with-withdrawn row withdrawn)) (fn-lb-log-model-home-frame row)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
  '(fn-lb-log-model-home-frame fn-lbcwd-logical-row-type-of-withdrawal fn-lbcwd-logical-homes-of-withdrawal-by-definition)))))

(defthm fn-lbcwd-logical-payload-of-withdrawal-by-definition
 (equal (fn-lb-log-payload (fn-held-with-withdrawn row withdrawn) log) (fn-lb-log-payload row log))
 :hints (("Goal" :induct (fn-lb-log-model-row-entry row log)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lb-log-payload fn-lb-log-model-row-entry fn-lbcwd-logical-key-of-withdrawal-by-definition)))))

(defthm fn-lbcwd-logical-projection-of-withdrawal-by-definition
 (equal (fn-cat-served-projection (fn-held-with-withdrawn row withdrawn))
  (update-nth 5 withdrawn (fn-cat-served-projection row)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
  '(fn-cat-served-projection fn-held-with-withdrawn fn-held-make
    fn-record-msgid fn-record-payload fn-record-groups fn-held-numbers fn-record-stamp
    fn-held-withdrawn fn-held-facts fn-record-txid fn-record-generation fn-record-charge
    fn-record-sequence fn-cbor-ag-car fn-cbor-ag-cdr update-nth)))))

(defthm fn-lbcwd-logical-stamp-of-withdrawal-by-definition
 (equal (fn-record-stamp (fn-held-with-withdrawn row withdrawn)) (fn-record-stamp row))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
  '(fn-held-with-withdrawn fn-held-make fn-record-stamp fn-cbor-ag-car fn-cbor-ag-cdr)))))
