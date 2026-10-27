; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-sparse-decoder")

(local (defthm fn-lbrec-nth-of-cons
 (equal (nth i (cons value xs))
        (if (zp i) value (nth (- (nfix i) 1) xs)))
 :hints (("Goal" :in-theory (enable nth)))))

(local (defthm fn-lbrec-alist-of-pair-cons
 (equal (alistp (cons (cons key value) rest)) (alistp rest))
 :hints (("Goal" :in-theory (enable alistp)))))

(defthm fn-lbc-row-cell-decodes-handle
 (let ((escape (assoc-eq :handle (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 (fn-record-payload row))) (fn-record-payload row)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 0) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))

(defthm fn-lbc-row-cell-decodes-head-length
 (let ((escape (assoc-eq :head-length (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 head-length)) head-length))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 1) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))

(defthm fn-lbc-row-cell-decodes-stamp
 (let ((escape (assoc-eq :stamp (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 (fn-record-stamp row))) (fn-record-stamp row)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 2) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))

(defthm fn-lbc-row-cell-decodes-prefix-max
 (let ((escape (assoc-eq :prefix-max (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 max-stamp)) max-stamp))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 3) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))

(defthm fn-lbc-row-cell-decodes-txid
 (let ((escape (assoc-eq :txid (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 (fn-record-txid row))) (fn-record-txid row)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 4) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))

(defthm fn-lbc-row-cell-decodes-generation
 (let ((escape (assoc-eq :generation (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 (fn-record-generation row))) (fn-record-generation row)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 5) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))

(defthm fn-lbc-row-cell-decodes-charge
 (let ((escape (assoc-eq :charge (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 (fn-record-charge row))) (fn-record-charge row)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 6) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))

(defthm fn-lbc-row-cell-decodes-msgid-offset
 (let ((escape (assoc-eq :msgid-offset (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 msgid-offset)) msgid-offset))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 7) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))

(defthm fn-lbc-row-cell-decodes-msgid-length
 (let ((escape (assoc-eq :msgid-length (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 msgid-length)) msgid-length))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 8) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))

(defthm fn-lbc-row-cell-decodes-withdrawal-at
 (let ((escape (assoc-eq :withdrawal-at (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 (nfix (car (fn-held-withdrawn row))))) (nfix (car (fn-held-withdrawn row)))))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 9) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))

(defthm fn-lbc-row-cell-decodes-withdrawal-by
 (let ((escape (assoc-eq :withdrawal-by (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 (nfix (cdr (fn-held-withdrawn row))))) (nfix (cdr (fn-held-withdrawn row)))))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 10) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))

(defthm fn-lbc-row-cell-decodes-overview-offset
 (let ((escape (assoc-eq :overview-offset (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 i)) i))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 11) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))

(defthm fn-lbc-row-cell-decodes-sequence
 (let ((escape (assoc-eq :sequence (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 (fn-record-sequence row))) (fn-record-sequence row)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 12) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))

(defthm fn-lbc-row-cell-decodes-facts-octets
 (let ((escape (assoc-eq :facts-octets (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 (fn-hf-octets (fn-held-facts row)))) (fn-hf-octets (fn-held-facts row))))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 13) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))

(defthm fn-lbc-row-cell-decodes-body-start
 (let ((escape (assoc-eq :body-start (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 (nfix (fn-hf-body-start (fn-held-facts row))))) (nfix (fn-hf-body-start (fn-held-facts row)))))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 14) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))

(defthm fn-lbc-row-cell-decodes-body-lines
 (let ((escape (assoc-eq :body-lines (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 (fn-hf-body-lines (fn-held-facts row)))) (fn-hf-body-lines (fn-held-facts row))))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 15) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))

(defthm fn-lbc-row-cell-decodes-nov-start
 (let ((escape (assoc-eq :nov-start (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 nov-start)) nov-start))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 16) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))

(defthm fn-lbc-row-cell-decodes-render-nov-start
 (let ((escape (assoc-eq :render-nov-start (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 render-start)) render-start))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 17) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))

(defthm fn-lbc-row-cell-decodes-groups-start
 (let ((escape (assoc-eq :groups-start (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 groups-start)) groups-start))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 18) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))

(defthm fn-lbc-row-cell-decodes-groups-count
 (let ((escape (assoc-eq :groups-count (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 (len (fn-record-groups row)))) (len (fn-record-groups row))))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 19) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))

(defthm fn-lbc-row-cell-decodes-numbers-start
 (let ((escape (assoc-eq :numbers-start (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 numbers-start)) numbers-start))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 20) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))

(defthm fn-lbc-row-cell-decodes-numbers-count
 (let ((escape (assoc-eq :numbers-count (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 (len (fn-held-numbers row)))) (len (fn-held-numbers row))))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 21) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))

(defthm fn-lbc-row-cell-decodes-raw-head-length
 (let ((escape (assoc-eq :raw-head-length (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small))))
  (equal (if escape (cdr escape) (fn-lbc-u64 raw-head-length)) raw-head-length))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-recovers-selected-value
          (k 22) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge
                 :msgid-offset :msgid-length :withdrawal-at :withdrawal-by
                 :overview-offset :sequence :facts-octets :body-start :body-lines
                 :nov-start :render-nov-start :groups-start :groups-count
                 :numbers-start :numbers-count :raw-head-length)) (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrec-alist-of-pair-cons fn-lbrec-nth-of-cons car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart no-duplicatesp-equal) (:executable-counterpart natp) (:executable-counterpart <) (:executable-counterpart len) (:executable-counterpart nth) (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart assoc-equal) (:executable-counterpart alistp))))))
