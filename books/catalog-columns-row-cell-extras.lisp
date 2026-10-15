; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-array-count-properties")

(local (defthm fn-lbrce-alist-pair-cons
 (equal (alistp (cons (cons key value) rest)) (alistp rest))
 :hints (("Goal" :in-theory (enable alistp)))))

(local (defthm fn-lbrce-assoc-nil
 (equal (assoc-eq key nil) nil)
 :hints (("Goal" :in-theory (enable assoc-eq)))))

(defthm fn-lbc-row-cell-extra-nov
 (equal (assoc-eq :nov (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small)) (if (and (fn-hf-nov (fn-held-facts row)) (not nov-small)) (cons :nov (fn-hf-nov (fn-held-facts row))) nil))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-absent-key (key :nov) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge :msgid-offset :msgid-length :withdrawal-at :withdrawal-by :overview-offset :sequence :facts-octets :body-start :body-lines :nov-start :render-nov-start :groups-start :groups-count :numbers-start :numbers-count :raw-head-length))
    (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrce-alist-pair-cons fn-lbrce-assoc-nil car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart alistp) (:executable-counterpart assoc-equal) (:executable-counterpart member-equal))))))

(defthm fn-lbc-row-cell-extra-render-nov
 (equal (assoc-eq :render-nov (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small)) (if render-small nil (cons :render-nov render-nov)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-absent-key (key :render-nov) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge :msgid-offset :msgid-length :withdrawal-at :withdrawal-by :overview-offset :sequence :facts-octets :body-start :body-lines :nov-start :render-nov-start :groups-start :groups-count :numbers-start :numbers-count :raw-head-length))
    (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrce-alist-pair-cons fn-lbrce-assoc-nil car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart alistp) (:executable-counterpart assoc-equal) (:executable-counterpart member-equal))))))

(defthm fn-lbc-row-cell-extra-groups
 (equal (assoc-eq :groups (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small)) (if groups-small nil (cons :groups (fn-record-groups row))))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-absent-key (key :groups) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge :msgid-offset :msgid-length :withdrawal-at :withdrawal-by :overview-offset :sequence :facts-octets :body-start :body-lines :nov-start :render-nov-start :groups-start :groups-count :numbers-start :numbers-count :raw-head-length))
    (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrce-alist-pair-cons fn-lbrce-assoc-nil car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart alistp) (:executable-counterpart assoc-equal) (:executable-counterpart member-equal))))))

(defthm fn-lbc-row-cell-extra-numbers
 (equal (assoc-eq :numbers (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small)) (if numbers-small nil (cons :numbers (fn-held-numbers row))))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-absent-key (key :numbers) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge :msgid-offset :msgid-length :withdrawal-at :withdrawal-by :overview-offset :sequence :facts-octets :body-start :body-lines :nov-start :render-nov-start :groups-start :groups-count :numbers-start :numbers-count :raw-head-length))
    (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrce-alist-pair-cons fn-lbrce-assoc-nil car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart alistp) (:executable-counterpart assoc-equal) (:executable-counterpart member-equal))))))

(defthm fn-lbc-row-cell-extra-xref-body-prefix
 (equal (assoc-eq :xref-body-prefix (fn-lbc-row-escape-cell row payload render-nov head-length max-stamp msgid-offset msgid-length i nov-start render-start groups-start numbers-start raw-head-length nov-small render-small groups-small numbers-small)) (if (fn-lb-xref-shift-prefix payload) (cons :xref-body-prefix (fn-lb-xref-shift-prefix payload)) nil))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :use ((:instance fn-lbc-sparse-u64-absent-key (key :xref-body-prefix) (fields '(:handle :head-length :stamp :prefix-max :txid :generation :charge :msgid-offset :msgid-length :withdrawal-at :withdrawal-by :overview-offset :sequence :facts-octets :body-start :body-lines :nov-start :render-nov-start :groups-start :groups-count :numbers-start :numbers-count :raw-head-length))
    (values (list (fn-record-payload row) head-length (fn-record-stamp row) max-stamp (fn-record-txid row) (fn-record-generation row) (fn-record-charge row) msgid-offset msgid-length (nfix (car (fn-held-withdrawn row))) (nfix (cdr (fn-held-withdrawn row))) i (fn-record-sequence row) (fn-hf-octets (fn-held-facts row)) (nfix (fn-hf-body-start (fn-held-facts row))) (fn-hf-body-lines (fn-held-facts row)) nov-start render-start groups-start (len (fn-record-groups row)) numbers-start (len (fn-held-numbers row)) raw-head-length))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-row-escape-cell fn-lbc-assoc-eq-of-append fn-lbc-assoc-eq-of-pair-cons fn-lbc-sparse-u64-is-alist fn-lbrce-alist-pair-cons fn-lbrce-assoc-nil car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart alistp) (:executable-counterpart assoc-equal) (:executable-counterpart member-equal))))))
