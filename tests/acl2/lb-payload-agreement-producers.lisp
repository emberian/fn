; Ruling 1 producer controls: actual producer values and whole rebuild correspondence.
(in-package "ACL2")
(include-book "lb-cross-kind-unlink-case")
(include-book "../../books/catalog-columns-open-catalog-correspondence")
(include-book "../../books/owner-reclaim-seal")

(local (defun fn-lbw-cross-definition-runes (runes)
 (declare (xargs :guard t))
 (if (consp runes)
  (let* ((r (car runes)) (sym (ec-call (car (ec-call (cdr r)))))
         (name (if (symbolp sym) (symbol-name sym) "")))
   (if (and (equal (ec-call (car r)) :definition)
            (or (equal (subseq name 0 (min 7 (length name))) "FN-LBC-")
                (equal (subseq name 0 (min 8 (length name))) "FN-DMAP-")
                (equal (subseq name 0 (min 14 (length name))) "UPDATE-FN-LBC-")
                (member-eq sym '(fn-lbr13-finish-single-row fn-lbw-cross-state fn-lbr1-old-corr create-fn-lbc create-fn-dmap))))
       (cons r (fn-lbw-cross-definition-runes (cdr runes)))
     (fn-lbw-cross-definition-runes (cdr runes)))) nil)))
(local (defun fn-lbw-cross-pure-runes (runes)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp runes)
  (let* ((r (car runes)) (sym (car (cdr r)))
         (name (if (symbolp sym) (symbol-name sym) "")))
   (if (and (equal (car r) :executable-counterpart)
     (not (equal (subseq name 0 (min 7 (length name))) "FN-LBC-"))
     (not (equal (subseq name 0 (min 9 (length name))) "FN-LBR13-"))
     (not (equal (subseq name 0 (min 14 (length name))) "UPDATE-FN-LBC-"))
     (not (member-eq sym '(create-fn-lbc fn-lbw-cross-state fn-lbr1-move-state fn-lbr1-old-corr
       fn-lb-retained-payloads-agreep fn-lb-log-row-copies-agreep
       fn-lb-log-entries-payload-agreep fn-lb-log-rows-sourcep fn-lb-log-row-sourcep fn-lb-log-model-next-range))))
    (cons r (fn-lbw-cross-pure-runes (cdr runes)))
    (fn-lbw-cross-pure-runes (cdr runes)))) nil)))

(defun fn-lbr1-reclaim-rows () (declare (xargs :guard t :verify-guards nil)) (car (fn-orcs-predict (fn-lbw-reclaim-input) nil 2)))
(defun fn-lbr1-reclaim-log () (declare (xargs :guard t :verify-guards nil)) (fn-lb-log-model-reclaim-events (fn-lbw-reclaim-input) nil 2 2 (fn-lbw-two-log)))
(defthm fn-lbr1-reclaim-source-positive
 (and (fn-lbc-p (create-fn-lbc)) (fn-cat-rowsp (fn-lbr1-reclaim-rows))
      (fn-lbc-rows-log-guardp (fn-lbr1-reclaim-rows) (fn-lbr1-reclaim-log))
      (fn-lb-log-layoutp (fn-lbr1-reclaim-log)) (fn-lb-log-model-segsp (fn-lbr1-reclaim-log))
      (fn-lb-log-rows-sourcep (fn-lbr1-reclaim-rows) (fn-lbr1-reclaim-log)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
  (union-theories '(fn-lbc-p create-fn-lbc create-fn-dmap
    fn-lb-log-rows-sourcep fn-lb-log-row-sourcep fn-lb-log-row-copies-agreep
    fn-lb-log-entries-payload-agreep fn-lb-log-model-next-range fn-lbc-rows-log-guardp fn-lbc-row-log-guardp)
   (union-theories (fn-lbw-cross-pure-runes (universal-theory :here))
     (fn-lbw-cross-definition-runes (definition-theory (universal-theory :here)))))))))
(defthm fn-lbr1-reclaim-corr-positive
 (fn-lbc-corr (fn-lbc-open-rebuild (fn-lbr1-reclaim-rows) (fn-lbr1-reclaim-log) (create-fn-lbc))
              (fn-lbr1-reclaim-rows) (fn-lbr1-reclaim-log))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr1-reclaim-source-positive)
       (:instance fn-lbc-corr-of-open-rebuild (fn-lbc (create-fn-lbc))
          (rows (fn-lbr1-reclaim-rows)) (log (fn-lbr1-reclaim-log))))
 :in-theory (theory 'minimal-theory))))

(defun fn-lbr1-append-rows () (declare (xargs :guard t :verify-guards nil)) (fn-lbw-two-rows))
(defun fn-lbr1-append-log () (declare (xargs :guard t :verify-guards nil)) (fn-lb-log-model-append (fn-cat-assign (fn-lbw-incoming-held) (fn-lbw-two-rows)) *fn-lbw-payload-b* 2 (fn-lbw-two-log)))
(defthm fn-lbr1-append-source-positive
 (and (fn-lbc-p (create-fn-lbc)) (fn-cat-rowsp (fn-lbr1-append-rows))
      (fn-lbc-rows-log-guardp (fn-lbr1-append-rows) (fn-lbr1-append-log))
      (fn-lb-log-layoutp (fn-lbr1-append-log)) (fn-lb-log-model-segsp (fn-lbr1-append-log))
      (fn-lb-log-rows-sourcep (fn-lbr1-append-rows) (fn-lbr1-append-log)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
  (union-theories '(fn-lbc-p create-fn-lbc create-fn-dmap
    fn-lb-log-rows-sourcep fn-lb-log-row-sourcep fn-lb-log-row-copies-agreep
    fn-lb-log-entries-payload-agreep fn-lb-log-model-next-range fn-lbc-rows-log-guardp fn-lbc-row-log-guardp)
   (union-theories (fn-lbw-cross-pure-runes (universal-theory :here))
     (fn-lbw-cross-definition-runes (definition-theory (universal-theory :here)))))))))
(defthm fn-lbr1-append-corr-positive
 (fn-lbc-corr (fn-lbc-open-rebuild (fn-lbr1-append-rows) (fn-lbr1-append-log) (create-fn-lbc))
              (fn-lbr1-append-rows) (fn-lbr1-append-log))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr1-append-source-positive)
       (:instance fn-lbc-corr-of-open-rebuild (fn-lbc (create-fn-lbc))
          (rows (fn-lbr1-append-rows)) (log (fn-lbr1-append-log))))
 :in-theory (theory 'minimal-theory))))

(defun fn-lbr1-commit-rows () (declare (xargs :guard t :verify-guards nil)) (fn-cat$a-commit (fn-lbw-incoming-held) (fn-lbw-two-rows)))
(defun fn-lbr1-commit-log () (declare (xargs :guard t :verify-guards nil)) (fn-lb-log-model-append (fn-cat-assign (fn-lbw-incoming-held) (fn-lbw-two-rows)) *fn-lbw-payload-b* 2 (fn-lbw-two-log)))
(defthm fn-lbr1-commit-source-positive
 (and (fn-lbc-p (create-fn-lbc)) (fn-cat-rowsp (fn-lbr1-commit-rows))
      (fn-lbc-rows-log-guardp (fn-lbr1-commit-rows) (fn-lbr1-commit-log))
      (fn-lb-log-layoutp (fn-lbr1-commit-log)) (fn-lb-log-model-segsp (fn-lbr1-commit-log))
      (fn-lb-log-rows-sourcep (fn-lbr1-commit-rows) (fn-lbr1-commit-log)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
  (union-theories '(fn-lbc-p create-fn-lbc create-fn-dmap
    fn-lb-log-rows-sourcep fn-lb-log-row-sourcep fn-lb-log-row-copies-agreep
    fn-lb-log-entries-payload-agreep fn-lb-log-model-next-range fn-lbc-rows-log-guardp fn-lbc-row-log-guardp)
   (union-theories (fn-lbw-cross-pure-runes (universal-theory :here))
     (fn-lbw-cross-definition-runes (definition-theory (universal-theory :here)))))))))
(defthm fn-lbr1-commit-corr-positive
 (fn-lbc-corr (fn-lbc-open-rebuild (fn-lbr1-commit-rows) (fn-lbr1-commit-log) (create-fn-lbc))
              (fn-lbr1-commit-rows) (fn-lbr1-commit-log))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr1-commit-source-positive)
       (:instance fn-lbc-corr-of-open-rebuild (fn-lbc (create-fn-lbc))
          (rows (fn-lbr1-commit-rows)) (log (fn-lbr1-commit-log))))
 :in-theory (theory 'minimal-theory))))

(defun fn-lbr1-allocated-commit-rows () (declare (xargs :guard t :verify-guards nil)) (fn-cat$a-commit (fn-lbw-incoming-held) (fn-lbw-two-rows)))
(defun fn-lbr1-allocated-commit-log () (declare (xargs :guard t :verify-guards nil)) (fn-lb-log-model-append (fn-cat-assign (fn-lbw-incoming-held) (fn-lbw-two-rows)) *fn-lbw-payload-b* 2 (fn-lbw-two-log)))
(defthm fn-lbr1-allocated-commit-source-positive
 (and (fn-lbc-p (create-fn-lbc)) (fn-cat-rowsp (fn-lbr1-allocated-commit-rows))
      (fn-lbc-rows-log-guardp (fn-lbr1-allocated-commit-rows) (fn-lbr1-allocated-commit-log))
      (fn-lb-log-layoutp (fn-lbr1-allocated-commit-log)) (fn-lb-log-model-segsp (fn-lbr1-allocated-commit-log))
      (fn-lb-log-rows-sourcep (fn-lbr1-allocated-commit-rows) (fn-lbr1-allocated-commit-log)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
  (union-theories '(fn-lbc-p create-fn-lbc create-fn-dmap
    fn-lb-log-rows-sourcep fn-lb-log-row-sourcep fn-lb-log-row-copies-agreep
    fn-lb-log-entries-payload-agreep fn-lb-log-model-next-range fn-lbc-rows-log-guardp fn-lbc-row-log-guardp)
   (union-theories (fn-lbw-cross-pure-runes (universal-theory :here))
     (fn-lbw-cross-definition-runes (definition-theory (universal-theory :here)))))))))
(defthm fn-lbr1-allocated-commit-corr-positive
 (fn-lbc-corr (fn-lbc-open-rebuild (fn-lbr1-allocated-commit-rows) (fn-lbr1-allocated-commit-log) (create-fn-lbc))
              (fn-lbr1-allocated-commit-rows) (fn-lbr1-allocated-commit-log))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr1-allocated-commit-source-positive)
       (:instance fn-lbc-corr-of-open-rebuild (fn-lbc (create-fn-lbc))
          (rows (fn-lbr1-allocated-commit-rows)) (log (fn-lbr1-allocated-commit-log))))
 :in-theory (theory 'minimal-theory))))

(defun fn-lbr1-move-rows () (declare (xargs :guard t :verify-guards nil)) (list (fn-lbr13-held)))
(defun fn-lbr1-move-log () (declare (xargs :guard t :verify-guards nil)) (fn-lb-log-model-append (fn-lbr13-held) *fn-lbr13-payload* 2 (fn-lb-log-model-append (fn-lbr13-held) *fn-lbr13-payload* 1 nil)))
(defthm fn-lbr1-move-source-positive
 (and (fn-lbc-p (create-fn-lbc)) (fn-cat-rowsp (fn-lbr1-move-rows))
      (fn-lbc-rows-log-guardp (fn-lbr1-move-rows) (fn-lbr1-move-log))
      (fn-lb-log-layoutp (fn-lbr1-move-log)) (fn-lb-log-model-segsp (fn-lbr1-move-log))
      (fn-lb-log-rows-sourcep (fn-lbr1-move-rows) (fn-lbr1-move-log)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
  (union-theories '(fn-lbc-p create-fn-lbc create-fn-dmap
    fn-lb-log-rows-sourcep fn-lb-log-row-sourcep fn-lb-log-row-copies-agreep
    fn-lb-log-entries-payload-agreep fn-lb-log-model-next-range fn-lbc-rows-log-guardp fn-lbc-row-log-guardp)
   (union-theories (fn-lbw-cross-pure-runes (universal-theory :here))
     (fn-lbw-cross-definition-runes (definition-theory (universal-theory :here)))))))))
(defthm fn-lbr1-move-corr-positive
 (fn-lbc-corr (fn-lbc-open-rebuild (fn-lbr1-move-rows) (fn-lbr1-move-log) (create-fn-lbc))
              (fn-lbr1-move-rows) (fn-lbr1-move-log))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr1-move-source-positive)
       (:instance fn-lbc-corr-of-open-rebuild (fn-lbc (create-fn-lbc))
          (rows (fn-lbr1-move-rows)) (log (fn-lbr1-move-log))))
 :in-theory (theory 'minimal-theory))))

(defun fn-lbr1-open-rebuild-rows () (declare (xargs :guard t :verify-guards nil)) (fn-lbw-two-rows))
(defun fn-lbr1-open-rebuild-log () (declare (xargs :guard t :verify-guards nil)) (fn-lbw-two-log))
(defthm fn-lbr1-open-rebuild-source-positive
 (and (fn-lbc-p (create-fn-lbc)) (fn-cat-rowsp (fn-lbr1-open-rebuild-rows))
      (fn-lbc-rows-log-guardp (fn-lbr1-open-rebuild-rows) (fn-lbr1-open-rebuild-log))
      (fn-lb-log-layoutp (fn-lbr1-open-rebuild-log)) (fn-lb-log-model-segsp (fn-lbr1-open-rebuild-log))
      (fn-lb-log-rows-sourcep (fn-lbr1-open-rebuild-rows) (fn-lbr1-open-rebuild-log)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
  (union-theories '(fn-lbc-p create-fn-lbc create-fn-dmap
    fn-lb-log-rows-sourcep fn-lb-log-row-sourcep fn-lb-log-row-copies-agreep
    fn-lb-log-entries-payload-agreep fn-lb-log-model-next-range fn-lbc-rows-log-guardp fn-lbc-row-log-guardp)
   (union-theories (fn-lbw-cross-pure-runes (universal-theory :here))
     (fn-lbw-cross-definition-runes (definition-theory (universal-theory :here)))))))))
(defthm fn-lbr1-open-rebuild-corr-positive
 (fn-lbc-corr (fn-lbc-open-rebuild (fn-lbr1-open-rebuild-rows) (fn-lbr1-open-rebuild-log) (create-fn-lbc))
              (fn-lbr1-open-rebuild-rows) (fn-lbr1-open-rebuild-log))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbr1-open-rebuild-source-positive)
       (:instance fn-lbc-corr-of-open-rebuild (fn-lbc (create-fn-lbc))
          (rows (fn-lbr1-open-rebuild-rows)) (log (fn-lbr1-open-rebuild-log))))
 :in-theory (theory 'minimal-theory))))

(defun-nx fn-lbr1-move-state ()
 (update-fn-lbc-loc0 0 2
  (fn-lbc-open-rebuild (fn-lbr1-move-rows) (fn-lbr1-move-log) (create-fn-lbc))))
(defthm fn-lbr1-move-relocated-corr-positive
 (and (equal (fn-lbc-loc0 0 (fn-lbr1-move-state)) 2)
      (fn-lbc-corr (fn-lbr1-move-state) (fn-lbr1-move-rows) (fn-lbr1-move-log)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :expand ((:free (i fn-lbc) (fn-lbc-escape-cellsp i fn-lbc))
(:free (i fn-lbc) (fn-lbc-number-escape-cellsp i fn-lbc))
(:free (i fn-lbc) (fn-lbc-stamp-escape-cellsp i fn-lbc))
(:free (off n fn-lbc) (fn-lbc-msgid-pool-range off n fn-lbc))
(:free (bytes fn-lbc) (fn-lbc-msgid-pool-append bytes fn-lbc))
(:free (off n fn-lbc) (fn-lbc-overview-pool-range off n fn-lbc))
(:free (bytes fn-lbc) (fn-lbc-overview-pool-append bytes fn-lbc))
(:free (i field fn-lbc) (fn-lbc-escape i field fn-lbc))
(:free (i fn-lbc) (fn-lbc-msgid i fn-lbc))
(:free (start count numbersp fn-lbc) (fn-lbc-membership-run start count numbersp fn-lbc))
(:free (fields values) (fn-lbc-sparse-u64 fields values))
(:free (numbers) (fn-lbc-numbers-smallp numbers))
(:free (texts fn-lbc) (fn-lbc-append-nov-texts texts fn-lbc))
(:free (texts offset) (fn-lbc-nov-spans texts offset))
(:free (nov fn-lbc) (fn-lbc-append-nov nov fn-lbc))
(:free (items numbersp fn-lbc) (fn-lbc-append-memberships items numbersp fn-lbc))
(:free (bytes hash) (fn-lbc-msgid-hash-octets bytes hash))
(:free (msgid) (fn-lbc-msgid-hash msgid))
(:free (rows log) (fn-lbc-rows-log-guardp rows log))
(:free (rows) (fn-lbc-row-homes-guardp rows))
(:free (threshold lo hi fn-lbc) (fn-lbc-first-reaching threshold lo hi fn-lbc))
(:free (groups numbers) (fn-lbc-newnews-candidatep groups numbers))
(:free (groups threshold v lo hi fn-lbc) (fn-lbc-newnews-tail groups threshold v lo hi fn-lbc))
(:free (numbers seen i fn-lbc) (fn-lbc-number-put-row-seen numbers seen i fn-lbc))
(:free (numbers i fn-lbc) (fn-lbc-number-put-row numbers i fn-lbc))
(:free (group values field fn-lbc) (fn-lbc-summary-put group values field fn-lbc))
(:free (numbers) (fn-lbc-number-group-keys numbers))
(:free (rows) (fn-lbc-row-group-keys rows))
(:free (groups rows fn-lbc) (fn-lbc-rebuild-summaries groups rows fn-lbc))
(:free (rows log fn-lbc) (fn-lbc-rebuild-rows rows log fn-lbc))
(:free (keys fn-lbc) (fn-lbc-slot-owners-guardp keys fn-lbc))
(:free (i fn-lbc) (fn-lbc-slot-values-guardp i fn-lbc))
(:free (slot keys fn-lbc) (fn-lbc-escaped-slot-word slot keys fn-lbc))
(:free (slot keys fn-lbc) (fn-lbc-slot-drop-owner slot keys fn-lbc))
(:free (n fn-lbc) (fn-lbc-reserve-slots n fn-lbc))
(:free (i slot fuel fn-lbc) (fn-lbc-slot-insert i slot fuel fn-lbc))
(:free (i n fn-lbc) (fn-lbc-index-slots i n fn-lbc))
(:free (msgid hash slot fuel fn-lbc) (fn-lbc-msgid-probe msgid hash slot fuel fn-lbc))
(:free (ordinal slot fuel table) (fn-lbc-canonical-slot-insert ordinal slot fuel table))
(:free (rows i table) (fn-lbc-canonical-slots-from rows i table))
(:free (rows) (fn-lbc-canonical-slots rows))
(:free (table slot fn-lbc) (fn-lbc-slot-cells-corr table slot fn-lbc))
(:free (numbers rows fn-lbc) (fn-lbc-number-keys-covered numbers rows fn-lbc))
(:free (rest rows fn-lbc) (fn-lbc-number-rows-covered rest rows fn-lbc))
(:free (i rows prefix-max fn-lbc log) (fn-lbc-rows-corr i rows prefix-max fn-lbc log))
(:free (groups rows fn-lbc) (fn-lbc-summaries-corr groups rows fn-lbc))
(:free (keys table rows) (fn-lbc-summary-cells-corr keys table rows))
(:free (keys table rows) (fn-lbc-number-cells-corr keys table rows)))
 :in-theory (union-theories (theory 'ground-zero)
  (union-theories (fn-lbw-cross-pure-runes (universal-theory :here))
   (union-theories '(fn-lbr1-move-state fn-lbr13-finish-single-row update-fn-lbc-loc0 create-fn-lbc create-fn-dmap fn-lb-retained-payloads-agreep fn-lb-log-row-copies-agreep fn-lb-log-entries-payload-agreep) (fn-lbw-cross-definition-runes (definition-theory (universal-theory :here)))))))))
