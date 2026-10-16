; Actual duplicate command calls refute each operation's derived cost claim.
(in-package "ACL2")
(include-book "../../books/catalog-columns-command-cost")
(include-book "lb-column-read-cost-teeth")
(local (defun fn-lbcc-test-theory (runes)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp runes)
  (let* ((r (car runes)) (sym (fn-ag-car (fn-ag-cdr r)))
         (name (if (symbolp sym) (symbol-name sym) ""))
         (model (or (equal (subseq name 0 (min 6 (length name))) "FN-LBC")
                    (equal (subseq name 0 (min 8 (length name))) "FN-DMAP-")
                    (equal (subseq name 0 (min 14 (length name))) "UPDATE-FN-LBC-")
                    (member-eq sym '(create-fn-lbc create-fn-dmap)))))
   (if (or (and model (equal (fn-ag-car r) :definition))
           (and (not model) (equal (fn-ag-car r) :executable-counterpart)))
    (cons r (fn-lbcc-test-theory (cdr runes)))
    (fn-lbcc-test-theory (cdr runes)))) nil)))
(defthm fn-lbcct-command-counts-positive
 (and
 (equal (fn-lbc-over-row-fetches "fn.test" 1 1 1 (fn-lbcc-test-one-state)) 1)
 (equal (len (fn-lbc-over-eligible "fn.test" 1 1 1 (fn-lbcc-test-one-state))) 1)
 (equal (fn-lbc-over-probes "fn.test" 1 1 1 (fn-lbcc-test-one-state)) 1)
 (equal (fn-lbc-listgroup-number-reads "fn.test" 1 1 1 (fn-lbcc-test-one-state)) 1)
 (equal (len (fn-lbc-listgroup-numbers "fn.test" 1 1 1 (fn-lbcc-test-one-state))) 1)
 (equal (fn-lbc-list-summary-reads '("fn.test" "empty.test") (fn-lbcc-test-one-state)) 2))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :expand ((:free (group v lo hi fn-lbc-v acc) (fn-lbc-over-loop-row-fetches group v lo hi fn-lbc-v acc))
(:free (group v lo hi fn-lbc-v acc) (fn-lbc-over-loop-probes group v lo hi fn-lbc-v acc))
(:free (group v lo hi fn-lbc) (fn-lbc-over-eligible group v lo hi fn-lbc))
(:free (group v lo hi fn-lbc-v acc) (fn-lbc-listgroup-loop-number-reads group v lo hi fn-lbc-v acc))
(:free (lo hi) (fn-lbc-listgroup-requested-numbers lo hi))
(:free (groups fn-lbc-v acc) (fn-lbc-list-loop-summary-reads groups fn-lbc-v acc))
(:free (i fn-lbc) (fn-lbc-escape-cellsp i fn-lbc))
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
 :in-theory
  (union-theories (theory 'ground-zero) (fn-lbcc-test-theory (universal-theory :here))))))

(defun fn-lbcct-double-over (group v lo hi fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (and (natp lo) (natp hi) (fn-lbc-escape-cellsp 0 fn-lbc)) :verify-guards nil))
 (list (fn-lbc-over group v lo hi fn-lbc) (fn-lbc-over group v lo hi fn-lbc)))
(def-cost fn-lbcct-double-over
 :unaccounted (fn-lbc-directory-value fn-lbc-escape fn-lbc-id-article fn-lbc-render-nov fn-lbc-visiblep fn-nntp-article-idp)
 :calls ((row-fetches (fn-lbc-render-nov)) (probes (fn-lbc-number-get))))
(defun fn-lbcct-double-listgroup (group v lo hi fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (and (natp lo) (natp hi) (fn-lbc-escape-cellsp 0 fn-lbc)) :verify-guards nil))
 (list (fn-lbc-listgroup group v lo hi fn-lbc) (fn-lbc-listgroup group v lo hi fn-lbc)))
(def-cost fn-lbcct-double-listgroup
 :unaccounted (fn-lbc-directory-value fn-lbc-escape fn-lbc-id-article fn-lbc-visiblep fn-nntp-article-idp)
 :calls ((number-reads (fn-lbc-number-get))))
(defun fn-lbcct-double-list (groups fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-escape-cellsp 0 fn-lbc) :verify-guards nil))
 (list (fn-lbc-list groups fn-lbc) (fn-lbc-list groups fn-lbc)))
(def-cost fn-lbcct-double-list
 :unaccounted ()
 :calls ((summary-reads (fn-lbc-live-summary))))
(defthm fn-lbcct-over-fetch-whole-witness
 (equal (fn-lbc-over-row-fetches "fn.test" 1 1 1 (fn-lbcc-test-one-state)) (len (fn-lbc-over-eligible "fn.test" 1 1 1 (fn-lbcc-test-one-state)))) :rule-classes nil
 :hints (("Goal" :use fn-lbcct-command-counts-positive :in-theory (theory 'ground-zero))))
(defthm fn-lbcct-over-fetch-fault-whole-witness
 (and (equal (fn-lbc-over-row-fetches "fn.test" 1 1 1 (fn-lbcc-test-one-state)) (len (fn-lbc-over-eligible "fn.test" 1 1 1 (fn-lbcc-test-one-state)))) (not (equal (fn-lbcct-double-over-row-fetches "fn.test" 1 1 1 (fn-lbcc-test-one-state)) (len (fn-lbc-over-eligible "fn.test" 1 1 1 (fn-lbcc-test-one-state)))))) :rule-classes nil
 :hints (("Goal" :use fn-lbcct-command-counts-positive
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbcct-double-over-row-fetches)))))
(defteeth fn-lbc-over-fetches-exactly-eligible
 :claim (nil (equal (fn-lbc-over-row-fetches group v lo hi fn-lbc-v) (len (fn-lbc-over-eligible group v lo hi fn-lbc-v))))
 :subject fn-lbc-over :witness ((group "fn.test") (v 1) (lo 1) (hi 1) (fn-lbc-v (fn-lbcc-test-one-state))) :witness-lemma fn-lbcct-over-fetch-whole-witness
 :breaks ()
 :mutations ((duplicate-command (:conclusion (equal (fn-lbcct-double-over-row-fetches group v lo hi fn-lbc-v) (len (fn-lbc-over-eligible group v lo hi fn-lbc-v)))) ((group "fn.test") (v 1) (lo 1) (hi 1) (fn-lbc-v (fn-lbcc-test-one-state)))
  :fault "The operation repeats its actual column-reader command" :lemma fn-lbcct-over-fetch-fault-whole-witness)))
(defthm fn-lbcct-over-probe-whole-witness
 (and (<= 1 1) (<= (fn-lbc-over-probes "fn.test" 1 1 1 (fn-lbcc-test-one-state)) (+ 1 (binary-+ 1 (unary-- 1))))) :rule-classes nil
 :hints (("Goal" :use fn-lbcct-command-counts-positive :in-theory (theory 'ground-zero))))
(defthm fn-lbcct-over-probe-fault-whole-witness
 (and (<= 1 1) (<= (fn-lbc-over-probes "fn.test" 1 1 1 (fn-lbcc-test-one-state)) (+ 1 (binary-+ 1 (unary-- 1)))) (not (<= (fn-lbcct-double-over-probes "fn.test" 1 1 1 (fn-lbcc-test-one-state)) (+ 1 (binary-+ 1 (unary-- 1)))))) :rule-classes nil
 :hints (("Goal" :use fn-lbcct-command-counts-positive
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbcct-double-over-probes)))))
(defthm fn-lbcct-over-probe-removal
 (and (not (<= 3 1)) (not (<= (fn-lbc-over-probes "fn.test" 1 3 1 (fn-lbcc-test-one-state)) (+ 1 (binary-+ 1 (unary-- 3))))))
 :rule-classes nil :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-over-probes fn-lbc-over-loop-probes natp nfix)))))
(defteeth fn-lbc-over-probes-at-most-range
 :claim (((ordered (<= lo hi))) (<= (fn-lbc-over-probes group v lo hi fn-lbc-v) (+ 1 (- hi lo))))
 :subject fn-lbc-over :witness ((group "fn.test") (v 1) (lo 1) (hi 1) (fn-lbc-v (fn-lbcc-test-one-state))) :witness-lemma fn-lbcct-over-probe-whole-witness
 :breaks ((ordered ((group "fn.test") (v 1) (lo 3) (hi 1) (fn-lbc-v (fn-lbcc-test-one-state))) :lemma fn-lbcct-over-probe-removal :logical "Both endpoints are natural; the order premise is deliberately false"))
 :mutations ((duplicate-command (:conclusion (<= (fn-lbcct-double-over-probes group v lo hi fn-lbc-v) (+ 1 (- hi lo)))) ((group "fn.test") (v 1) (lo 1) (hi 1) (fn-lbc-v (fn-lbcc-test-one-state)))
  :fault "The operation repeats its actual column-reader command" :lemma fn-lbcct-over-probe-fault-whole-witness)))
(defthm fn-lbcct-listgroup-reads-whole-witness
 (equal (fn-lbc-listgroup-number-reads "fn.test" 1 1 1 (fn-lbcc-test-one-state)) (len (fn-lbc-listgroup-numbers "fn.test" 1 1 1 (fn-lbcc-test-one-state)))) :rule-classes nil
 :hints (("Goal" :use fn-lbcct-command-counts-positive :in-theory (theory 'ground-zero))))
(defthm fn-lbcct-listgroup-reads-fault-whole-witness
 (and (equal (fn-lbc-listgroup-number-reads "fn.test" 1 1 1 (fn-lbcc-test-one-state)) (len (fn-lbc-listgroup-numbers "fn.test" 1 1 1 (fn-lbcc-test-one-state)))) (not (equal (fn-lbcct-double-listgroup-number-reads "fn.test" 1 1 1 (fn-lbcc-test-one-state)) (len (fn-lbc-listgroup-numbers "fn.test" 1 1 1 (fn-lbcc-test-one-state)))))) :rule-classes nil
 :hints (("Goal" :use fn-lbcct-command-counts-positive
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbcct-double-listgroup-number-reads)))))
(defteeth fn-lbc-listgroup-number-reads-exact
 :claim (nil (equal (fn-lbc-listgroup-number-reads group v lo hi fn-lbc-v) (len (fn-lbc-listgroup-numbers group v lo hi fn-lbc-v))))
 :subject fn-lbc-listgroup :witness ((group "fn.test") (v 1) (lo 1) (hi 1) (fn-lbc-v (fn-lbcc-test-one-state))) :witness-lemma fn-lbcct-listgroup-reads-whole-witness
 :breaks ()
 :mutations ((duplicate-command (:conclusion (equal (fn-lbcct-double-listgroup-number-reads group v lo hi fn-lbc-v) (len (fn-lbc-listgroup-numbers group v lo hi fn-lbc-v)))) ((group "fn.test") (v 1) (lo 1) (hi 1) (fn-lbc-v (fn-lbcc-test-one-state)))
  :fault "The operation repeats its actual column-reader command" :lemma fn-lbcct-listgroup-reads-fault-whole-witness)))
(defthm fn-lbcct-list-summaries-whole-witness
 (equal (fn-lbc-list-summary-reads '("fn.test" "empty.test") (fn-lbcc-test-one-state)) (len '("fn.test" "empty.test"))) :rule-classes nil
 :hints (("Goal" :use fn-lbcct-command-counts-positive :in-theory (theory 'ground-zero))))
(defthm fn-lbcct-list-summaries-fault-whole-witness
 (and (equal (fn-lbc-list-summary-reads '("fn.test" "empty.test") (fn-lbcc-test-one-state)) (len '("fn.test" "empty.test"))) (not (equal (fn-lbcct-double-list-summary-reads '("fn.test" "empty.test") (fn-lbcc-test-one-state)) (len '("fn.test" "empty.test"))))) :rule-classes nil
 :hints (("Goal" :use fn-lbcct-command-counts-positive
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbcct-double-list-summary-reads)))))
(defteeth fn-lbc-list-exact-summary-reads
 :claim (nil (equal (fn-lbc-list-summary-reads groups fn-lbc-v) (len groups)))
 :subject fn-lbc-list :witness ((groups '("fn.test" "empty.test")) (fn-lbc-v (fn-lbcc-test-one-state))) :witness-lemma fn-lbcct-list-summaries-whole-witness
 :breaks ()
 :mutations ((duplicate-command (:conclusion (equal (fn-lbcct-double-list-summary-reads groups fn-lbc-v) (len groups))) ((groups '("fn.test" "empty.test")) (fn-lbc-v (fn-lbcc-test-one-state)))
  :fault "The operation repeats its actual column-reader command" :lemma fn-lbcct-list-summaries-fault-whole-witness)))
