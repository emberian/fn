; Whole retrieval one-request bound, with a derived duplicate-call fault.
(in-package "ACL2")
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
(defthm fn-lbcct-retrieval-one-request-positive
 (equal (fn-lbc-retrieval-range-requests '(t "fn.test" 1 nil) nil nil :head nil nil 1
 (fn-lb-log-model-append (fn-lbcc-test-decided-row) *fn-lbr13-payload* 1 nil)
 '(nil nil) (list *fn-lbr13-payload*) (fn-lbcc-test-one-state)) 1)
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
 :in-theory
  (union-theories (theory 'ground-zero) (fn-lbcc-test-theory (universal-theory :here))))))
(defun fn-lbcct-duplicate-retrieval
    (session archive arts kind args server v log fn-lb-vmap fn-arena fn-lbc)
 (declare (ignorable archive arts fn-arena) (xargs :stobjs (fn-lb-vmap fn-arena fn-lbc) :guard (and (fn-lbc-escape-cellsp 0 fn-lbc) (fn-lbc-slot-owners-guardp (fn-lbc-slot-escape-keys fn-lbc) fn-lbc) (fn-lb-log-read-guardp log) (or (atom args) (true-listp (car args))) (fn-lbc-section-values-guardp 0 fn-lbc log)) :verify-guards nil))
 (list (fn-lbc-retrieval session archive arts kind args server v log fn-lb-vmap fn-arena fn-lbc)
       (fn-lbc-retrieval session archive arts kind args server v log fn-lb-vmap fn-arena fn-lbc)))
(def-cost fn-lbcct-duplicate-retrieval :unaccounted (fn-arx-entry-ok fn-lb-entry-octets fn-lb-entry-protected-len fn-lb-log-model-read-range fn-lb-log-model-unwire fn-lb-unverified-refusal fn-lbc-article fn-lbc-directory-value fn-lbc-flag fn-lbc-id-article fn-lbc-select fn-lbc-selected-reads-entry-p fn-lbc-value fn-lbc-xref-shift-prefix fn-nntp-article-idp fn-nntp-article-response-of-bytes fn-nntp-crlf fn-nntp-response-okp-of-bytes fn-nntp-retrieval-initial fn-nntp-single fn-nntp-stuffed-section fn-rcompat-served-payload-of-bytes fn-xref-field fn-xref-pairs fn-xref-serverp)
 :calls ((range-requests (fn-lb-log-model-read-range) :stop-at (fn-lb-entry-octets))))
(defthm fn-lbcct-retrieval-bound-whole-witness
 (<= (fn-lbc-retrieval-range-requests '(t "fn.test" 1 nil) nil nil :head nil nil 1
       (fn-lb-log-model-append (fn-lbcc-test-decided-row) *fn-lbr13-payload* 1 nil)
       '(nil nil) (list *fn-lbr13-payload*) (fn-lbcc-test-one-state)) 1)
 :rule-classes nil
 :hints (("Goal" :use fn-lbcct-retrieval-one-request-positive :in-theory (theory 'ground-zero))))
(defthm fn-lbcct-retrieval-double-fault-whole-witness
 (and
  (<= (fn-lbc-retrieval-range-requests '(t "fn.test" 1 nil) nil nil :head nil nil 1
       (fn-lb-log-model-append (fn-lbcc-test-decided-row) *fn-lbr13-payload* 1 nil)
       '(nil nil) (list *fn-lbr13-payload*) (fn-lbcc-test-one-state)) 1)
  (not (<= (fn-lbcct-duplicate-retrieval-range-requests '(t "fn.test" 1 nil) nil nil :head nil nil 1
       (fn-lb-log-model-append (fn-lbcc-test-decided-row) *fn-lbr13-payload* 1 nil)
       '(nil nil) (list *fn-lbr13-payload*) (fn-lbcc-test-one-state)) 1)))
 :rule-classes nil
 :hints (("Goal" :use fn-lbcct-retrieval-one-request-positive
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbcct-duplicate-retrieval-range-requests)))))
(defteeth fn-lbc-retrieval-at-most-one-range-request
 :claim (nil (<= (fn-lbc-retrieval-range-requests session archive arts kind args server v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 1))
 :subject fn-lbc-retrieval
 :witness ((session '(t "fn.test" 1 nil)) (archive nil) (arts nil) (kind :head) (args nil) (server nil) (v 1)
           (log (fn-lb-log-model-append (fn-lbcc-test-decided-row) *fn-lbr13-payload* 1 nil))
           (fn-lb-vmap-v '(nil nil)) (fn-arena-v (list *fn-lbr13-payload*)) (fn-lbc-v (fn-lbcc-test-one-state)))
 :witness-lemma fn-lbcct-retrieval-bound-whole-witness
 :breaks ()
 :mutations ((duplicate-retrieval
  (:conclusion (<= (fn-lbcct-duplicate-retrieval-range-requests session archive arts kind args server v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 1))
  ((session '(t "fn.test" 1 nil)) (archive nil) (arts nil) (kind :head) (args nil) (server nil) (v 1)
   (log (fn-lb-log-model-append (fn-lbcc-test-decided-row) *fn-lbr13-payload* 1 nil))
   (fn-lb-vmap-v '(nil nil)) (fn-arena-v (list *fn-lbr13-payload*)) (fn-lbc-v (fn-lbcc-test-one-state)))
  :fault "the retrieval path executes the same section request twice"
  :lemma fn-lbcct-retrieval-double-fault-whole-witness)))
(defun fn-lbcct-native-retrieval-control ()
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-lbc
  (mv-let (ok fn-lbc)
   (with-local-stobj fn-lb-vmap
    (mv-let (ok fn-lb-vmap fn-lbc)
     (with-local-stobj fn-arena
      (mv-let (ok fn-arena fn-lb-vmap fn-lbc)
       (let* ((row (fn-lbcc-test-decided-row))
              (log (fn-lb-log-model-append row *fn-lbr13-payload* 1 nil))
              (fn-arena (fn-arena-seal-list *fn-lbr13-payload* fn-arena))
              (fn-lbc (fn-lbc-open-rebuild (list row) log fn-lbc))
              (reply (fn-lbc-retrieval '(t "fn.test" 1 nil) nil nil :head nil nil 1
                       log fn-lb-vmap fn-arena fn-lbc))
              (line (fn-ag-car (fn-ag-cdr (fn-ag-car (fn-nntp-result-effects reply))))))
        (mv (equal (take 3 line) '(50 50 49)) fn-arena fn-lb-vmap fn-lbc))
       (mv ok fn-lb-vmap fn-lbc)))
     (mv ok fn-lbc)))
   ok)))
(with-guard-checking-event t (assert-event (fn-lbcct-native-retrieval-control)))
