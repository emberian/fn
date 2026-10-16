; Zero payload reads on refused/withdrawn/reclaimed rows and STAT.
(in-package "ACL2")
(include-book "lb-retrieval-cost-teeth")
(local (defun fn-lbzc-test-theory (runes)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp runes)
  (let* ((r (car runes)) (sym (fn-ag-car (fn-ag-cdr r)))
         (name (if (symbolp sym) (symbol-name sym) ""))
         (model (or (equal (subseq name 0 (min 6 (length name))) "FN-LBC")
                    (equal (subseq name 0 (min 8 (length name))) "FN-DMAP-") (equal (subseq name 0 (min 7 (length name))) "FN-LBZC")
                    (equal (subseq name 0 (min 14 (length name))) "UPDATE-FN-LBC-")
                    (member-eq sym '(create-fn-lbc create-fn-dmap)))))
   (if (or (and model (equal (fn-ag-car r) :definition))
           (and (not model) (equal (fn-ag-car r) :executable-counterpart)))
    (cons r (fn-lbzc-test-theory (cdr runes)))
    (fn-lbzc-test-theory (cdr runes)))) nil)))
(defun fn-lbzc-log ()
 (declare (xargs :guard t :verify-guards nil))
 (fn-lb-log-model-append (fn-lbcc-test-decided-row) *fn-lbr13-payload* 1 nil))
(defun-nx fn-lbzc-withdrawn-state ()
 (fn-lbcc-test-model-columns (fn-cat$a-withdraw 0 99 (list (fn-lbcc-test-decided-row))) (fn-lbzc-log)))
(defun fn-lbzc-prefetch (session kind v log fn-lb-vmap fn-arena fn-lbc)
 (declare (xargs :stobjs (fn-lb-vmap fn-arena fn-lbc) :guard (and
  (fn-lbc-escape-cellsp 0 fn-lbc)
  (fn-lbc-slot-owners-guardp (fn-lbc-slot-escape-keys fn-lbc) fn-lbc)
  (fn-lb-log-read-guardp log) (fn-lbc-section-values-guardp 0 fn-lbc log)) :verify-guards nil))
 (list (fn-lb-log-model-read-range 1 6 1 log)
       (fn-lb-entry-octets 1 6 log)
       (fn-lbc-retrieval session nil nil kind nil nil v log fn-lb-vmap fn-arena fn-lbc)))
(def-cost fn-lbzc-prefetch
 :unaccounted (fn-arx-entry-ok fn-lb-entry-octets fn-lb-entry-protected-len fn-lb-log-model-read-range fn-lb-log-model-unwire fn-lb-unverified-refusal fn-lbc-article fn-lbc-directory-value fn-lbc-flag fn-lbc-id-article fn-lbc-select fn-lbc-selected-reads-entry-p fn-lbc-value fn-lbc-xref-shift-prefix fn-nntp-article-idp fn-nntp-article-response-of-bytes fn-nntp-crlf fn-nntp-response-okp-of-bytes fn-nntp-retrieval-initial fn-nntp-single fn-nntp-stuffed-section fn-rcompat-served-payload-of-bytes fn-xref-field fn-xref-pairs fn-xref-serverp)
 :calls ((range-requests (fn-lb-log-model-read-range) :stop-at (fn-lb-entry-octets))
         (entry-reads (fn-lb-entry-octets))))
(defthm fn-lbzc-native-selection-facts
 (and (equal (car (fn-lbc-select '(t "fn.test" 1 nil) :head nil 1 (fn-lbcc-test-one-state))) :row)
(equal (car (fn-lbc-select '(t "fn.test" 1 nil) :head nil 0 (fn-lbcc-test-one-state))) :refusal)
(equal (car (fn-lbc-select '(t nil nil nil) :head nil 1 (fn-lbcc-test-one-state))) :refusal)
(not (fn-lbc-visiblep (fn-lbc-number-get "fn.test" 1 (fn-lbzc-withdrawn-state)) 2 (fn-lbzc-withdrawn-state)))
(equal (fn-lbc-number-get "fn.test" 1 (fn-lbcc-test-one-state)) 0)
(fn-lbc-visiblep 0 1 (fn-lbcc-test-one-state))
(not (fn-lbc-visiblep 0 0 (fn-lbcc-test-one-state)))
(equal (fn-lbc-retrieval-entry-reads '(t "fn.test" 1 nil) nil nil :head nil nil 1 (fn-lbzc-log) '(nil nil) nil (fn-lbcc-test-one-state)) 1)) :rule-classes nil
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
  (union-theories (theory 'ground-zero) (fn-lbzc-test-theory (universal-theory :here))))))

; BEGIN generated zero-cost teeth
(defthm fn-lbzc-stat-whole-positive
 (equal (fn-lbc-retrieval-range-requests '(t "fn.test" 1 nil) nil nil :stat nil nil 1 (fn-lbzc-log) '(nil nil) nil (fn-lbcc-test-one-state)) 0) :rule-classes nil
 :hints (("Goal" :use (fn-lbzc-native-selection-facts (:instance fn-lbc-stat-no-range-request
  (session '(t "fn.test" 1 nil)) (archive nil) (arts nil)  (args nil) (server nil)
  (v 1) (log (fn-lbzc-log)) (fn-lb-vmap-v '(nil nil)) (fn-arena-v nil) (fn-lbc-v (fn-lbcc-test-one-state))))
  :in-theory (union-theories (theory 'ground-zero) '(fn-nntp-session-group fn-nntp-session-current)))))
(defthm fn-lbzc-stat-fault-whole-positive
 (and (equal (fn-lbc-retrieval-range-requests '(t "fn.test" 1 nil) nil nil :stat nil nil 1 (fn-lbzc-log) '(nil nil) nil (fn-lbcc-test-one-state)) 0) (not (equal (fn-lbzc-prefetch-range-requests '(t "fn.test" 1 nil) :stat 1 (fn-lbzc-log) '(nil nil) nil (fn-lbcc-test-one-state)) 0))) :rule-classes nil
 :hints (("Goal" :use fn-lbzc-stat-whole-positive
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbzc-prefetch-range-requests)))))
(defteeth fn-lbc-stat-no-range-request
 :claim (nil (equal (fn-lbc-retrieval-range-requests session archive arts :stat args server v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 0))
 :subject fn-lbc-retrieval :witness ((session '(t "fn.test" 1 nil)) (archive nil) (arts nil) (kind :head) (args nil) (server nil) (v 1) (log (fn-lbzc-log)) (fn-lb-vmap-v '(nil nil)) (fn-arena-v nil) (fn-lbc-v (fn-lbcc-test-one-state))) :witness-lemma fn-lbzc-stat-whole-positive
 :breaks ()
 :mutations ((prefetch-before-selection (:conclusion (equal (fn-lbzc-prefetch-range-requests session :stat v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 0)) ((session '(t "fn.test" 1 nil)) (archive nil) (arts nil) (kind :head) (args nil) (server nil) (v 1) (log (fn-lbzc-log)) (fn-lb-vmap-v '(nil nil)) (fn-arena-v nil) (fn-lbc-v (fn-lbcc-test-one-state)))
  :fault "Read the entry and payload before deciding that the reply needs no bytes" :lemma fn-lbzc-stat-fault-whole-positive)))
(defthm fn-lbzc-withdrawn-whole-positive
 (and (not (fn-lbc-visiblep (fn-lbc-number-get (fn-nntp-session-group '(t "fn.test" 1 nil)) (fn-nntp-session-current '(t "fn.test" 1 nil)) (fn-lbzc-withdrawn-state)) 2 (fn-lbzc-withdrawn-state))) (and (equal (fn-lbc-retrieval-range-requests '(t "fn.test" 1 nil) nil nil :head nil nil 2 (fn-lbzc-log) '(nil nil) nil (fn-lbzc-withdrawn-state)) 0) (equal (fn-lbc-retrieval-entry-reads '(t "fn.test" 1 nil) nil nil :head nil nil 2 (fn-lbzc-log) '(nil nil) nil (fn-lbzc-withdrawn-state)) 0))) :rule-classes nil
 :hints (("Goal" :use (fn-lbzc-native-selection-facts (:instance fn-lbc-retrieval-withdrawn-reads-nothing
  (session '(t "fn.test" 1 nil)) (archive nil) (arts nil) (kind :head)  (server nil)
  (v 2) (log (fn-lbzc-log)) (fn-lb-vmap-v '(nil nil)) (fn-arena-v nil) (fn-lbc-v (fn-lbzc-withdrawn-state))))
  :in-theory (union-theories (theory 'ground-zero) '(fn-nntp-session-group fn-nntp-session-current)))))
(defthm fn-lbzc-withdrawn-fault-whole-positive
 (and (not (fn-lbc-visiblep (fn-lbc-number-get (fn-nntp-session-group '(t "fn.test" 1 nil)) (fn-nntp-session-current '(t "fn.test" 1 nil)) (fn-lbzc-withdrawn-state)) 2 (fn-lbzc-withdrawn-state))) (and (equal (fn-lbc-retrieval-range-requests '(t "fn.test" 1 nil) nil nil :head nil nil 2 (fn-lbzc-log) '(nil nil) nil (fn-lbzc-withdrawn-state)) 0) (equal (fn-lbc-retrieval-entry-reads '(t "fn.test" 1 nil) nil nil :head nil nil 2 (fn-lbzc-log) '(nil nil) nil (fn-lbzc-withdrawn-state)) 0)) (not (equal (fn-lbzc-prefetch-range-requests '(t "fn.test" 1 nil) :head 2 (fn-lbzc-log) '(nil nil) nil (fn-lbzc-withdrawn-state)) 0))) :rule-classes nil
 :hints (("Goal" :use fn-lbzc-withdrawn-whole-positive
  :in-theory (union-theories (theory 'ground-zero) '(fn-lbzc-prefetch-range-requests)))))
(defthm fn-lbzc-withdrawn-premise-removal
 (and (not (not (fn-lbc-visiblep (fn-lbc-number-get (fn-nntp-session-group '(t "fn.test" 1 nil)) (fn-nntp-session-current '(t "fn.test" 1 nil)) (fn-lbcc-test-one-state)) 1 (fn-lbcc-test-one-state)))) (not (and (equal (fn-lbc-retrieval-range-requests '(t "fn.test" 1 nil) nil nil :head nil nil 1 (fn-lbzc-log) '(nil nil) nil (fn-lbcc-test-one-state)) 0) (equal (fn-lbc-retrieval-entry-reads '(t "fn.test" 1 nil) nil nil :head nil nil 1 (fn-lbzc-log) '(nil nil) nil (fn-lbcc-test-one-state)) 0)))) :rule-classes nil
 :hints (("Goal" :use fn-lbzc-native-selection-facts
  :in-theory (union-theories (theory 'ground-zero) '(fn-nntp-session-group fn-nntp-session-current)))))
(defteeth fn-lbc-retrieval-withdrawn-reads-nothing
 :claim (((hidden (not (fn-lbc-visiblep (fn-lbc-number-get (fn-nntp-session-group session) (fn-nntp-session-current session) fn-lbc-v) v fn-lbc-v)))) (and (equal (fn-lbc-retrieval-range-requests session archive arts kind nil server v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 0) (equal (fn-lbc-retrieval-entry-reads session archive arts kind nil server v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 0)))
 :subject fn-lbc-retrieval :witness ((session '(t "fn.test" 1 nil)) (archive nil) (arts nil) (kind :head) (args nil) (server nil) (v 2) (log (fn-lbzc-log)) (fn-lb-vmap-v '(nil nil)) (fn-arena-v nil) (fn-lbc-v (fn-lbzc-withdrawn-state))) :witness-lemma fn-lbzc-withdrawn-whole-positive
 :breaks ((hidden ((session '(t "fn.test" 1 nil)) (archive nil) (arts nil) (kind :head) (args nil) (server nil) (v 1) (log (fn-lbzc-log)) (fn-lb-vmap-v '(nil nil)) (fn-arena-v nil) (fn-lbc-v (fn-lbcc-test-one-state))) :lemma fn-lbzc-withdrawn-premise-removal))
 :mutations ((prefetch-before-selection (:conclusion (equal (fn-lbzc-prefetch-range-requests session kind v log fn-lb-vmap-v fn-arena-v fn-lbc-v) 0)) ((session '(t "fn.test" 1 nil)) (archive nil) (arts nil) (kind :head) (args nil) (server nil) (v 2) (log (fn-lbzc-log)) (fn-lb-vmap-v '(nil nil)) (fn-arena-v nil) (fn-lbc-v (fn-lbzc-withdrawn-state)))
  :fault "Read the entry and payload before deciding that the reply needs no bytes" :lemma fn-lbzc-withdrawn-fault-whole-positive)))

(defun fn-lbzc-native-withdrawn-retrieval-control ()
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-lbc
  (mv-let (ok fn-lbc)
   (with-local-stobj fn-lb-vmap
    (mv-let (ok fn-lb-vmap fn-lbc)
     (with-local-stobj fn-arena
      (mv-let (ok fn-arena fn-lb-vmap fn-lbc)
       (let* ((rows (fn-cat$a-withdraw 0 99 (list (fn-lbcc-test-decided-row))))
              (log (fn-lbzc-log))
              (fn-arena (fn-arena-seal-list *fn-lbr13-payload* fn-arena))
              (fn-lbc (fn-lbc-open-rebuild rows log fn-lbc))
              (reply (fn-lbc-retrieval '(t "fn.test" 1 nil) nil nil :head nil nil 2
                       log fn-lb-vmap fn-arena fn-lbc))
              (line (fn-ag-car (fn-ag-cdr (fn-ag-car (fn-nntp-result-effects reply))))))
        (mv (and (not (fn-lbc-visiblep 0 2 fn-lbc)) (equal (take 3 line) '(52 50 48))) fn-arena fn-lb-vmap fn-lbc))
       (mv ok fn-lb-vmap fn-lbc)))
     (mv ok fn-lbc)))
   ok)))
(with-guard-checking-event t (assert-event (fn-lbzc-native-withdrawn-retrieval-control)))
