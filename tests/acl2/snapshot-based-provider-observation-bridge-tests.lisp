(in-package "ACL2")
(include-book "../../books/snapshot-based-provider-observation-bridge")
(local (include-book "snapshot-based-provider-decoder-lineage-tests"))

; Fixed literal scripts generate observations with the actual demand fields.
; This witness helper supplies literal octets; it is not a source oracle.
(defun-nx fn-obptt-script (recipe c)
  (declare (xargs :measure (acl2-count recipe)))
  (if (consp recipe)
      (let* ((item (car recipe))
             (d (fn-obp-demand c))
             (o (cond ((eq item :quiet) nil)
                      ((eq item :stale)
                       (list :byte (nth 1 d) (nth 2 d) (+ 1 (nth 3 d))
                             (nth 4 d) (nth 5 d) 0))
                      (t (fn-obplt-observe c item)))))
        (cons o (fn-obptt-script (cdr recipe)
                  (fn-obpl-next (fn-obp-tick c o)))))
    nil))
(defun-nx fn-obptt-positive-observations ()
  (fn-obptt-script '(:quiet :stale 0 :quiet 0 0 0 0 0 0 0 :quiet :quiet)
                   (fn-obplt-decoding)))
(defun-nx fn-obptt-corrupt-decoding ()
  (fn-obp-with :decode 4 0 0 '(0 3 0 8)
    (fn-hdc-state :digits 1 0 (list 1 *fn-hrsc-integer-bound* 1)
                  0 0 0 2 3 nil 0 '(1 1))
    nil 3 nil nil 32 (fn-obplt-decoding)))

; Complete actual metadata→decoder→padding→key trajectory with demand and stale supplies.
(defthm fn-obptt-complete-positive
  (let* ((c (fn-obplt-decoding)) (pool '(0 0 0 0 0 0 0 0)) (os (fn-obptt-positive-observations)) (final (fn-obpt-replay os c)) (r (fn-hdc-result (fn-hdc-model-run (fn-obpt-decode-count os c) (fn-omk-at 7 c) pool)))) (and (fn-obpt-observation-tracep os c pool) (fn-obpl-source-lineagep c pool) (equal (fn-omk-at 0 final) :done) (equal (fn-obpt-decode-count os c) 1) (equal (fn-omk-at 7 c) (fn-hdc-begin 0 1 0 '(1 1))) (equal (fn-omk-at 7 final) (fn-hdc-model-run (fn-obpt-decode-count os c) (fn-omk-at 7 c) pool)) (fn-obpl-source-lineagep final pool) (equal (car r) :ok) (equal (fn-omk-at 8 final) (cadr r)) (fn-hrcur-cold-domainp (fn-omk-at 8 final) pool) (fn-hdc-node-in-poolp (fn-omk-at 8 final) (fn-obpl-end final))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (recipe c) (fn-obptt-script recipe c))
                           (:free (observations c) (fn-obpt-replay observations c))
                           (:free (observations c) (fn-obpt-decode-count observations c))
                           (:free (observations c pool) (fn-obpt-observation-tracep observations c pool))
                           (:free (fuel s pool) (fn-hdc-model-run fuel s pool))
                           (:free (bytes c) (fn-obplt-bytes bytes c)))
    :in-theory (enable fn-hrcur-dos-domainp fn-hrcur-widthp fn-hrcur-field fn-hdcl-node-weight fn-hdcl-source-statep fn-hdcl-weighted-statep fn-hdcl-scalar-statep fn-hdcl-borrowed-statep fn-hdcl-numeric-statep fn-hdcl-number-budgetp fn-hdcl-scalar-stackp fn-hdcl-scalar-lineagep fn-hdcl-stack-weight fn-hdcl-payload-charge fn-hdc-node-in-poolp fn-hdc-stack-in-poolp fn-hdc-model-run fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-finish-number fn-hdc-payload-node fn-hdc-state fn-hdc-statep fn-hdc-numberp fn-hrsc-domainp fn-hrsc-codecp fn-scc-atomp fn-scc-nat-encodablep fn-scc-octetp fn-scc-octet-listp fn-obpl-offset fn-obpl-count fn-obpl-end fn-obpl-next fn-obpl-source-lineagep fn-obpl-exact-decode-bytep fn-obp-begin fn-obp-tick fn-obp-cursorp fn-obp-headerp fn-obp-u64s fn-obp-columns-fitp fn-obp-state fn-obp-with fn-obp-size-with fn-obp-refuse fn-obp-demand fn-obp-byte-position fn-obp-cell-put fn-obp-byte-matchp fn-obp-completion fn-omk-at fn-omk-widthp fn-omk-tokenp fn-omk-token-matchp fn-hds-begin fn-hds-feed fn-hdc-result fn-hdc-begin fn-hdc-atom fn-hdc-pair fn-hdc-span fn-hrcur-cold-domainp fn-hdc-built-nodep fn-hdc-abstract fn-obplt-observe fn-obplt-bytes fn-obplt-initial fn-obplt-decoding fn-obplt-finished fn-obplt-change-phase fn-omk-begin fn-omk-message-source fn-omk-node-message fn-odm-at fn-hdc-car fn-hdc-cdr fn-omk-tick fn-hkc-begin fn-obpt-decode-consumesp fn-obpt-replay fn-obpt-decode-count fn-obpt-observation-tracep fn-obptt-script fn-obptt-positive-observations fn-obptt-corrupt-decoding))))

; Argument mutation: same actual scalar observations disagree with the declared immutable pool.
(defthm fn-obptt-remove-exact-trace
  (let* ((c (fn-obplt-decoding)) (pool '(1 0 0 0 0 0 0 0)) (os (fn-obptt-positive-observations)) (final (fn-obpt-replay os c)) (model (fn-hdc-model-run (fn-obpt-decode-count os c) (fn-omk-at 7 c) pool)) (r (fn-hdc-result model))) (and (not (fn-obpt-observation-tracep os c pool)) (fn-obpl-source-lineagep c pool) (equal (fn-omk-at 0 final) :done) (not (equal (fn-omk-at 7 final) model)) (not (and (equal (car r) :ok) (equal (fn-omk-at 8 final) (cadr r)) (fn-hrcur-cold-domainp (fn-omk-at 8 final) pool) (fn-hdc-node-in-poolp (fn-omk-at 8 final) (fn-obpl-end final))))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (recipe c) (fn-obptt-script recipe c))
                           (:free (observations c) (fn-obpt-replay observations c))
                           (:free (observations c) (fn-obpt-decode-count observations c))
                           (:free (observations c pool) (fn-obpt-observation-tracep observations c pool))
                           (:free (fuel s pool) (fn-hdc-model-run fuel s pool))
                           (:free (bytes c) (fn-obplt-bytes bytes c)))
    :in-theory (enable fn-hrcur-dos-domainp fn-hrcur-widthp fn-hrcur-field fn-hdcl-node-weight fn-hdcl-source-statep fn-hdcl-weighted-statep fn-hdcl-scalar-statep fn-hdcl-borrowed-statep fn-hdcl-numeric-statep fn-hdcl-number-budgetp fn-hdcl-scalar-stackp fn-hdcl-scalar-lineagep fn-hdcl-stack-weight fn-hdcl-payload-charge fn-hdc-node-in-poolp fn-hdc-stack-in-poolp fn-hdc-model-run fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-finish-number fn-hdc-payload-node fn-hdc-state fn-hdc-statep fn-hdc-numberp fn-hrsc-domainp fn-hrsc-codecp fn-scc-atomp fn-scc-nat-encodablep fn-scc-octetp fn-scc-octet-listp fn-obpl-offset fn-obpl-count fn-obpl-end fn-obpl-next fn-obpl-source-lineagep fn-obpl-exact-decode-bytep fn-obp-begin fn-obp-tick fn-obp-cursorp fn-obp-headerp fn-obp-u64s fn-obp-columns-fitp fn-obp-state fn-obp-with fn-obp-size-with fn-obp-refuse fn-obp-demand fn-obp-byte-position fn-obp-cell-put fn-obp-byte-matchp fn-obp-completion fn-omk-at fn-omk-widthp fn-omk-tokenp fn-omk-token-matchp fn-hds-begin fn-hds-feed fn-hdc-result fn-hdc-begin fn-hdc-atom fn-hdc-pair fn-hdc-span fn-hrcur-cold-domainp fn-hdc-built-nodep fn-hdc-abstract fn-obplt-observe fn-obplt-bytes fn-obplt-initial fn-obplt-decoding fn-obplt-finished fn-obplt-change-phase fn-omk-begin fn-omk-message-source fn-omk-node-message fn-odm-at fn-hdc-car fn-hdc-cdr fn-omk-tick fn-hkc-begin fn-obpt-decode-consumesp fn-obpt-replay fn-obpt-decode-count fn-obpt-observation-tracep fn-obptt-script fn-obptt-positive-observations fn-obptt-corrupt-decoding))))

; Corrupted-state removal: otherwise structured numeric decoder starts beyond codec potential.
(defthm fn-obptt-remove-initial-lineage
  (let* ((c (fn-obptt-corrupt-decoding)) (pool '(1 1 0 0 0 0 0 0)) (os (fn-obptt-script '(0 :quiet 0 0 0 0 0 :quiet :quiet) c)) (final (fn-obpt-replay os c)) (r (fn-hdc-result (fn-hdc-model-run (fn-obpt-decode-count os c) (fn-omk-at 7 c) pool)))) (and (fn-obpt-observation-tracep os c pool) (not (fn-obpl-source-lineagep c pool)) (equal (fn-omk-at 0 final) :done) (not (fn-obpl-source-lineagep final pool)) (not (and (equal (car r) :ok) (equal (fn-omk-at 8 final) (cadr r)) (fn-hrcur-cold-domainp (fn-omk-at 8 final) pool) (fn-hdc-node-in-poolp (fn-omk-at 8 final) (fn-obpl-end final))))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (recipe c) (fn-obptt-script recipe c))
                           (:free (observations c) (fn-obpt-replay observations c))
                           (:free (observations c) (fn-obpt-decode-count observations c))
                           (:free (observations c pool) (fn-obpt-observation-tracep observations c pool))
                           (:free (fuel s pool) (fn-hdc-model-run fuel s pool))
                           (:free (bytes c) (fn-obplt-bytes bytes c)))
    :in-theory (enable fn-hrcur-dos-domainp fn-hrcur-widthp fn-hrcur-field fn-hdcl-node-weight fn-hdcl-source-statep fn-hdcl-weighted-statep fn-hdcl-scalar-statep fn-hdcl-borrowed-statep fn-hdcl-numeric-statep fn-hdcl-number-budgetp fn-hdcl-scalar-stackp fn-hdcl-scalar-lineagep fn-hdcl-stack-weight fn-hdcl-payload-charge fn-hdc-node-in-poolp fn-hdc-stack-in-poolp fn-hdc-model-run fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-finish-number fn-hdc-payload-node fn-hdc-state fn-hdc-statep fn-hdc-numberp fn-hrsc-domainp fn-hrsc-codecp fn-scc-atomp fn-scc-nat-encodablep fn-scc-octetp fn-scc-octet-listp fn-obpl-offset fn-obpl-count fn-obpl-end fn-obpl-next fn-obpl-source-lineagep fn-obpl-exact-decode-bytep fn-obp-begin fn-obp-tick fn-obp-cursorp fn-obp-headerp fn-obp-u64s fn-obp-columns-fitp fn-obp-state fn-obp-with fn-obp-size-with fn-obp-refuse fn-obp-demand fn-obp-byte-position fn-obp-cell-put fn-obp-byte-matchp fn-obp-completion fn-omk-at fn-omk-widthp fn-omk-tokenp fn-omk-token-matchp fn-hds-begin fn-hds-feed fn-hdc-result fn-hdc-begin fn-hdc-atom fn-hdc-pair fn-hdc-span fn-hrcur-cold-domainp fn-hdc-built-nodep fn-hdc-abstract fn-obplt-observe fn-obplt-bytes fn-obplt-initial fn-obplt-decoding fn-obplt-finished fn-obplt-change-phase fn-omk-begin fn-omk-message-source fn-omk-node-message fn-odm-at fn-hdc-car fn-hdc-cdr fn-omk-tick fn-hkc-begin fn-obpt-decode-consumesp fn-obpt-replay fn-obpt-decode-count fn-obpt-observation-tracep fn-obptt-script fn-obptt-positive-observations fn-obptt-corrupt-decoding))))

; Reachable incomplete prefix: all other completion hypotheses hold, result is still yield.
(defthm fn-obptt-remove-completion-phase
  (let* ((c (fn-obplt-decoding)) (pool '(0 0 0 0 0 0 0 0)) (os nil) (final (fn-obpt-replay os c)) (r (fn-hdc-result (fn-hdc-model-run (fn-obpt-decode-count os c) (fn-omk-at 7 c) pool)))) (and (fn-obpt-observation-tracep os c pool) (fn-obpl-source-lineagep c pool) (not (equal (fn-omk-at 0 final) :done)) (not (and (equal (car r) :ok) (equal (fn-omk-at 8 final) (cadr r)) (fn-hrcur-cold-domainp (fn-omk-at 8 final) pool) (fn-hdc-node-in-poolp (fn-omk-at 8 final) (fn-obpl-end final))))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (recipe c) (fn-obptt-script recipe c))
                           (:free (observations c) (fn-obpt-replay observations c))
                           (:free (observations c) (fn-obpt-decode-count observations c))
                           (:free (observations c pool) (fn-obpt-observation-tracep observations c pool))
                           (:free (fuel s pool) (fn-hdc-model-run fuel s pool))
                           (:free (bytes c) (fn-obplt-bytes bytes c)))
    :in-theory (enable fn-hrcur-dos-domainp fn-hrcur-widthp fn-hrcur-field fn-hdcl-node-weight fn-hdcl-source-statep fn-hdcl-weighted-statep fn-hdcl-scalar-statep fn-hdcl-borrowed-statep fn-hdcl-numeric-statep fn-hdcl-number-budgetp fn-hdcl-scalar-stackp fn-hdcl-scalar-lineagep fn-hdcl-stack-weight fn-hdcl-payload-charge fn-hdc-node-in-poolp fn-hdc-stack-in-poolp fn-hdc-model-run fn-hdc-feed fn-hdc-feed-raw fn-hdc-move fn-hdc-finish-number fn-hdc-payload-node fn-hdc-state fn-hdc-statep fn-hdc-numberp fn-hrsc-domainp fn-hrsc-codecp fn-scc-atomp fn-scc-nat-encodablep fn-scc-octetp fn-scc-octet-listp fn-obpl-offset fn-obpl-count fn-obpl-end fn-obpl-next fn-obpl-source-lineagep fn-obpl-exact-decode-bytep fn-obp-begin fn-obp-tick fn-obp-cursorp fn-obp-headerp fn-obp-u64s fn-obp-columns-fitp fn-obp-state fn-obp-with fn-obp-size-with fn-obp-refuse fn-obp-demand fn-obp-byte-position fn-obp-cell-put fn-obp-byte-matchp fn-obp-completion fn-omk-at fn-omk-widthp fn-omk-tokenp fn-omk-token-matchp fn-hds-begin fn-hds-feed fn-hdc-result fn-hdc-begin fn-hdc-atom fn-hdc-pair fn-hdc-span fn-hrcur-cold-domainp fn-hdc-built-nodep fn-hdc-abstract fn-obplt-observe fn-obplt-bytes fn-obplt-initial fn-obplt-decoding fn-obplt-finished fn-obplt-change-phase fn-omk-begin fn-omk-message-source fn-omk-node-message fn-odm-at fn-hdc-car fn-hdc-cdr fn-omk-tick fn-hkc-begin fn-obpt-decode-consumesp fn-obpt-replay fn-obpt-decode-count fn-obpt-observation-tracep fn-obptt-script fn-obptt-positive-observations fn-obptt-corrupt-decoding))))
