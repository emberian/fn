; Decisions made by the recovery install arm, expressed in the vocabulary
; returned to the replay. The chain length and receipt are inputs here.
(in-package "ACL2")
(include-book "recovery")
(include-book "log-model")
(fn2-book-layer :b)

(defthm fn2-rec-detection-iff-credited-later-receipt
 (iff (eq (nth (fn2-rec-witness-outcome assume witness chain matches)
               *fn2-rec-witness-outcomes*)
          :rollback-detected)
      (and (posp witness)
           (fn2-rec-assumep assume *fn2-rec-assume-frontier*)
           (< chain witness)))
 :hints (("Goal" :in-theory (e/d (fn2-rec-witness-outcome) (fn2-rec-assumep)))))

; A presented receipt in any position suffices. Every earlier conflicting
; receipt has a name too, so the model can report that one first.
(defthm fn2-rec-presented-receipt-conflicts
 (implies (and (member-equal (cons name frontier) witnesses)
               (not (member-equal nil (strip-cars witnesses)))
               (posp frontier) (< (len recovered) frontier))
          (fn2-lm-conflicting-witness witnesses recovered))
 :hints (("Goal" :induct (strip-cars witnesses)))
 :rule-classes nil)

(defthm fn2-rec-detection-has-conflicting-receipt
 (implies (and (eq (nth (fn2-rec-witness-outcome assume witness (len recovered) matches)
                        *fn2-rec-witness-outcomes*)
                   :rollback-detected)
               (member-equal (cons :receipt witness) witnesses)
               (not (member-equal nil (strip-cars witnesses))))
          (and (fn2-rec-assumep assume *fn2-rec-assume-frontier*)
               (fn2-lm-conflicting-witness witnesses recovered)))
 :hints (("Goal" :in-theory nil
                 :use ((:instance fn2-rec-detection-iff-credited-later-receipt
                                  (chain (len recovered)))
                       (:instance fn2-rec-presented-receipt-conflicts
                                  (name :receipt) (frontier witness)))))
 :rule-classes nil)

(defthm fn2-rec-broad-dirty-classification
 (implies (and dirty (not (fn2-rec-assumep assume *fn2-rec-assume-crash-only*)))
          (member-eq (nth (fn2-rec-classify assume dirty ambiguous outcome) *fn2-rec-classes*)
                     '(:unknown :damaged)))
 :hints (("Goal" :in-theory (e/d (fn2-rec-classify) (fn2-rec-assumep)))))

(defthm fn2-rec-dirty-stays-set
 (implies dirty (mv-nth 1 (fn2-rec-dirty left p high dirty fn2-rec-cand)))
 :hints (("Goal" :induct (fn2-rec-dirty left p high dirty fn2-rec-cand)
                 :in-theory (disable fn2-rec-cand-rows fn2-rec-cand-status))))

(defthm fn2-rec-dirty-finds-defective-row
 (implies (and (natp p) (natp left) (natp row)
               (<= p row) (< row (+ p left))
               (< row high) (< row (fn2-rec-cand-rows fn2-rec-cand))
               (not (member-equal (fn2-rec-cand-status row fn2-rec-cand)
                                  (list *fn2-rec-status-empty* *fn2-rec-status-chained*
                                        *fn2-rec-status-payload*))))
          (mv-nth 1 (fn2-rec-dirty left p high dirty fn2-rec-cand)))
 :hints (("Goal" :induct (fn2-rec-dirty left p high dirty fn2-rec-cand)
                 :in-theory (disable fn2-rec-cand-rows fn2-rec-cand-status))))
