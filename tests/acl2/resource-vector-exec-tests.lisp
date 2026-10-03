; Teeth for books/resource-vector-exec (deputy-1, 2026-10-01; Codex review
; r06 F4 and F8): the typed ledger installed from a small profile, a draw
; and its token, a settle, the replayed token :stale, an unrepresentable
; profile REFUSED before any store, the abstraction read back as the
; logical bank and compared, ON THESE VALUES, with the logical transitions.
; Fresh installation now has fn-rl-install-correspondence; the ground
; conjunctive witnesses below check its complete antecedent and conclusion.
; Draw/settle now have general boundary theorems; their witnesses below
; check complete literal premises/conclusions, refusal refinement, and
; labelled corrupted-state hypothesis removals.
(in-package "ACL2")
(include-book "../../books/resource-vector-exec")
(include-book "std/testing/assert-bang" :dir :system)

(defconst *rxt-mib* 1048576)
(defconst *rxt-budget* (list (* 256 *rxt-mib*) (* 4096 *rxt-mib*) 64 8 1000 1000000 100 10000 1000000))
(defconst *rxt-baseline* (list (* 160 *rxt-mib*) 0 1 1 0 0 0 0 0))
(defconst *rxt-reserve* (list (* 16 *rxt-mib*) (* 512 *rxt-mib*) 2 1 0 1 1 0 100000))
(defconst *rxt-read* (list 65536 0 0 0 1 0 0 0 1000))

;; Round 3 regressions on the actual fresh stobj, before the existing trace.
(make-event
 (let ((fresh (fn-rl-freshp fn-resource-ledger)))
   (mv-let (word fn-resource-ledger)
     (fn-rl-install *fn-rv-zero* nil *fn-rv-zero* 2 fn-resource-ledger)
     (if (and fresh (equal word :invalid-draw)
              (fn-rl-freshp fn-resource-ledger))
         (mv nil '(value-triple :nil-baseline-is-invalid-draw) state fn-resource-ledger)
       (mv t nil state fn-resource-ledger)))))

(make-event
 (let ((fresh (fn-rl-freshp fn-resource-ledger)))
   (mv-let (word fn-resource-ledger)
     (fn-rl-install *fn-rv-zero* *fn-rv-zero* *fn-rv-zero* 4294967296 fn-resource-ledger)
     (if (and fresh (equal word :unrepresentable-profile)
              (fn-rl-freshp fn-resource-ledger))
         (mv nil '(value-triple :slot-count-unrepresentable) state fn-resource-ledger)
       (mv t nil state fn-resource-ledger)))))

;; A budget word past u64 is refused by name, and nothing is stored.
(defconst *rxt-too-big* (list (expt 2 64) 0 0 0 0 0 0 0 0))
(assert! (not (fn-rl-words-representable-p *rxt-too-big*)))
(assert! (fn-rl-words-representable-p *rxt-budget*))

(make-event
 (mv-let (w fn-resource-ledger)
   (fn-rl-install *rxt-too-big* *rxt-baseline* *rxt-reserve* 8 fn-resource-ledger)
   (if (and (eq w :unrepresentable-profile)
            (equal (fn-rl-count fn-resource-ledger) 0)
            (equal (fn-rl-budgeti 0 fn-resource-ledger) 0))
       (mv nil '(value-triple :unrepresentable-refused) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

;; A profile the baseline and reserve do not fit is refused before any store.
(make-event
 (mv-let (w fn-resource-ledger)
   (fn-rl-install *rxt-baseline* *rxt-baseline* *rxt-reserve* 8 fn-resource-ledger)
   (if (and (eq w :resources-unavailable) (equal (fn-rl-count fn-resource-ledger) 0))
       (mv nil '(value-triple :unfunded-refused-before-any-store) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

;; The small profile installs; its abstraction is the logical root.
(make-event
 (mv-let (w fn-resource-ledger)
   (fn-rl-install *rxt-budget* *rxt-baseline* *rxt-reserve* 8 fn-resource-ledger)
   (if (and (eq w :installed)
            (fn-rl-wfp fn-resource-ledger)
            (equal (fn-rl-bank fn-resource-ledger)
                   (cadr (fn-rv-install *rxt-budget* *rxt-baseline* *rxt-reserve* 8)))
            (fn-rv-okp (fn-rl-bank fn-resource-ledger)))
       (mv nil '(value-triple :installed-as-the-logical-root) state fn-resource-ledger)
     (mv t nil state fn-resource-ledger))))

;; A second install is refused (:already-installed): the generations are
;; never reset, so no old token can name a new draw (Codex r18 F2).
(make-event
 (let ((before (fn-rl-bank fn-resource-ledger)))
   (mv-let (w fn-resource-ledger)
     (fn-rl-install *rxt-budget* *rxt-baseline* *rxt-reserve* 2 fn-resource-ledger)
     (if (and (eq w :already-installed) (equal (fn-rl-bank fn-resource-ledger) before))
         (mv nil '(value-triple :installs-once) state fn-resource-ledger)
       (mv t nil state fn-resource-ledger)))))

;; A draw at slot 2 answers token 1; the abstraction is the logical draw.
(make-event
 (let ((before (fn-rl-bank fn-resource-ledger)))
   (mv-let (w g fn-resource-ledger)
     (fn-rl-draw 2 *rxt-read* fn-resource-ledger)
     (if (and (eq w :drawn) (equal g 1)
              (equal (fn-rl-bank fn-resource-ledger) (cadr (fn-rv-draw before 2 *rxt-read*)))
              (equal g (caddr (fn-rv-draw before 2 *rxt-read*))))
         (mv nil '(value-triple :drawn-as-the-logical-draw) state fn-resource-ledger)
       (mv t nil state fn-resource-ledger)))))

;; The settle with its token; the replayed token after a second draw is
;; :stale and changes nothing.
(make-event
 (let ((before (fn-rl-bank fn-resource-ledger)))
   (mv-let (w fn-resource-ledger)
     (fn-rl-settle 2 1 fn-resource-ledger)
     (if (and (eq w :settled)
              (equal (fn-rl-bank fn-resource-ledger) (cadr (fn-rv-settle before 2 1))))
         (mv nil '(value-triple :settled-as-the-logical-settle) state fn-resource-ledger)
       (mv t nil state fn-resource-ledger)))))

(make-event
 (mv-let (w g fn-resource-ledger)
   (fn-rl-draw 2 *rxt-read* fn-resource-ledger)
   (let ((again (fn-rl-bank fn-resource-ledger)))
     (mv-let (w2 fn-resource-ledger)
       (fn-rl-settle 2 1 fn-resource-ledger)
       (if (and (eq w :drawn) (equal g 2) (eq w2 :stale)
                (equal (fn-rl-bank fn-resource-ledger) again))
           (mv nil '(value-triple :replayed-token-stale) state fn-resource-ledger)
         (mv t nil state fn-resource-ledger))))))

;; Ground witnesses use theorem contexts because ACL2 permits the stobj
;; creator and complete logical ledger equality there. Each is a conjunction,
;; never a vacuous implication of the antecedent: all antecedents are asserted
;; together with the literal correspondence conclusion and the expected word.
;; They are concrete checks, not substitutes for the book's general theorem.

(defthm rxt-install-correspondence-installed-witness
  (let* ((ledger (create-fn-resource-ledger))
         (budget *rxt-budget*) (baseline *rxt-baseline*) (reserve *rxt-reserve*) (nslots 8)
         (result (fn-rl-install budget baseline reserve nslots ledger))
         (word (mv-nth 0 result))
         (after (mv-nth 1 result)))
    (and (fn-rl-freshp ledger)
         (true-listp budget) (true-listp baseline) (true-listp reserve)
         (natp nslots)
         (equal word :installed)
         (fn-rl-profile-representable-p budget nslots)
         (equal word
                (if (fn-rl-profile-representable-p budget nslots)
                    (car (fn-rv-install budget baseline reserve nslots))
                  :unrepresentable-profile))
         (implies (equal word :installed)
                  (equal (fn-rl-bank after)
                         (cadr (fn-rv-install budget baseline reserve nslots))))
         (implies (not (equal word :installed)) (equal after ledger))))
  :rule-classes nil)

(defthm rxt-install-correspondence-nil-baseline-witness
  (let* ((ledger (create-fn-resource-ledger))
         (budget *fn-rv-zero*) (baseline nil) (reserve *fn-rv-zero*) (nslots 2)
         (result (fn-rl-install budget baseline reserve nslots ledger))
         (word (mv-nth 0 result))
         (after (mv-nth 1 result)))
    (and (fn-rl-freshp ledger)
         (true-listp budget) (true-listp baseline) (true-listp reserve)
         (natp nslots)
         (equal word :invalid-draw)
         (fn-rl-profile-representable-p budget nslots)
         (equal word
                (if (fn-rl-profile-representable-p budget nslots)
                    (car (fn-rv-install budget baseline reserve nslots))
                  :unrepresentable-profile))
         (implies (equal word :installed)
                  (equal (fn-rl-bank after)
                         (cadr (fn-rv-install budget baseline reserve nslots))))
         (implies (not (equal word :installed)) (equal after ledger))))
  :rule-classes nil)

(defthm rxt-install-correspondence-unfunded-witness
  (let* ((ledger (create-fn-resource-ledger))
         (budget *rxt-baseline*) (baseline *rxt-baseline*) (reserve *rxt-reserve*) (nslots 8)
         (result (fn-rl-install budget baseline reserve nslots ledger))
         (word (mv-nth 0 result))
         (after (mv-nth 1 result)))
    (and (fn-rl-freshp ledger)
         (true-listp budget) (true-listp baseline) (true-listp reserve)
         (natp nslots)
         (equal word :resources-unavailable)
         (fn-rl-profile-representable-p budget nslots)
         (equal word
                (if (fn-rl-profile-representable-p budget nslots)
                    (car (fn-rv-install budget baseline reserve nslots))
                  :unrepresentable-profile))
         (implies (equal word :installed)
                  (equal (fn-rl-bank after)
                         (cadr (fn-rv-install budget baseline reserve nslots))))
         (implies (not (equal word :installed)) (equal after ledger))))
  :rule-classes nil)

(defthm rxt-install-correspondence-slot-count-witness
  (let* ((ledger (create-fn-resource-ledger))
         (budget *fn-rv-zero*) (baseline *fn-rv-zero*) (reserve *fn-rv-zero*) (nslots 4294967296)
         (result (fn-rl-install budget baseline reserve nslots ledger))
         (word (mv-nth 0 result))
         (after (mv-nth 1 result)))
    (and (fn-rl-freshp ledger)
         (true-listp budget) (true-listp baseline) (true-listp reserve)
         (natp nslots)
         (equal word :unrepresentable-profile)
         (not (fn-rl-profile-representable-p budget nslots))
         (equal word
                (if (fn-rl-profile-representable-p budget nslots)
                    (car (fn-rv-install budget baseline reserve nslots))
                  :unrepresentable-profile))
         (implies (equal word :installed)
                  (equal (fn-rl-bank after)
                         (cadr (fn-rv-install budget baseline reserve nslots))))
         (implies (not (equal word :installed)) (equal after ledger))))
  :rule-classes nil
  ;; Do not execute the enormous logical table, even during simplification.
  ;; The representation exception excludes that branch of the conclusion.
  :hints (("Goal" :in-theory (disable fn-rv-install
                                     (:executable-counterpart fn-rv-install)))))

(defthm rxt-install-correspondence-budget-word-witness
  (let* ((ledger (create-fn-resource-ledger))
         (budget *rxt-too-big*) (baseline *rxt-baseline*) (reserve *rxt-reserve*) (nslots 8)
         (result (fn-rl-install budget baseline reserve nslots ledger))
         (word (mv-nth 0 result))
         (after (mv-nth 1 result)))
    (and (fn-rl-freshp ledger)
         (true-listp budget) (true-listp baseline) (true-listp reserve)
         (natp nslots)
         (equal word :unrepresentable-profile)
         (not (fn-rl-profile-representable-p budget nslots))
         (equal word
                (if (fn-rl-profile-representable-p budget nslots)
                    (car (fn-rv-install budget baseline reserve nslots))
                  :unrepresentable-profile))
         (implies (equal word :installed)
                  (equal (fn-rl-bank after)
                         (cadr (fn-rv-install budget baseline reserve nslots))))
         (implies (not (equal word :installed)) (equal after ledger))))
  :rule-classes nil)

(defthm rxt-install-preflight-charges-witness
  (let* ((ledger (create-fn-resource-ledger))
         (budget *rxt-budget*) (baseline *rxt-baseline*) (reserve *rxt-reserve*)
         (nslots 8)
         (stored (fn-rl-store-words-from 0 budget (fn-rl-resize-all nslots ledger)))
         (first (fn-rl-draw 0 baseline stored))
         (second (fn-rl-open 1 reserve (mv-nth 2 first))))
    (and (fn-rl-freshp ledger)
         (true-listp budget) (true-listp baseline) (true-listp reserve)
         (natp nslots)
         (fn-rl-profile-representable-p budget nslots)
         (equal (car (fn-rv-install budget baseline reserve nslots)) :installed)
         (equal (mv-nth 0 first) :drawn)
         (equal (mv-nth 0 second) :opened)))
  :rule-classes nil)

; General representation/receipt preservation teeth. Removals below name
; corrupted states and affirm every retained hypothesis and failed conclusion.
(defthm rxt-draw-representation-and-receipts-witness
 (let* ((ledger (update-fn-rl-worker-outcome 0 (update-fn-rl-worker-physical 1 (update-fn-rl-worker-operation 13 (update-fn-rl-worker-resident 7 (mv-nth 1 (fn-rl-install (list 10 0 0 1 1 0 0 0 5) *fn-rv-zero* *fn-rv-zero* 3 (create-fn-resource-ledger))))))))
        (result (fn-rl-draw 2 (list 2 0 0 1 1 0 0 0 3) ledger))
        (after (mv-nth 2 result)))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger)
       (equal (mv-nth 0 result) :drawn) (equal (mv-nth 1 result) 1)
       (fn-resource-ledgerp after) (fn-rl-wfp after)
       (equal (fn-rl-worker-resident after) (fn-rl-worker-resident ledger))
       (equal (fn-rl-worker-operation after) (fn-rl-worker-operation ledger))
       (equal (fn-rl-worker-physical after) (fn-rl-worker-physical ledger))
       (equal (fn-rl-worker-outcome after) (fn-rl-worker-outcome ledger))))
 :rule-classes nil)

(defthm rxt-settle-representation-and-receipts-witness
 (let* ((before (update-fn-rl-worker-outcome 0 (update-fn-rl-worker-physical 1 (update-fn-rl-worker-operation 13 (update-fn-rl-worker-resident 7 (mv-nth 1 (fn-rl-install (list 10 0 0 1 1 0 0 0 5) *fn-rv-zero* *fn-rv-zero* 3 (create-fn-resource-ledger))))))))
        (ledger (mv-nth 2 (fn-rl-draw 2 (list 2 0 0 1 1 0 0 0 3) before)))
        (result (fn-rl-settle 2 1 ledger))
        (after (mv-nth 1 result)))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger)
       (equal (mv-nth 0 result) :settled)
       (fn-resource-ledgerp after) (fn-rl-wfp after)
       (equal (fn-rl-worker-resident after) (fn-rl-worker-resident ledger))
       (equal (fn-rl-worker-operation after) (fn-rl-worker-operation ledger))
       (equal (fn-rl-worker-physical after) (fn-rl-worker-physical ledger))
       (equal (fn-rl-worker-outcome after) (fn-rl-worker-outcome ledger))))
 :rule-classes nil)

(defthm rxt-draw-representation-without-type-corrupted-state-witness
 (let* ((ledger (update-nth 0 nil (create-fn-resource-ledger))) (after (mv-nth 2 (fn-rl-draw 0 nil ledger))))
  (and (and (not (fn-resource-ledgerp ledger)) (fn-rl-wfp ledger))
       (not (and (fn-resource-ledgerp after) (fn-rl-wfp after)))))
 :rule-classes nil)

(defthm rxt-draw-representation-without-shape-corrupted-state-witness
 (let* ((ledger (update-fn-rl-count 1 (create-fn-resource-ledger))) (after (mv-nth 2 (fn-rl-draw 0 nil ledger))))
  (and (and (fn-resource-ledgerp ledger) (not (fn-rl-wfp ledger)))
       (not (and (fn-resource-ledgerp after) (fn-rl-wfp after)))))
 :rule-classes nil)

(defthm rxt-settle-representation-without-type-corrupted-state-witness
 (let* ((ledger (update-nth 0 nil (create-fn-resource-ledger))) (after (mv-nth 1 (fn-rl-settle 0 1 ledger))))
  (and (and (not (fn-resource-ledgerp ledger)) (fn-rl-wfp ledger))
       (not (and (fn-resource-ledgerp after) (fn-rl-wfp after)))))
 :rule-classes nil)

(defthm rxt-settle-representation-without-shape-corrupted-state-witness
 (let* ((ledger (update-fn-rl-count 1 (create-fn-resource-ledger))) (after (mv-nth 1 (fn-rl-settle 0 1 ledger))))
  (and (and (fn-resource-ledgerp ledger) (not (fn-rl-wfp ledger)))
       (not (and (fn-resource-ledgerp after) (fn-rl-wfp after)))))
 :rule-classes nil)

(defthm rxt-noncanonical-demand-refused-witness
 (let* ((ledger (update-fn-rl-worker-outcome 0 (update-fn-rl-worker-physical 1 (update-fn-rl-worker-operation 13 (update-fn-rl-worker-resident 7 (mv-nth 1 (fn-rl-install (list 10 0 0 1 1 0 0 0 5) *fn-rv-zero* *fn-rv-zero* 3 (create-fn-resource-ledger))))))))
        (result (fn-rl-draw 2 '(2 . 3) ledger)))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger)
       (not (true-listp '(2 . 3)))
       (equal (mv-nth 0 result) :invalid-draw)
       (equal (mv-nth 1 result) 0) (equal (mv-nth 2 result) ledger)
       (fn-resource-ledgerp (mv-nth 2 result)) (fn-rl-wfp (mv-nth 2 result))))
 :rule-classes nil)

(defthm rxt-exhausted-generation-refused-witness
 (let* ((ledger (update-fn-rl-gensi 2 *fn-rl-word-max* (update-fn-rl-worker-outcome 0 (update-fn-rl-worker-physical 1 (update-fn-rl-worker-operation 13 (update-fn-rl-worker-resident 7 (mv-nth 1 (fn-rl-install (list 10 0 0 1 1 0 0 0 5) *fn-rv-zero* *fn-rv-zero* 3 (create-fn-resource-ledger)))))))))
        (result (fn-rl-draw 2 (list 2 0 0 1 1 0 0 0 3) ledger)))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger)
       (equal (mv-nth 0 result) :slot-exhausted)
       (equal (mv-nth 1 result) 0) (equal (mv-nth 2 result) ledger)
       (equal (fn-rl-gensi 2 (mv-nth 2 result)) *fn-rl-word-max*)))
 :rule-classes nil)

; Literal boundary teeth; removals are corrupted-state witnesses.

(defthm rxt-draw-correspondence-accepted-witness
 (let* ((ledger (mv-nth 1 (fn-rl-install (list 10 0 0 1 1 0 0 0 5) *fn-rv-zero* *fn-rv-zero* 3 (create-fn-resource-ledger)))) (slot 2) (demand (list 2 0 0 1 1 0 0 0 3))
        (bank (fn-rl-bank ledger)) (logical (fn-rv-draw bank slot demand))
        (result (fn-rl-draw slot demand ledger))
        (word (mv-nth 0 result)) (token (mv-nth 1 result)) (after (mv-nth 2 result)))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger) (equal word :drawn) (equal token 1)
       (and
    (equal word (if (and (equal (car logical) :drawn)
                        (<= *fn-rl-word-max* (fn-rv-gen slot bank)))
                    :slot-exhausted (car logical)))
    (equal token (if (equal word :drawn) (caddr logical) 0))
    (equal (fn-rl-bank after) (if (equal word :drawn) (cadr logical) bank))
    (implies (not (equal word :drawn)) (equal after ledger)))))
 :rule-classes nil)

(defthm rxt-draw-correspondence-busy-witness
 (let* ((ledger (mv-nth 2 (fn-rl-draw 2 (list 2 0 0 1 1 0 0 0 3) (mv-nth 1 (fn-rl-install (list 10 0 0 1 1 0 0 0 5) *fn-rv-zero* *fn-rv-zero* 3 (create-fn-resource-ledger)))))) (slot 2) (demand (list 2 0 0 1 1 0 0 0 3))
        (bank (fn-rl-bank ledger)) (logical (fn-rv-draw bank slot demand))
        (result (fn-rl-draw slot demand ledger))
        (word (mv-nth 0 result)) (token (mv-nth 1 result)) (after (mv-nth 2 result)))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger) (equal word :slot-busy) (equal token 0)
       (and
    (equal word (if (and (equal (car logical) :drawn)
                        (<= *fn-rl-word-max* (fn-rv-gen slot bank)))
                    :slot-exhausted (car logical)))
    (equal token (if (equal word :drawn) (caddr logical) 0))
    (equal (fn-rl-bank after) (if (equal word :drawn) (cadr logical) bank))
    (implies (not (equal word :drawn)) (equal after ledger)))))
 :rule-classes nil)

(defthm rxt-draw-correspondence-unfunded-witness
 (let* ((ledger (mv-nth 1 (fn-rl-install (list 10 0 0 1 1 0 0 0 5) *fn-rv-zero* *fn-rv-zero* 3 (create-fn-resource-ledger)))) (slot 2) (demand (list 11 0 0 0 0 0 0 0 0))
        (bank (fn-rl-bank ledger)) (logical (fn-rv-draw bank slot demand))
        (result (fn-rl-draw slot demand ledger))
        (word (mv-nth 0 result)) (token (mv-nth 1 result)) (after (mv-nth 2 result)))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger) (equal word :resources-unavailable) (equal token 0)
       (and
    (equal word (if (and (equal (car logical) :drawn)
                        (<= *fn-rl-word-max* (fn-rv-gen slot bank)))
                    :slot-exhausted (car logical)))
    (equal token (if (equal word :drawn) (caddr logical) 0))
    (equal (fn-rl-bank after) (if (equal word :drawn) (cadr logical) bank))
    (implies (not (equal word :drawn)) (equal after ledger)))))
 :rule-classes nil)

(defthm rxt-draw-correspondence-noncanonical-witness
 (let* ((ledger (mv-nth 1 (fn-rl-install (list 10 0 0 1 1 0 0 0 5) *fn-rv-zero* *fn-rv-zero* 3 (create-fn-resource-ledger)))) (slot 2) (demand '(2 . 3))
        (bank (fn-rl-bank ledger)) (logical (fn-rv-draw bank slot demand))
        (result (fn-rl-draw slot demand ledger))
        (word (mv-nth 0 result)) (token (mv-nth 1 result)) (after (mv-nth 2 result)))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger) (equal word :invalid-draw) (not (true-listp '(2 . 3)))
       (and
    (equal word (if (and (equal (car logical) :drawn)
                        (<= *fn-rl-word-max* (fn-rv-gen slot bank)))
                    :slot-exhausted (car logical)))
    (equal token (if (equal word :drawn) (caddr logical) 0))
    (equal (fn-rl-bank after) (if (equal word :drawn) (cadr logical) bank))
    (implies (not (equal word :drawn)) (equal after ledger)))))
 :rule-classes nil)

(defthm rxt-draw-correspondence-invalid-slot-witness
 (let* ((ledger (mv-nth 1 (fn-rl-install (list 10 0 0 1 1 0 0 0 5) *fn-rv-zero* *fn-rv-zero* 3 (create-fn-resource-ledger)))) (slot -1) (demand (list 2 0 0 1 1 0 0 0 3))
        (bank (fn-rl-bank ledger)) (logical (fn-rv-draw bank slot demand))
        (result (fn-rl-draw slot demand ledger))
        (word (mv-nth 0 result)) (token (mv-nth 1 result)) (after (mv-nth 2 result)))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger) (equal word :invalid-draw) (not (natp slot))
       (and
    (equal word (if (and (equal (car logical) :drawn)
                        (<= *fn-rl-word-max* (fn-rv-gen slot bank)))
                    :slot-exhausted (car logical)))
    (equal token (if (equal word :drawn) (caddr logical) 0))
    (equal (fn-rl-bank after) (if (equal word :drawn) (cadr logical) bank))
    (implies (not (equal word :drawn)) (equal after ledger)))))
 :rule-classes nil)

(defthm rxt-draw-correspondence-exhausted-witness
 (let* ((ledger (update-fn-rl-gensi 2 *fn-rl-word-max* (mv-nth 1 (fn-rl-install (list 10 0 0 1 1 0 0 0 5) *fn-rv-zero* *fn-rv-zero* 3 (create-fn-resource-ledger))))) (slot 2) (demand (list 2 0 0 1 1 0 0 0 3))
        (bank (fn-rl-bank ledger)) (logical (fn-rv-draw bank slot demand))
        (result (fn-rl-draw slot demand ledger))
        (word (mv-nth 0 result)) (token (mv-nth 1 result)) (after (mv-nth 2 result)))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger) (equal word :slot-exhausted) (equal (car logical) :drawn) (equal (caddr logical) (+ 1 *fn-rl-word-max*)) (equal token 0) (equal (fn-rl-gensi slot after) *fn-rl-word-max*)
       (and
    (equal word (if (and (equal (car logical) :drawn)
                        (<= *fn-rl-word-max* (fn-rv-gen slot bank)))
                    :slot-exhausted (car logical)))
    (equal token (if (equal word :drawn) (caddr logical) 0))
    (equal (fn-rl-bank after) (if (equal word :drawn) (cadr logical) bank))
    (implies (not (equal word :drawn)) (equal after ledger)))))
 :rule-classes nil)

(defthm rxt-settle-correspondence-accepted-witness
 (let* ((ledger (mv-nth 2 (fn-rl-draw 2 (list 2 0 0 1 1 0 0 0 3) (mv-nth 1 (fn-rl-install (list 10 0 0 1 1 0 0 0 5) *fn-rv-zero* *fn-rv-zero* 3 (create-fn-resource-ledger)))))) (slot 2) (gen 1)
        (logical (fn-rv-settle (fn-rl-bank ledger) slot gen))
        (result (fn-rl-settle slot gen ledger))
        (word (mv-nth 0 result)) (after (mv-nth 1 result)))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger) (equal word :settled)
       (and (equal word (car logical))
       (equal (fn-rl-bank after) (cadr logical))
       (implies (not (equal word :settled)) (equal after ledger)))))
 :rule-classes nil)

(defthm rxt-settle-correspondence-stale-witness
 (let* ((ledger (mv-nth 2 (fn-rl-draw 2 (list 2 0 0 1 1 0 0 0 3) (mv-nth 1 (fn-rl-install (list 10 0 0 1 1 0 0 0 5) *fn-rv-zero* *fn-rv-zero* 3 (create-fn-resource-ledger)))))) (slot 2) (gen 0)
        (logical (fn-rv-settle (fn-rl-bank ledger) slot gen))
        (result (fn-rl-settle slot gen ledger))
        (word (mv-nth 0 result)) (after (mv-nth 1 result)))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger) (equal word :stale)
       (and (equal word (car logical))
       (equal (fn-rl-bank after) (cadr logical))
       (implies (not (equal word :settled)) (equal after ledger)))))
 :rule-classes nil)

(defthm rxt-settle-correspondence-invalid-slot-witness
 (let* ((ledger (mv-nth 1 (fn-rl-install (list 10 0 0 1 1 0 0 0 5) *fn-rv-zero* *fn-rv-zero* 3 (create-fn-resource-ledger)))) (slot 3) (gen 0)
        (logical (fn-rv-settle (fn-rl-bank ledger) slot gen))
        (result (fn-rl-settle slot gen ledger))
        (word (mv-nth 0 result)) (after (mv-nth 1 result)))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger) (equal word :invalid-slot)
       (and (equal word (car logical))
       (equal (fn-rl-bank after) (cadr logical))
       (implies (not (equal word :settled)) (equal after ledger)))))
 :rule-classes nil)

(defthm rxt-draw-correspondence-without-type-corrupted-state-witness
 (let* ((ledger (update-fn-rl-budgeti 0 -1 (mv-nth 1 (fn-rl-install (list 10 0 0 1 1 0 0 0 5) *fn-rv-zero* *fn-rv-zero* 3 (create-fn-resource-ledger))))) (slot 2) (demand *fn-rv-zero*)
        (bank (fn-rl-bank ledger)) (logical (fn-rv-draw bank slot demand))
        (result (fn-rl-draw slot demand ledger))
        (word (mv-nth 0 result)) (token (mv-nth 1 result)) (after (mv-nth 2 result)))
  (and (not (fn-resource-ledgerp ledger)) (fn-rl-wfp ledger)
       (not (and
    (equal word (if (and (equal (car logical) :drawn)
                        (<= *fn-rl-word-max* (fn-rv-gen slot bank)))
                    :slot-exhausted (car logical)))
    (equal token (if (equal word :drawn) (caddr logical) 0))
    (equal (fn-rl-bank after) (if (equal word :drawn) (cadr logical) bank))
    (implies (not (equal word :drawn)) (equal after ledger))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d
   (fn-rl-rows-from fn-rl-demand-list fn-rv-draw fn-rv-charge
    fn-rv-gen fn-rv-phase fn-rv-slotp fn-rv-settle fn-rv-drawnp fn-rl-release-from)
   ((:executable-counterpart fn-rl-rows-from)
    (:executable-counterpart fn-rl-release-from)
    (:definition nth) (:definition update-nth))))))

(defthm rxt-draw-correspondence-without-shape-corrupted-state-witness
 (let* ((ledger (update-fn-rl-count 1 (create-fn-resource-ledger))) (slot 0) (demand *fn-rv-zero*)
        (bank (fn-rl-bank ledger)) (logical (fn-rv-draw bank slot demand))
        (result (fn-rl-draw slot demand ledger))
        (word (mv-nth 0 result)) (token (mv-nth 1 result)) (after (mv-nth 2 result)))
  (and (fn-resource-ledgerp ledger) (not (fn-rl-wfp ledger))
       (not (and
    (equal word (if (and (equal (car logical) :drawn)
                        (<= *fn-rl-word-max* (fn-rv-gen slot bank)))
                    :slot-exhausted (car logical)))
    (equal token (if (equal word :drawn) (caddr logical) 0))
    (equal (fn-rl-bank after) (if (equal word :drawn) (cadr logical) bank))
    (implies (not (equal word :drawn)) (equal after ledger))))))
 :rule-classes nil
 :hints (("Goal" :expand ((fn-rl-rows-from 0 '((0 0 0 0 0 0 0 0 0) (0 0 0 0 0 0 0 0 0) 1 nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil 0 0 0 0 0 0 0 0 0 0)) (fn-rl-rows-from 1 '((0 0 0 0 0 0 0 0 0) (0 0 0 0 0 0 0 0 0) 1 nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil 0 0 0 0 0 0 0 0 0 0))) :in-theory (e/d
   (fn-rl-rows-from fn-rl-demand-list fn-rv-draw fn-rv-charge
    fn-rv-gen fn-rv-phase fn-rv-slotp fn-rv-settle fn-rv-drawnp fn-rl-release-from)
   ((:executable-counterpart fn-rl-rows-from)
    (:executable-counterpart fn-rl-release-from)
    (:definition nth) (:definition update-nth))))))

(defthm rxt-settle-correspondence-without-type-corrupted-state-witness
 (let* ((ledger (update-fn-rl-gensi 2 -1 (mv-nth 2 (fn-rl-draw 2 (list 2 0 0 1 1 0 0 0 3) (mv-nth 1 (fn-rl-install (list 10 0 0 1 1 0 0 0 5) *fn-rv-zero* *fn-rv-zero* 3 (create-fn-resource-ledger))))))) (slot 2) (gen -1)
        (logical (fn-rv-settle (fn-rl-bank ledger) slot gen))
        (result (fn-rl-settle slot gen ledger))
        (word (mv-nth 0 result)) (after (mv-nth 1 result)))
  (and (not (fn-resource-ledgerp ledger)) (fn-rl-wfp ledger)
       (not (and (equal word (car logical))
       (equal (fn-rl-bank after) (cadr logical))
       (implies (not (equal word :settled)) (equal after ledger))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d
   (fn-rl-rows-from fn-rl-demand-list fn-rv-draw fn-rv-charge
    fn-rv-gen fn-rv-phase fn-rv-slotp fn-rv-settle fn-rv-drawnp fn-rl-release-from)
   ((:executable-counterpart fn-rl-rows-from)
    (:executable-counterpart fn-rl-release-from)
    (:definition nth) (:definition update-nth))))))

(defthm rxt-settle-correspondence-without-shape-corrupted-state-witness
 (let* ((ledger (update-fn-rl-count 1 (update-fn-rl-phasesi 0 1 (create-fn-resource-ledger)))) (slot 0) (gen 0)
        (logical (fn-rv-settle (fn-rl-bank ledger) slot gen))
        (result (fn-rl-settle slot gen ledger))
        (word (mv-nth 0 result)) (after (mv-nth 1 result)))
  (and (fn-resource-ledgerp ledger) (not (fn-rl-wfp ledger))
       (not (and (equal word (car logical))
       (equal (fn-rl-bank after) (cadr logical))
       (implies (not (equal word :settled)) (equal after ledger))))))
 :rule-classes nil
 :hints (("Goal" :expand ((fn-rl-rows-from 0 '((0 0 0 0 0 0 0 0 0) (0 0 0 0 0 0 0 0 0) 1 (1) nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil 0 0 0 0 0 0 0 0 0 0)) (fn-rl-rows-from 1 '((0 0 0 0 0 0 0 0 0) (0 0 0 0 0 0 0 0 0) 1 (1) nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil nil 0 0 0 0 0 0 0 0 0 0))) :in-theory (e/d
   (fn-rl-rows-from fn-rl-demand-list fn-rv-draw fn-rv-charge
    fn-rv-gen fn-rv-phase fn-rv-slotp fn-rv-settle fn-rv-drawnp fn-rl-release-from)
   ((:executable-counterpart fn-rl-rows-from)
    (:executable-counterpart fn-rl-release-from)
    (:definition nth) (:definition update-nth))))))

(defthm rxt-draw-keeps-okp-witness
 (let* ((ledger (mv-nth 1 (fn-rl-install (list 10 0 0 1 1 0 0 0 5) *fn-rv-zero* *fn-rv-zero* 3 (create-fn-resource-ledger)))) (after (mv-nth 2 (fn-rl-draw 2 (list 2 0 0 1 1 0 0 0 3) ledger))))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger) (fn-rv-okp (fn-rl-bank ledger)) (fn-rv-okp (fn-rl-bank after))))
 :rule-classes nil)

(defthm rxt-settle-keeps-okp-witness
 (let* ((ledger (mv-nth 2 (fn-rl-draw 2 (list 2 0 0 1 1 0 0 0 3) (mv-nth 1 (fn-rl-install (list 10 0 0 1 1 0 0 0 5) *fn-rv-zero* *fn-rv-zero* 3 (create-fn-resource-ledger)))))) (after (mv-nth 1 (fn-rl-settle 2 1 ledger))))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger) (fn-rv-okp (fn-rl-bank ledger)) (fn-rv-okp (fn-rl-bank after))
       (equal (fn-rl-drawn-list after) (list 0 0 0 0 1 0 0 0 3))
       (equal (fn-rl-demand-list 2 after) *fn-rv-zero*)))
 :rule-classes nil)

(defthm rxt-draw-keeps-okp-without-okp-corrupted-state-witness
 (let* ((ledger (update-fn-rl-drawni 0 11 (mv-nth 1 (fn-rl-install (list 10 0 0 1 1 0 0 0 5) *fn-rv-zero* *fn-rv-zero* 3 (create-fn-resource-ledger))))) (after (mv-nth 2 (fn-rl-draw 2 (list 2 0 0 1 1 0 0 0 3) ledger))))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger) (not (fn-rv-okp (fn-rl-bank ledger))) (not (fn-rv-okp (fn-rl-bank after)))))
 :rule-classes nil)

(defthm rxt-settle-keeps-okp-without-okp-corrupted-state-witness
 (let* ((ledger (update-fn-rl-drawni 0 11 (mv-nth 1 (fn-rl-install (list 10 0 0 1 1 0 0 0 5) *fn-rv-zero* *fn-rv-zero* 3 (create-fn-resource-ledger))))) (after (mv-nth 1 (fn-rl-settle 2 1 ledger))))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger) (not (fn-rv-okp (fn-rl-bank ledger))) (not (fn-rv-okp (fn-rl-bank after)))))
 :rule-classes nil)

(defthm rxt-draw-refusal-without-refusal-witness
 (let* ((ledger (mv-nth 1 (fn-rl-install (list 10 0 0 1 1 0 0 0 5) *fn-rv-zero* *fn-rv-zero* 3 (create-fn-resource-ledger)))) (result (fn-rl-draw 2 (list 2 0 0 1 1 0 0 0 3) ledger)))
  (and (equal (mv-nth 0 result) :drawn) (not (equal (mv-nth 2 result) ledger))))
 :rule-classes nil)

(defthm rxt-settle-refusal-without-refusal-witness
 (let* ((ledger (mv-nth 2 (fn-rl-draw 2 (list 2 0 0 1 1 0 0 0 3) (mv-nth 1 (fn-rl-install (list 10 0 0 1 1 0 0 0 5) *fn-rv-zero* *fn-rv-zero* 3 (create-fn-resource-ledger)))))) (result (fn-rl-settle 2 1 ledger)))
  (and (equal (mv-nth 0 result) :settled) (not (equal (mv-nth 1 result) ledger))))
 :rule-classes nil)

; Bootstrap representation teeth, over all logical arguments of the export.
(defthm rxt-install-keeps-representation-witness
 (let* ((ledger (create-fn-resource-ledger))
        (result (fn-rl-install (list 10 0 0 1 1 0 0 0 5)
                              *fn-rv-zero* *fn-rv-zero* 3 ledger))
        (after (mv-nth 1 result)))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger)
       (equal (mv-nth 0 result) :installed)
       (fn-resource-ledgerp after) (fn-rl-wfp after)))
 :rule-classes nil)

(defthm rxt-install-keeps-representation-noncanonical-profile-witness
 (let* ((ledger (create-fn-resource-ledger))
        (result (fn-rl-install '(2 . 3) nil nil 'invalid ledger))
        (after (mv-nth 1 result)))
  (and (fn-resource-ledgerp ledger) (fn-rl-wfp ledger)
       (not (true-listp '(2 . 3))) (not (natp 'invalid))
       (equal (mv-nth 0 result) :unrepresentable-profile)
       (equal after ledger) (fn-resource-ledgerp after) (fn-rl-wfp after)))
 :rule-classes nil)

(defthm rxt-install-representation-without-type-corrupted-state-witness
 (let* ((ledger (update-nth 0 nil (create-fn-resource-ledger)))
        (after (mv-nth 1 (fn-rl-install nil nil nil 0 ledger))))
  (and (not (fn-resource-ledgerp ledger)) (fn-rl-wfp ledger)
       (not (and (fn-resource-ledgerp after) (fn-rl-wfp after)))))
 :rule-classes nil)

(defthm rxt-install-representation-without-shape-corrupted-state-witness
 (let* ((ledger (update-fn-rl-count 1 (create-fn-resource-ledger)))
        (after (mv-nth 1 (fn-rl-install nil nil nil 0 ledger))))
  (and (fn-resource-ledgerp ledger) (not (fn-rl-wfp ledger))
       (not (and (fn-resource-ledgerp after) (fn-rl-wfp after)))))
 :rule-classes nil)
