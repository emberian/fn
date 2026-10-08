; Reachable lifecycle witnesses, premise removals, and an over-refund mutant.
(in-package "ACL2")
(include-book "../../books/page-read-ledger-rowsum")
(include-book "../../books/defkeystone")

(defconst *rs-budget* '(100 100 10 10 100))
(defconst *rs-empty* (fn-prl-make *rs-budget*))
(defconst *rs-registered*
  (nth 1 (mv-list 2 (fn-prl-register *rs-empty* 1 '(2 0 1 0 0)))))
(defconst *rs-reserved*
  (nth 2 (mv-list 3 (fn-prl-reserve-growth *rs-registered* 7))))
(defconst *rs-reserve-token*
  (nth 1 (mv-list 3 (fn-prl-reserve-growth *rs-registered* 7))))
(defconst *rs-issued*
  (nth 2 (mv-list 3 (fn-prl-admit *rs-reserved* 2 1 0 4 0
                                  '(10 2 0 1 1) '(6 1 0 1 0)))))
(defconst *rs-read-token*
  (nth 1 (mv-list 3 (fn-prl-admit *rs-reserved* 2 1 0 4 0
                                  '(10 2 0 1 1) '(6 1 0 1 0)))))
(defconst *rs-cached*
  (nth 1 (mv-list 2 (fn-prl-settle *rs-issued* *rs-read-token* t))))
(defconst *rs-evicted*
  (nth 1 (mv-list 2 (fn-prl-evict *rs-cached* *rs-read-token*))))

; The same live rows with no charge: removal witnesses for the custody premise.
(defconst *rs-undercharged*
  (fn-prl-build *rs-budget* '(0 0 0 0 0) 1
                (fn-prl-nth 3 *rs-reserved*) nil))
; Exact reserve binding and pool funding still hold, but conversion must fail.
(defconst *rs-too-large*
  (fn-prl-build '(3 0 0 0 10) '(0 0 0 0 0) 1
                (list (cons *rs-reserve-token* (list '(7 0 0 0 0) :cached nil))) nil))
; Custody holds while installed budget is insufficient.
(defconst *rs-unfunded*
  (fn-prl-build '(3 0 0 0 10) '(7 0 0 0 0) 1
                (list (cons *rs-reserve-token* (list '(7 0 0 0 0) :cached nil))) nil))
(defconst *rs-negative*
  (fn-prl-build *rs-budget* '(0 0 0 0 0) 1
                (list (cons *rs-reserve-token* (list '(-1 0 0 0 0) :cached nil))) nil))

; Mutated eviction: refund DEMAND plus all currently charged resources.
; release-reusable's NFIX clamps the over-refund to zero; the other rows survive.
; This is a deliberately wrong transition, not a change to the ledger.
(defun fn-prl-rs-overrefund-mutant (ledger token)
  (declare (xargs :guard t))
  (let* ((rows (fn-prl-nth 3 ledger))
         (entry (fn-prl-binding token rows))
         (demand (fn-prl-nth 0 (if (consp entry) (cdr entry) nil)))
         (charged (fn-prl-nth 1 ledger)))
    (if (and (true-listp charged) (true-listp demand))
        (fn-prl-build (fn-prl-nth 0 ledger)
                      (fn-prs-release-reusable charged (fn-prs-plus charged demand))
                      (fn-prl-nth 2 ledger) (fn-prl-remove token rows)
                      (fn-prl-nth 4 ledger))
      ledger)))

; Assert successful branches as well as the complete claims checked below.
(assert-event
 (and (equal (nth 0 (mv-list 2 (fn-prl-register *rs-empty* 1 '(2 0 1 0 0)))) :registered)
      (equal (nth 0 (mv-list 3 (fn-prl-reserve-growth *rs-registered* 7))) :admitted)
      (equal (nth 0 (mv-list 3 (fn-prl-admit *rs-reserved* 2 1 0 4 0
                                            '(10 2 0 1 1) '(6 1 0 1 0)))) :admitted)
      (equal (nth 0 (mv-list 2 (fn-prl-settle *rs-issued* *rs-read-token* t))) :settled)
      (equal (nth 0 (mv-list 2 (fn-prl-settle *rs-issued* *rs-read-token* nil))) :settled)
      (fn-prl-row-sum-invp (nth 1 (mv-list 2 (fn-prl-settle *rs-issued* *rs-read-token* nil))))
      (equal (nth 0 (mv-list 2 (fn-prl-evict *rs-cached* *rs-read-token*))) :evicted)
      (equal (nth 0 (mv-list 2 (fn-prl-close *rs-evicted* 1))) :closed)
      (equal (nth 0 (mv-list 2 (fn-prl-convert-growth *rs-evicted* *rs-reserve-token* 7)))
             :protected-growth-admitted)))

(defteeth fn-prl-make-row-sum-invp
  :claim (() (fn-prl-row-sum-invp (fn-prl-make budget)))
  :subject fn-prl-make
  :witness ((budget *rs-budget*))
  :breaks ()
  :mutations ((unfunded-initial-row
    (:conclusion (fn-prl-row-sum-invp
                  (fn-prl-build budget '(0 0 0 0 0) 0
                    '((:unfunded (1 0 0 0 0) :cached nil)) nil)))
    ((budget *rs-budget*)) :fault "initialize a bound row without its charge")))

(defteeth fn-prl-register-preserves-row-sum-invp
  :claim (((custody (fn-prl-row-sum-invp ledger)))
          (fn-prl-row-sum-invp (mv-nth 1 (fn-prl-register ledger file demand))))
  :subject fn-prl-register
  :witness ((ledger *rs-empty*) (file 1) (demand '(2 0 1 0 0)))
  :breaks ((custody ((ledger *rs-undercharged*) (file 1) (demand '(2 0 1 0 0)))))
  :mutations (:not-applicable
    "The shared release-reusable over-refund fault is checked by eviction's mutant in this book."))

(defteeth fn-prl-admit-preserves-row-sum-invp
  :claim (((custody (fn-prl-row-sum-invp ledger)))
          (fn-prl-row-sum-invp (mv-nth 2 (fn-prl-admit ledger cid file eoff elen trailer demand native-demand))))
  :subject fn-prl-admit
  :witness ((ledger *rs-reserved*) (cid 2) (file 1) (eoff 0) (elen 4) (trailer 0) (demand '(10 2 0 1 1)) (native-demand '(6 1 0 1 0)))
  :breaks ((custody ((ledger *rs-undercharged*) (cid 2) (file 1) (eoff 0) (elen 4) (trailer 0) (demand '(10 2 0 1 1)) (native-demand '(6 1 0 1 0)))))
  :mutations (:not-applicable
    "The shared release-reusable over-refund fault is checked by eviction's mutant in this book."))

(defteeth fn-prl-settle-preserves-row-sum-invp
  :claim (((custody (fn-prl-row-sum-invp ledger)))
          (fn-prl-row-sum-invp (mv-nth 1 (fn-prl-settle ledger token cachedp))))
  :subject fn-prl-settle
  :witness ((ledger *rs-issued*) (token *rs-read-token*) (cachedp t))
  :breaks ((custody ((ledger *rs-undercharged*) (token *rs-read-token*) (cachedp t))))
  :mutations (:not-applicable
    "The shared release-reusable over-refund fault is checked by eviction's mutant in this book."))

(defteeth fn-prl-evict-preserves-row-sum-invp
  :claim (((custody (fn-prl-row-sum-invp ledger)))
          (fn-prl-row-sum-invp (mv-nth 1 (fn-prl-evict ledger token))))
  :subject fn-prl-evict
  :witness ((ledger *rs-cached*) (token *rs-read-token*))
  :breaks ((custody ((ledger *rs-undercharged*) (token *rs-reserve-token*))))
  :mutations ((refunds-another-row
    (:conclusion (fn-prl-row-sum-invp (fn-prl-rs-overrefund-mutant ledger token)))
    ((ledger *rs-cached*) (token *rs-read-token*))
    :fault "over-refund clamps resident charge to zero while the reserve and incarnation rows survive")))

(defteeth fn-prl-close-preserves-row-sum-invp
  :claim (((custody (fn-prl-row-sum-invp ledger)))
          (fn-prl-row-sum-invp (mv-nth 1 (fn-prl-close ledger file))))
  :subject fn-prl-close
  :witness ((ledger *rs-evicted*) (file 1))
  :breaks ((custody ((ledger *rs-undercharged*) (file 1))))
  :mutations (:not-applicable
    "The shared release-reusable over-refund fault is checked by eviction's mutant in this book."))

(defteeth fn-prl-reserve-growth-preserves-row-sum-invp
  :claim (((custody (fn-prl-row-sum-invp ledger)))
          (fn-prl-row-sum-invp (mv-nth 2 (fn-prl-reserve-growth ledger amount))))
  :subject fn-prl-reserve-growth
  :witness ((ledger *rs-registered*) (amount 7))
  :breaks ((custody ((ledger *rs-undercharged*) (amount 7))))
  :mutations (:not-applicable
    "The shared release-reusable over-refund fault is checked by eviction's mutant in this book."))

(defteeth fn-prl-convert-growth-preserves-row-sum-invp
  :claim (((custody (fn-prl-row-sum-invp ledger)))
          (fn-prl-row-sum-invp (mv-nth 1 (fn-prl-convert-growth ledger token amount))))
  :subject fn-prl-convert-growth
  :witness ((ledger *rs-evicted*) (token *rs-reserve-token*) (amount 7))
  :breaks ((custody ((ledger *rs-undercharged*) (token *rs-reserve-token*) (amount 7))))
  :mutations (:not-applicable
    "The shared release-reusable over-refund fault is checked by eviction's mutant in this book."))

(defteeth fn-prl-row-sum-bound-reserve-natural
  :claim (((custody (fn-prl-row-sum-invp ledger))
           (bound (equal (fn-prl-binding token (fn-prl-nth 3 ledger))
                         (cons token (list (list amount 0 0 0 0) :cached nil)))))
          (natp amount))
  :subject fn-prl-convert-growth
  :witness ((ledger *rs-reserved*) (token *rs-reserve-token*) (amount 7))
  :breaks ((custody ((ledger *rs-negative*) (token *rs-reserve-token*) (amount -1)))
           (bound ((ledger *rs-reserved*) (token *rs-reserve-token*) (amount -1))))
  :mutations (:not-applicable "This lemma derives the removed NATP premise, not a transition."))

(defteeth fn-prl-row-sum-covers-bound-reserve
  :claim (((custody (fn-prl-row-sum-invp ledger))
           (bound (equal (fn-prl-binding token (fn-prl-nth 3 ledger))
                         (cons token (list (list amount 0 0 0 0) :cached nil)))))
          (<= amount (fn-prl-nth 0 (fn-prl-nth 1 ledger))))
  :subject fn-prl-convert-growth
  :witness ((ledger *rs-evicted*) (token *rs-reserve-token*) (amount 7))
  :breaks ((custody ((ledger *rs-undercharged*) (token *rs-reserve-token*) (amount 7)))
           (bound ((ledger *rs-evicted*) (token *rs-reserve-token*) (amount 100))))
  :mutations ((strict-coverage
    (:conclusion (< amount (fn-prl-nth 0 (fn-prl-nth 1 ledger))))
    ((ledger *rs-unfunded*) (token *rs-reserve-token*) (amount 7))
    :fault "require strictly more charge than the bound row instead of allowing exact coverage")))

(defteeth fn-prl-convert-growth-under-row-sum-invp
  :claim (((custody (fn-prl-row-sum-invp ledger))
           (bound (equal (fn-prl-binding token (fn-prl-nth 3 ledger))
                         (cons token (list (list amount 0 0 0 0) :cached nil))))
           (funded (fn-prs-fundedp (fn-prl-nth 0 ledger) (fn-prl-baseline ledger)
                                   '(0 0 0 0 0) (fn-prl-nth 1 ledger))))
          (and (equal (mv-nth 0 (fn-prl-convert-growth ledger token amount))
                      :protected-growth-admitted)
               (let ((next (mv-nth 1 (fn-prl-convert-growth ledger token amount))))
                 (fn-prs-fundedp (fn-prl-nth 0 next) (fn-prl-baseline next)
                                 '(0 0 0 0 0) (fn-prl-nth 1 next)))))
  :subject fn-prl-convert-growth
  :witness ((ledger *rs-evicted*) (token *rs-reserve-token*) (amount 7))
  :breaks ((custody ((ledger *rs-too-large*) (token *rs-reserve-token*) (amount 7)))
           (bound ((ledger *rs-evicted*) (token :absent) (amount 7)))
           (funded ((ledger *rs-unfunded*) (token *rs-reserve-token*) (amount 7))))
  :mutations ((stale-reserve
    (:conclusion (equal (mv-nth 0 (fn-prl-convert-growth ledger token amount)) :stale))
    ((ledger *rs-evicted*) (token *rs-reserve-token*) (amount 7))
    :fault "a live funded reserve is treated as stale")))

; Distinguish the mutant from the production eviction on the same live input.
(assert-event
 (and (fn-prl-row-sum-invp *rs-cached*)
      (fn-prl-row-sum-invp *rs-evicted*)
      (not (fn-prl-row-sum-invp (fn-prl-rs-overrefund-mutant *rs-cached* *rs-read-token*)))
      (equal (fn-prl-nth 0 (fn-prl-nth 1
                  (fn-prl-rs-overrefund-mutant *rs-cached* *rs-read-token*))) 0)
      (equal (fn-prl-binding *rs-reserve-token*
                 (fn-prl-nth 3 (fn-prl-rs-overrefund-mutant *rs-cached* *rs-read-token*)))
             (cons *rs-reserve-token* (list '(7 0 0 0 0) :cached nil)))))

; A scalar sum bound alone is insufficient for cached settlement: native
; demand 11 exceeds this issued row's 4 while the other row owns 7.
(defconst *rs-native-too-large*
  (fn-prl-build *rs-budget* '(11 0 0 0 0) 2
    '((:issued-token (4 0 0 0 0) :issued (11 0 0 0 0))
      (:other-token (7 0 0 0 0) :cached nil)) nil))
(assert-event
 (and (<= (fn-prl-row-sum 0 (fn-prl-nth 3 *rs-native-too-large*))
          (fn-prl-nth 0 (fn-prl-nth 1 *rs-native-too-large*)))
      (not (fn-prl-row-sum-invp *rs-native-too-large*))
      (equal (nth 0 (mv-list 2 (fn-prl-settle *rs-native-too-large* :issued-token t)))
             :settled)
      (not (fn-prl-row-sum-invp
             (nth 1 (mv-list 2 (fn-prl-settle *rs-native-too-large* :issued-token t)))))))

(defteeth-check)
