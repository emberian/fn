; Reachable lifecycle witnesses, premise removals, and an over-refund mutant.
(in-package "ACL2")
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

; A scalar sum bound alone is insufficient for cached settlement: native
; demand 11 exceeds this issued row's 4 while the other row owns 7.
(defconst *rs-native-too-large*
  (fn-prl-build *rs-budget* '(11 0 0 0 0) 2
    '((:issued-token (4 0 0 0 0) :issued (11 0 0 0 0))
      (:other-token (7 0 0 0 0) :cached nil)) nil))
(defteeth-check)
