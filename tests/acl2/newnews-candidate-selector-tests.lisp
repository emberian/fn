(in-package "ACL2")
(include-book "../../books/newnews-candidate-selector")

; Test-only drain. Production drives one step and charges its entry visit.
(defun nnst-next (s)
  (declare (xargs :guard t))
  (mv-let (decided matched next) (fn-nnw-select-one s)
    (declare (ignore decided matched)) next))
(defun nnst-drain (s fuel)
  (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
  (if (or (zp fuel) (eq (fn-nnw-select-at 6 s) :done)) s
    (nnst-drain (nnst-next s) (1- fuel))))

(defconst *nnst-patterns*
  (fn-wildmat-result-value (fn-wildmat-parse (fn-nntp-string-octets "fn.*,!fn.block"))))
(defconst *nnst-article*
  (fn-make-article "<a@x>" nil '("fn.good")
                   '(("else" . 9) ("fn.block" . 1) ("fn.good" . 7)) 1 1))
(defconst *nnst-start*
  (fn-nnw-select-start *nnst-patterns* '("fn.miss" "fn.block" "fn.good") *nnst-article*))
(defconst *nnst-member*
  (nnst-next *nnst-start*))
(defconst *nnst-sparse*
  (nnst-next *nnst-member*))

; Full literal antecedents and conclusions on states reached from start.
(defthm nnst-sparse-progress-positive
  (let ((next (mv-nth 2 (fn-nnw-select-one *nnst-sparse*))))
    (and (fn-nnw-select-statep *nnst-sparse*)
         (not (eq (fn-nnw-select-at 6 *nnst-sparse*) :done))
         (posp (fn-nnw-select-remaining *nnst-sparse*))
         (not (mv-nth 0 (fn-nnw-select-one *nnst-sparse*)))
         (fn-nnw-select-statep next)
         (equal (fn-nnw-select-value next) (fn-nnw-select-value *nnst-sparse*))
         (< (fn-nnw-select-remaining next) (fn-nnw-select-remaining *nnst-sparse*))
         (equal (fn-nnw-select-at 7 next) 1)
         (equal (fn-nnw-select-at 8 next) 2)
         (<= (fn-nnw-select-at 7 *nnst-sparse*) (fn-nnw-select-at 7 next))
         (<= (fn-nnw-select-at 7 next) (+ 1 (fn-nnw-select-at 7 *nnst-sparse*)))
         (<= (fn-nnw-select-at 8 *nnst-sparse*) (fn-nnw-select-at 8 next))
         (<= (fn-nnw-select-at 8 next) (+ 1 (fn-nnw-select-at 8 *nnst-sparse*)))
         (equal (+ (- (fn-nnw-select-at 7 next) (fn-nnw-select-at 7 *nnst-sparse*))
                   (- (fn-nnw-select-at 8 next) (fn-nnw-select-at 8 *nnst-sparse*)))
                (fn-nnw-select-entry-visits *nnst-sparse*))
         (equal (fn-nnw-select-entry-visits *nnst-sparse*) 1))))

(defthm nnst-complete-candidate-positive
  (let* ((before (nnst-drain *nnst-start* 11))
         (answer (fn-nnw-select-one before))
         (done (mv-nth 2 answer)))
    (and (fn-nnw-select-statep before)
         (equal (fn-nnw-select-at 6 before) :member)
         (posp (fn-nnw-select-remaining before))
         (mv-nth 0 answer) (mv-nth 1 answer)
         (equal (fn-nnw-select-value before)
                (fn-nntp-newnews-candidatep
                 (fn-nntp-filter-groups-by-wildmat *nnst-patterns*
                                                  '("fn.miss" "fn.block" "fn.good"))
                 *nnst-article*))
         (equal (mv-nth 1 answer) (fn-nnw-select-value before))
         (equal (fn-nnw-select-value done) (fn-nnw-select-value before))
         (equal (fn-nnw-select-at 6 done) :done)
         (equal (fn-nnw-select-at 7 done) 3)
         (equal (fn-nnw-select-at 8 done) 3)
         (fn-nnw-select-statep done)
         (< (fn-nnw-select-remaining done) (fn-nnw-select-remaining before))
         (equal (fn-nnw-select-remaining done) 0))))

; Corrupted record teeth: a later valid duplicate must never rescue the FIRST
; equal membership's zero/overflow number. Valid article-id guard retained.
(defthm nnst-first-invalid-membership-stops
  (let* ((a (fn-make-article "<a@x>" nil '("fn.good")
                            '(("fn.good" . 0) ("fn.good" . 7)) 1 1))
         (s (fn-nnw-select-start *nnst-patterns* '("fn.good") a))
         (done (nnst-drain s 10)))
    (and (fn-nntp-article-idp a)
         (not (fn-nntp-newnews-candidatep '("fn.good") a))
         (fn-nnw-select-statep s) (fn-nnw-select-statep done)
         (equal (fn-nnw-select-at 6 done) :done)
         (equal (fn-nnw-select-at 8 done) 1)
         (not (fn-nnw-select-value s)) (not (fn-nnw-select-value done)))))

(defthm nnst-overflow-number-refused
  (let* ((a (fn-make-article "<a@x>" nil '("fn.good")
                            (list (cons "fn.good" (+ 1 *fn-nntp-max-article-number*))) 1 1))
         (s (fn-nnw-select-start *nnst-patterns* '("fn.good") a)))
    (and (fn-nntp-article-idp a)
         (not (fn-nntp-newnews-candidatep '("fn.good") a))
         (not (fn-nnw-select-value (nnst-drain s 10))))))

(defthm nnst-invalid-id-refused
  (let* ((a (fn-make-article "bad id" nil '("fn.good") '(("fn.good" . 7)) 1 1))
         (s (fn-nnw-select-start *nnst-patterns* '("fn.good") a)))
    (and (posp (fn-nntp-membership-number "fn.good" (fn-article-memberships a)))
         (<= (fn-nntp-membership-number "fn.good" (fn-article-memberships a))
             *fn-nntp-max-article-number*)
         (not (fn-nntp-article-idp a))
         (not (fn-nntp-newnews-candidatep '("fn.good") a))
         (not (fn-nnw-select-value (nnst-drain s 10))))))

(defthm nnst-negative-wildmat-refused
  (let ((s (fn-nnw-select-start *nnst-patterns* '("fn.block") *nnst-article*)))
    (and (fn-nntp-article-idp *nnst-article*)
         (posp (fn-nntp-article-number "fn.block" *nnst-article*))
         (not (fn-nntp-group-matches-parsed-wildmatp *nnst-patterns* "fn.block"))
         (not (fn-nnw-select-value s))
         (equal (fn-nnw-select-at 6 (nnst-drain s 10)) :done)
         (not (fn-nnw-select-value (nnst-drain s 10))))))

(defthm nnst-empty-settlement-positive
  (let* ((s (fn-nnw-select-start *nnst-patterns* nil *nnst-article*))
         (answer (fn-nnw-select-one s)))
    (and (fn-nnw-select-statep s)
         (equal (fn-nnw-select-remaining s) 0)
         (equal (fn-nnw-select-entry-visits s) 0)
         (not (< (fn-nnw-select-remaining (mv-nth 2 answer))
                 (fn-nnw-select-remaining s)))
         (mv-nth 0 answer) (not (mv-nth 1 answer))
         (equal (fn-nnw-select-at 6 (mv-nth 2 answer)) :done)
         (equal (fn-nnw-select-value (mv-nth 2 answer)) (fn-nnw-select-value s)))))

; Hypothesis removal: without fixed nonnegative offsets the group-visit upper
; bound fails. No other antecedent is retained by that literal theorem.
(defthm nnst-statep-removal-counterexample
  (let* ((s (fn-nnw-select-state *nnst-patterns* '("fn.good") *nnst-article*
                                nil nil :group -2 0 nil))
         (next (mv-nth 2 (fn-nnw-select-one s))))
    (and (not (fn-nnw-select-statep s))
         (not (<= (fn-nnw-select-at 7 next) (+ 1 (fn-nnw-select-at 7 s)))))))
