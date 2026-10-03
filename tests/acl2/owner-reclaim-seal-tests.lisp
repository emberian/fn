; Teeth for books/owner-reclaim-seal.lisp (lane arena-forget): the reclaim
; pass predicts its tombstones and seals them only in the swap quantum.
;   fn-orcs-seal-is-the-intern       (one hypothesis: no row is :bad)
;   fn-orcs-seal-word-swap-means-base

(in-package "ACL2")
(include-book "../../books/owner-reclaim-seal")
(include-book "must-fail-checked")

(assert-event
 (and (eq (symbol-class 'fn-orcs-predict (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-orcs-seal (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-orcs-seal-word (w state)) :common-lisp-compliant)))

(defconst *orcst-w1*
  (fn-record-make 0 1 0 "<a@x>" '(83 58 32 97 13 10 13 10) '("fn.test") "o" "s" "e" 1 5))
(defconst *orcst-w2*
  (fn-record-make 1 2 0 "<b@x>" '(83 58 32 98 13 10 13 10) '("fn.test") "o" "s" "e" 1 5))

; Rows as the rewrite leaves them: a kept held row (by pointer), a
; tombstoned record, a kept wire event, a second record.
(defconst *orcst-kept* (fn-held-plain *orcst-w1* 0))
(defconst *orcst-rows* (list *orcst-kept* *orcst-w1* '(:not-a-record) *orcst-w2*))
(defconst *orcst-arena* '((1) (2)))

; Positive: over an arena of count 2 the prediction at 2 is the intern's
; rows, and the seal is the intern's arena (ground, both sides executed).
(defthm orcst-predict-is-intern-positive
  (and (equal (fn-arena-count *orcst-arena*) 2)
       (not (fn-orcs-has-bad *orcst-rows*))
       (equal (mv-nth 0 (fn-orcp-intern-rows *orcst-rows* nil 0 *orcst-arena*))
              (first (fn-orcs-predict *orcst-rows* nil 0 2)))
       (equal (mv-nth 1 (fn-orcp-intern-rows *orcst-rows* nil 0 *orcst-arena*))
              (fn-orcs-seal (second (fn-orcs-predict *orcst-rows* nil 0 2)) *orcst-arena*))
       (equal (len (fn-orcs-seal (second (fn-orcs-predict *orcst-rows* nil 0 2)) *orcst-arena*))
              4)
       (equal (fn-record-payload (nth 3 (first (fn-orcs-predict *orcst-rows* nil 0 2)))) 3))
  :rule-classes nil)

; MUTATION (the arena moved: a POST prepare sealed after the prediction).
; The prediction at the old base names handles the seal does not make.
(defthm orcst-moved-base-mutation
  (not (equal (mv-nth 0 (fn-orcp-intern-rows *orcst-rows* nil 0 '((1) (2) (3))))
              (first (fn-orcs-predict *orcst-rows* nil 0 2))))
  :rule-classes nil)

(local
 (must-fail-checked
  (defthm orcst-predict-at-any-base
    (implies (not (fn-orcs-has-bad rows))
             (equal (mv-nth 0 (fn-orcp-intern-rows rows keyring generation fn-arena))
                    (fn-orcs-predict-rows rows keyring generation h))))))

; fn-orcs-seal-word-swap-means-base.  Positive.
(defthm orcst-seal-word-positive
  (and (equal (fn-orcs-seal-word :swap 7 7) :swap)
       (equal :swap :swap) (equal 7 7))
  :rule-classes nil)

; The moved arena is deferred by name; any other word passes through.
(defthm orcst-seal-word-moved
  (and (equal (fn-orcs-seal-word :swap 8 7) :moved)
       (equal (fn-orcs-seal-word :readers 8 7) :readers)
       (equal (fn-orcs-seal-word :delta 7 7) :delta))
  :rule-classes nil)

(local
 (must-fail-checked
  (defthm orcst-seal-word-without-base
    (implies (equal word :swap)
             (equal (fn-orcs-seal-word word count base) :swap)))))

; Without the hypothesis: a row that is the word :bad makes the intern
; refuse, the prediction not.
(defthm orcst-without-no-bad
  (and (fn-orcs-has-bad '(:bad))
       (equal (mv-nth 0 (fn-orcp-intern-rows '(:bad) nil 0 *orcst-arena*)) :bad)
       (equal (fn-orcs-predict-rows '(:bad) nil 0 2) '(:bad))
       (equal (first (fn-orcs-predict '(:bad) nil 0 2)) :bad))
  :rule-classes nil)

(local
 (must-fail-checked
  (defthm orcst-intern-without-no-bad
    (equal (fn-orcp-intern-rows rows keyring generation fn-arena)
           (mv (fn-orcs-predict-rows rows keyring generation (fn-arena-count fn-arena))
               (fn-orcs-seal (fn-orcs-payloads rows) fn-arena))))))
