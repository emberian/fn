; Teeth for books/owner-reclaim-seal.lisp (lane arena-forget): the reclaim
; pass predicts its tombstones and seals them only in the swap quantum.
;   fn-orcs-seal-is-the-intern       (one hypothesis: no row is :bad)
;   fn-orcs-seal-word-swap-means-base

(in-package "ACL2")
(include-book "../../books/owner-reclaim-seal")
(include-book "must-fail-checked")
(include-book "../../books/defkeystone")

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
       (equal (mv-nth 0 (fn-orcp-intern-rows *orcst-rows* (fn-stxk-initial-context 0) *orcst-arena*))
              (first (fn-orcs-predict *orcst-rows* (fn-stxk-initial-context 0) 2)))
       (equal (mv-nth 1 (fn-orcp-intern-rows *orcst-rows* (fn-stxk-initial-context 0) *orcst-arena*))
              (fn-orcs-seal (second (fn-orcs-predict *orcst-rows* (fn-stxk-initial-context 0) 2)) *orcst-arena*))
       (equal (len (fn-orcs-seal (second (fn-orcs-predict *orcst-rows* (fn-stxk-initial-context 0) 2)) *orcst-arena*))
              4)
       (equal (fn-record-payload (nth 3 (first (fn-orcs-predict *orcst-rows* (fn-stxk-initial-context 0) 2)))) 3))
  :rule-classes nil)

; MUTATION (the arena moved: a POST prepare sealed after the prediction).
; The prediction at the old base names handles the seal does not make.
(defthm orcst-moved-base-mutation
  (not (equal (mv-nth 0 (fn-orcp-intern-rows *orcst-rows* (fn-stxk-initial-context 0) '((1) (2) (3))))
              (first (fn-orcs-predict *orcst-rows* (fn-stxk-initial-context 0) 2))))
  :rule-classes nil)

(local
 (must-fail-checked
  (defthm orcst-predict-at-any-base
    (implies (not (fn-orcs-has-bad rows))
             (equal (mv-nth 0 (fn-orcp-intern-rows rows id fn-arena))
                    (fn-orcs-predict-rows-at rows id h))))))

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
       (equal (mv-nth 0 (fn-orcp-intern-rows '(:bad) (fn-stxk-initial-context 0) *orcst-arena*)) :bad)
       (equal (fn-orcs-predict-rows-at '(:bad) (fn-stxk-initial-context 0) 2) '(:bad))
       (equal (first (fn-orcs-predict '(:bad) (fn-stxk-initial-context 0) 2)) :bad))
  :rule-classes nil)

(local
 (must-fail-checked
  (defthm orcst-intern-without-no-bad
    (equal (fn-orcp-intern-rows rows id fn-arena)
           (mv (fn-orcs-predict-rows-at rows id (fn-arena-count fn-arena))
               (fn-orcs-seal (fn-orcs-payloads rows) fn-arena))))))

; PRF-1258: literal full result/effect boundary of actual fn-orcs-predict.
; The boundary theorem lives in host/owner-host.lisp, where it is loaded;
; these ground teeth execute its book-level subjects without loading STATE.
(defthm orcst-actual-predict-seal-positive
  (and (not (fn-orcs-has-bad *orcst-rows*))
       (equal (fn-orcp-intern-rows *orcst-rows* (fn-stxk-initial-context 0) *orcst-arena*)
              (mv (car (fn-orcs-predict *orcst-rows* (fn-stxk-initial-context 0)
                                      (fn-arena-count *orcst-arena*)))
                  (fn-orcs-seal
                   (cadr (fn-orcs-predict *orcst-rows* (fn-stxk-initial-context 0)
                                         (fn-arena-count *orcst-arena*)))
                   *orcst-arena*))))
  :rule-classes nil)

; Hypothesis removal: a valid record before :bad makes the incremental
; intern retain a partial arena effect, while prediction refuses atomically.
(defthm orcst-actual-predict-seal-without-no-bad
  (let ((rows (list *orcst-w1* :bad)))
    (and (fn-orcs-has-bad rows)
         (not (equal (fn-orcp-intern-rows rows (fn-stxk-initial-context 0) *orcst-arena*)
                     (mv (car (fn-orcs-predict rows (fn-stxk-initial-context 0)
                                             (fn-arena-count *orcst-arena*)))
                         (fn-orcs-seal
                          (cadr (fn-orcs-predict rows (fn-stxk-initial-context 0)
                                                (fn-arena-count *orcst-arena*)))
                          *orcst-arena*))))))
  :rule-classes nil)

; The changed critical boundaries carry executable full-result evidence.
(defun orcst-seed-arena (fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let* ((fn-arena (fn-arena-seal-list '(1) fn-arena))
         (fn-arena (fn-arena-seal-list '(2) fn-arena)))
    fn-arena))

; Native observers compare the returned rows and the arena's final count.
; The reference and seal append the same payloads whenever prediction does
; not refuse. On refusal, equality with the unchanged arena is equivalent
; to sealing zero rows; the lemmas below establish that effect equivalence.
(defun orcst-payload-prefix (rows)
  (declare (xargs :guard t))
  (if (or (atom rows) (equal (car rows) :bad)) nil
    (if (fn-record-p (car rows))
        (cons (fn-record-payload (car rows)) (orcst-payload-prefix (cdr rows)))
      (orcst-payload-prefix (cdr rows)))))
(local
 (defthm orcst-reference-effect
   (equal (mv-nth 1 (fn-orcp-intern-rows-at rows id h fn-arena))
          (fn-orcs-seal (orcst-payload-prefix rows) fn-arena))
   :hints (("Goal" :induct (fn-orcp-intern-rows-at rows id h fn-arena)
            :in-theory (e/d (fn-record-p fn-record-payloadp)
                            (fn-intern-row-at fn-replay-identity-loop fn-ssr-seed fn-ssr-at
                             fn-arena-seal-list-is-append fn-arena-count-is-len))))))
(local
 (defthm orcst-prefix-count
   (equal (fn-arena-count (fn-orcs-seal (orcst-payload-prefix rows) fn-arena))
          (+ (fn-arena-count fn-arena) (len (orcst-payload-prefix rows))))
   :hints (("Goal" :induct (fn-orcp-intern-rows-at rows id h fn-arena)
            :in-theory (e/d (fn-record-p fn-record-payloadp)
                            (fn-intern-row-at fn-replay-identity-loop fn-ssr-seed fn-ssr-at
                             fn-arena-seal-list-is-append fn-arena-count-is-len))))))
(local
 (defthm orcst-prefix-empty
   (implies (equal (len (orcst-payload-prefix rows)) 0)
            (equal (orcst-payload-prefix rows) nil))))
(local
 (defthm orcst-effect-unchanged-iff-count
   (equal (equal (fn-orcs-seal (orcst-payload-prefix rows) fn-arena) fn-arena)
          (equal (fn-arena-count (fn-orcs-seal (orcst-payload-prefix rows) fn-arena))
                 (fn-arena-count fn-arena)))
   :hints (("Goal" :cases ((equal (len (orcst-payload-prefix rows)) 0))
            :use orcst-prefix-count
            :expand ((fn-orcs-seal nil fn-arena))
            :in-theory (disable fn-orcs-seal orcst-payload-prefix orcst-prefix-count)))))

(local
 (defthm orcst-prefix-when-no-bad
   (implies (not (fn-orcs-has-bad rows))
            (equal (orcst-payload-prefix rows) (fn-orcs-payloads rows)))
   :hints (("Goal" :in-theory (disable fn-record-p)))))
(local
 (defthm orcst-reference-bad
   (equal (equal (mv-nth 0 (fn-orcp-intern-rows-at rows id h fn-arena)) :bad)
          (if (fn-orcs-has-bad rows) t nil))
   :hints (("Goal" :induct (fn-orcp-intern-rows-at rows id h fn-arena)
            :in-theory (disable fn-intern-row-at fn-replay-identity-loop fn-ssr-seed fn-ssr-at
                                fn-record-p fn-arena-seal-list-is-append fn-arena-count-is-len)))))

(local
 (defthm orcst-reference-result
   (equal (fn-orcp-intern-rows-at rows id h fn-arena)
          (list (if (fn-orcs-has-bad rows) :bad (fn-orcs-predict-rows-at rows id h))
                (fn-orcs-seal (orcst-payload-prefix rows) fn-arena)))
   :hints (("Goal" :induct (fn-orcp-intern-rows-at rows id h fn-arena)
            :in-theory (e/d (fn-record-p fn-record-payloadp)
                            (fn-intern-row-at fn-replay-identity-loop fn-ssr-seed fn-ssr-at
                             fn-arena-seal-list-is-append fn-arena-count-is-len))))))

(defun orcst-seal-check (rows id offset fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((want (fn-orcs-predict-rows-at rows id (+ offset (fn-arena-count fn-arena)))))
    (mv-let (got fn-arena) (fn-orcp-intern-rows rows id fn-arena)
      (mv (equal got want) fn-arena))))
(defun orcst-predict-check (rows id offset fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((base (fn-arena-count fn-arena))
         (want (fn-orcs-predict rows id (+ offset base))))
    (mv-let (got fn-arena) (fn-orcp-intern-rows rows id fn-arena)
      (mv (and (equal got (car want))
               (equal (fn-arena-count fn-arena) (+ base (len (cadr want))))) fn-arena))))

(defteeth fn-orcs-seal-is-the-intern
 :claim (((no-bad (not (fn-orcs-has-bad rows))))
         (equal (fn-orcp-intern-rows rows id fn-arena)
                (mv (fn-orcs-predict-rows-at rows id (fn-arena-count fn-arena))
                    (fn-orcs-seal (fn-orcs-payloads rows) fn-arena))))
 :subject fn-orcp-intern-rows
 :witness ((rows *orcst-rows*) (id (fn-stxk-initial-context 0)))
 :stobjs ((fn-arena (orcst-seed-arena fn-arena)))
 :stobj-checks
 (((equal (fn-orcp-intern-rows rows id fn-arena)
                (mv (fn-orcs-predict-rows-at rows id (fn-arena-count fn-arena))
                    (fn-orcs-seal (fn-orcs-payloads rows) fn-arena)))
    (orcst-seal-check rows id 0 fn-arena)
    :hints (("Goal" :cases ((fn-orcs-has-bad rows))
             :in-theory (e/d (orcst-seal-check fn-orcp-intern-rows fn-orcs-predict)
                             (fn-orcp-intern-rows-at fn-orcs-predict-rows-at fn-orcs-payloads
                              fn-orcs-has-bad fn-orcs-seal orcst-payload-prefix
                              fn-arena-count-is-len)))))
  ((equal (fn-orcp-intern-rows rows id fn-arena)
                      (mv (fn-orcs-predict-rows-at rows id (+ 1 (fn-arena-count fn-arena)))
                          (fn-orcs-seal (fn-orcs-payloads rows) fn-arena)))
    (orcst-seal-check rows id 1 fn-arena)
    :hints (("Goal" :cases ((fn-orcs-has-bad rows))
             :in-theory (e/d (orcst-seal-check fn-orcp-intern-rows fn-orcs-predict)
                             (fn-orcp-intern-rows-at fn-orcs-predict-rows-at fn-orcs-payloads
                              fn-orcs-has-bad fn-orcs-seal orcst-payload-prefix
                              fn-arena-count-is-len))))))
 :breaks ((no-bad ((rows (list *orcst-w1* :bad)))))
 :mutations ((moved-handle
              (:conclusion
               (equal (fn-orcp-intern-rows rows id fn-arena)
                      (mv (fn-orcs-predict-rows-at rows id (+ 1 (fn-arena-count fn-arena)))
                          (fn-orcs-seal (fn-orcs-payloads rows) fn-arena))))
              () :fault "prediction starts above the actual arena count")))

(defteeth fn-orcs-predict-seal-refines-intern
 :claim (((no-bad (not (fn-orcs-has-bad rows))))
         (equal (fn-orcp-intern-rows rows id fn-arena)
                (mv (car (fn-orcs-predict rows id (fn-arena-count fn-arena)))
                    (fn-orcs-seal
                     (cadr (fn-orcs-predict rows id (fn-arena-count fn-arena)))
                     fn-arena))))
 :subject fn-orcs-predict
 :witness ((rows *orcst-rows*) (id (fn-stxk-initial-context 0)))
 :stobjs ((fn-arena (orcst-seed-arena fn-arena)))
 :stobj-checks
 (((equal (fn-orcp-intern-rows rows id fn-arena)
                (mv (car (fn-orcs-predict rows id (fn-arena-count fn-arena)))
                    (fn-orcs-seal
                     (cadr (fn-orcs-predict rows id (fn-arena-count fn-arena)))
                     fn-arena)))
    (orcst-predict-check rows id 0 fn-arena)
    :hints (("Goal" :cases ((fn-orcs-has-bad rows))
             :use orcst-prefix-count
             :expand ((fn-orcs-seal nil fn-arena))
             :in-theory (e/d (orcst-predict-check fn-orcp-intern-rows fn-orcs-predict)
                             (fn-orcp-intern-rows-at fn-orcs-predict-rows-at fn-orcs-payloads
                              fn-orcs-has-bad fn-orcs-seal orcst-payload-prefix
                              fn-arena-count-is-len orcst-prefix-count)))))
  ((equal (fn-orcp-intern-rows rows id fn-arena)
                      (mv (car (fn-orcs-predict rows id (+ 1 (fn-arena-count fn-arena))))
                          (fn-orcs-seal
                           (cadr (fn-orcs-predict rows id (fn-arena-count fn-arena)))
                           fn-arena)))
    (orcst-predict-check rows id 1 fn-arena)
    :hints (("Goal" :cases ((fn-orcs-has-bad rows))
             :use orcst-prefix-count
             :expand ((fn-orcs-seal nil fn-arena))
             :in-theory (e/d (orcst-predict-check fn-orcp-intern-rows fn-orcs-predict)
                             (fn-orcp-intern-rows-at fn-orcs-predict-rows-at fn-orcs-payloads
                              fn-orcs-has-bad fn-orcs-seal orcst-payload-prefix
                              fn-arena-count-is-len orcst-prefix-count))))))
 :breaks ((no-bad ((rows (list *orcst-w1* :bad)))))
 :mutations ((moved-handle
              (:conclusion
               (equal (fn-orcp-intern-rows rows id fn-arena)
                      (mv (car (fn-orcs-predict rows id (+ 1 (fn-arena-count fn-arena))))
                          (fn-orcs-seal
                           (cadr (fn-orcs-predict rows id (fn-arena-count fn-arena)))
                           fn-arena))))
              () :fault "the prediction names handles beyond the seal's actual handles")))
