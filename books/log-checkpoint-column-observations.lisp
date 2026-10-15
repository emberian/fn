; Logical resident-column observations. Labels are removed by column-pages
; before PGS; they do not add a stored page or a second resident structure.
(in-package "ACL2")
(include-book "log-checkpoint-publication")
(include-book "log-cleaning-move")
(include-book "log-cleaning-complete")
(include-book "log-cleaning-byte-properties")
(include-book "log-checkpoint-teeth-wrappers")
(local (include-book "../tests/acl2/lc-complete-cleaning-teeth-tests"))
(defun fn-lc-row-column-pagep (page)
 (declare (xargs :guard t))
 (and (equal (fn-lc-head page) :lc-column)
      (equal (fn-lc-at 1 page) :rows)))
(defun fn-lc-column-row-store (columns)
 (declare (xargs :guard t))
 (if (consp columns)
  (if (fn-lc-row-column-pagep (car columns)) (fn-lc-at 4 (car columns))
   (fn-lc-column-row-store (cdr columns))) nil))
(defun fn-lc-non-row-columns (columns)
 (declare (xargs :guard t))
 (if (consp columns)
  (if (fn-lc-row-column-pagep (car columns)) (fn-lc-non-row-columns (cdr columns))
   (cons (car columns) (fn-lc-non-row-columns (cdr columns)))) nil))
(defun fn-lc-erase-row-locators (row)
 (declare (xargs :guard t))
 (ec-call (update-nth 2 0 (ec-call (update-nth 1 0 row)))))
(defun fn-lc-erase-rows-locators (rows)
 (declare (xargs :guard t))
 (if (consp rows)
  (cons (fn-lc-erase-row-locators (car rows)) (fn-lc-erase-rows-locators (cdr rows))) nil))
(defun fn-lc-row-words (i columns)
 (declare (xargs :guard t))
 (fn-lc-at i (fn-lc-column-row-store columns)))
(defun fn-lc-without-locators (columns)
 (declare (xargs :guard t))
 ; Every raw row field other than slots1,2 and every other encoded array,
 ; pool and map stays in this observation. No column page is guessed a row.
 (list (fn-lc-erase-rows-locators (fn-lc-column-row-store columns))
       (fn-lc-non-row-columns columns)))

(local (defthm lcoc-pages-consp
 (equal (consp (adt-tp-pages words)) (consp words))
 :hints (("Goal" :expand ((adt-tp-pages words))
 :in-theory (theory 'minimal-theory)))))

(local (defthm lcoc-row-pages-consp
 (equal (consp (fn-lbc-rowwords-pages-of rows)) (consp rows))
 :hints (("Goal" :cases ((consp rows)) :expand ((:free (schema) (adt-tp-seq-words schema rows)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-rowwords-pages-of adt-tp-pages-of adt-tp-seq-words adt-tp-rw
   lcoc-pages-consp binary-append car-cons cdr-cons))))))

(local (defthm lcoc-row-metadata-of-tagged
 (equal (fn-lc-column-row-store (fn-lc-tag-column-pages kind ordinal pages row-value))
  (if (and (consp pages) (equal kind :rows)) row-value nil))
 :hints (("Goal" :induct (fn-lc-tag-column-pages kind ordinal pages row-value)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-column-row-store fn-lc-tag-column-pages fn-lc-row-column-pagep
   fn-lc-head fn-lc-at-is-nth nth car-cons cdr-cons
   (:induction fn-lc-tag-column-pages) (:executable-counterpart zp)
   (:executable-counterpart binary-+) (:executable-counterpart equal)))))))

(local (defthm lcoc-row-metadata-of-tagged-prefix
 (equal (fn-lc-column-row-store
          (append (fn-lc-tag-column-pages kind ordinal pages row-value) rest))
  (if (and (consp pages) (equal kind :rows)) row-value (fn-lc-column-row-store rest)))
 :hints (("Goal" :induct (fn-lc-tag-column-pages kind ordinal pages row-value)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-column-row-store fn-lc-tag-column-pages fn-lc-row-column-pagep
   binary-append fn-lc-head fn-lc-at-is-nth nth car-cons cdr-cons
   (:induction fn-lc-tag-column-pages) (:executable-counterpart zp)
   (:executable-counterpart binary-+) (:executable-counterpart equal)))))))

(local (defthm lcoc-non-row-of-append
 (equal (fn-lc-non-row-columns (append a b))
        (append (fn-lc-non-row-columns a) (fn-lc-non-row-columns b)))
 :hints (("Goal" :induct (fn-lc-non-row-columns a)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-non-row-columns binary-append (:induction fn-lc-non-row-columns)
   car-cons cdr-cons))))))

(local (defthm lcoc-non-row-of-tagged
 (equal (fn-lc-non-row-columns (fn-lc-tag-column-pages kind ordinal pages row-value))
  (if (equal kind :rows) nil (fn-lc-tag-column-pages kind ordinal pages row-value)))
 :hints (("Goal" :induct (fn-lc-tag-column-pages kind ordinal pages row-value)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-non-row-columns fn-lc-tag-column-pages fn-lc-row-column-pagep
   fn-lc-head fn-lc-at-is-nth nth car-cons cdr-cons
   (:induction fn-lc-tag-column-pages) (:executable-counterpart zp)
   (:executable-counterpart binary-+) (:executable-counterpart equal)))))))

(defthm fn-lc-column-row-store-of-columns-value
 (equal (fn-lc-column-row-store (fn-lc-columns-value value))
  (if (consp (nth *fn-lbc-row-store* value)) (nth *fn-lbc-row-store* value) nil))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-columns-value lcoc-row-pages-consp lcoc-row-metadata-of-tagged
   lcoc-row-metadata-of-tagged-prefix (:executable-counterpart equal))))))

(local (defthm lcoc-erase-loc0
 (equal (fn-lc-erase-row-locators (update-nth 1 v row))
        (fn-lc-erase-row-locators row))
 :hints (("Goal" :expand ((:free (a r) (update-nth 1 a r)) (:free (a r) (update-nth 2 a r)) (:free (a r) (update-nth 0 a r))) :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-erase-row-locators update-nth car-cons cdr-cons
 (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart equal)))))))

(local (defthm lcoc-erase-loc1
 (equal (fn-lc-erase-row-locators (update-nth 2 v row))
        (fn-lc-erase-row-locators row))
 :hints (("Goal" :expand ((:free (a r) (update-nth 1 a r)) (:free (a r) (update-nth 2 a r)) (:free (a r) (update-nth 0 a r))) :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-erase-row-locators update-nth car-cons cdr-cons
 (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart equal)))))))

(local (defthm lcoc-erase-rows-loc0
 (implies (and (natp i) (< i (len rows)))
  (equal (fn-lc-erase-rows-locators
    (update-nth i (update-nth 1 v (nth i rows)) rows))
   (fn-lc-erase-rows-locators rows)))
 :hints (("Goal" :induct (nth i rows)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-erase-rows-locators update-nth nth len natp lcoc-erase-loc0
 (:induction nth) car-cons cdr-cons (:executable-counterpart zp)
 (:type-prescription len) (:compound-recognizer natp-compound-recognizer)))))))

(local (defthm lcoc-erase-rows-loc1
 (implies (and (natp i) (< i (len rows)))
  (equal (fn-lc-erase-rows-locators
    (update-nth i (update-nth 2 v (nth i rows)) rows))
   (fn-lc-erase-rows-locators rows)))
 :hints (("Goal" :induct (nth i rows)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-erase-rows-locators update-nth nth len natp lcoc-erase-loc1
 (:induction nth) car-cons cdr-cons (:executable-counterpart zp)
 (:type-prescription len) (:compound-recognizer natp-compound-recognizer)))))))

(local (defthm lcoc-non-row-update-store
 (equal (fn-lc-non-row-columns
         (fn-lc-columns-value (update-nth *fn-lbc-row-store* rows value)))
        (fn-lc-non-row-columns (fn-lc-columns-value value)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-columns-value lcoc-non-row-of-append lcoc-non-row-of-tagged
 fn-dm-nth-update-nth (:executable-counterpart equal) (:executable-counterpart nfix) binary-append))))))

(local (defthm lcoc-row-store-update-store
 (equal (fn-lc-column-row-store
         (fn-lc-columns-value (update-nth *fn-lbc-row-store* rows value)))
        (if (consp rows) rows nil))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-column-row-store-of-columns-value fn-dm-nth-update-nth
 (:executable-counterpart equal) (:executable-counterpart nfix)))))))

(local (defthm lcoc-nonlocators-update-loc0
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
 (equal (fn-lc-without-locators (fn-lc-columns (update-fn-lbc-loc0 i v fn-lbc)))
        (fn-lc-without-locators (fn-lc-columns fn-lbc))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-without-locators fn-lc-columns update-fn-lbc-loc0 fn-lbc-count
 fn-lbc-row-store update-fn-lbc-row-store fn-lbc-rowwords-count-is-len
 fn-lbc-rowwords-set-loc0-is-update-nth lcoc-non-row-update-store
 lcoc-row-store-update-store fn-lc-column-row-store-of-columns-value
 lcoc-erase-rows-loc0 fn-dm-nth-update-nth fn-dm-len-update-nth
 fn-dm-nth-of-zeros natp len update-nth nth
 (:type-prescription len) (:compound-recognizer natp-compound-recognizer)
 car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp)
 (:executable-counterpart fn-dm-zerosp) (:executable-counterpart nfix)))))))

(local (defthm lcoc-nonlocators-update-loc1
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
 (equal (fn-lc-without-locators (fn-lc-columns (update-fn-lbc-loc1 i v fn-lbc)))
        (fn-lc-without-locators (fn-lc-columns fn-lbc))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-without-locators fn-lc-columns update-fn-lbc-loc1 fn-lbc-count
 fn-lbc-row-store update-fn-lbc-row-store fn-lbc-rowwords-count-is-len
 fn-lbc-rowwords-set-loc1-is-update-nth lcoc-non-row-update-store
 lcoc-row-store-update-store fn-lc-column-row-store-of-columns-value
 lcoc-erase-rows-loc1 fn-dm-nth-update-nth fn-dm-len-update-nth
 fn-dm-nth-of-zeros natp len update-nth nth
 (:type-prescription len) (:compound-recognizer natp-compound-recognizer)
 car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp)
 (:executable-counterpart fn-dm-zerosp) (:executable-counterpart nfix)))))))

; Statement first: the original is frozen in v7; only its type premise is dropped.
; (defthm fn-lc-replay-move-is-a-locator-update
;   (implies (fn-lc-move-recordp move fn-lbc segs)
;            (and (equal (fn-lc-replay-move move fn-lbc)
;                        (update-fn-lbc-loc1
;                          (fn-lc-move-sequence move) (fn-lc-move-loc1 move)
;                          (update-fn-lbc-loc0
;                            (fn-lc-move-sequence move) (fn-lc-move-loc0 move) fn-lbc)))
;                 (equal (fn-lc-count (fn-lc-replay-move move fn-lbc))
;                        (fn-lc-count fn-lbc))
;                 (equal (fn-lc-without-locators
;                          (fn-lc-columns (fn-lc-replay-move move fn-lbc)))
;                        (fn-lc-without-locators (fn-lc-columns fn-lbc)))))
;   :rule-classes nil)

(local (defthm lcoc-count-of-loc0
 (equal (fn-lbc-count (update-fn-lbc-loc0 i v fn-lbc))
        (max (+ 1 (nfix i)) (fn-lbc-count fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-count update-fn-lbc-loc0 fn-lbc-row-store update-fn-lbc-row-store
 fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-loc0-is-update-nth
 fn-dm-nth-update-nth adt-len-update-nth-local max fn-dm-nth-of-zeros
 (:executable-counterpart nfix) (:executable-counterpart equal)))))))

(local (defthm lcoc-count-of-loc1
 (equal (fn-lbc-count (update-fn-lbc-loc1 i v fn-lbc))
        (max (+ 1 (nfix i)) (fn-lbc-count fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-count update-fn-lbc-loc1 fn-lbc-row-store update-fn-lbc-row-store
 fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-loc1-is-update-nth
 fn-dm-nth-update-nth adt-len-update-nth-local max fn-dm-nth-of-zeros
 (:executable-counterpart nfix) (:executable-counterpart equal)))))))

(local (defthm lcoc-created-count
 (equal (fn-lbc-count (create-fn-lbc)) 0)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-count create-fn-lbc fn-lbc-row-store fn-lbc-rowwords-count-is-len
 nth len car-cons cdr-cons (:executable-counterpart zp)))))))

(local (defun-nx lcrp-whole-conclusion (move fn-lbc)
 (and (equal (fn-lc-replay-move move fn-lbc)
       (update-fn-lbc-loc1 (fn-lc-move-sequence move) (fn-lc-move-loc1 move)
        (update-fn-lbc-loc0 (fn-lc-move-sequence move) (fn-lc-move-loc0 move) fn-lbc)))
      (equal (fn-lc-count (fn-lc-replay-move move fn-lbc)) (fn-lc-count fn-lbc))
      (equal (fn-lc-without-locators (fn-lc-columns (fn-lc-replay-move move fn-lbc)))
             (fn-lc-without-locators (fn-lc-columns fn-lbc))))))

(local (defun lcrp-replay-tooth (move fn-lbc)
 (declare (xargs :stobjs fn-lbc :verify-guards nil
 :guard (and (fn-lbc-p fn-lbc) (natp (fn-lc-move-sequence move))
  (< (fn-lc-move-sequence move) (fn-lc-count fn-lbc))
  (fn-locp (fn-lc-move-loc0 move) (fn-lc-move-loc1 move)))))
 (mbe :logic (let* ((answer (lcrp-whole-conclusion move fn-lbc)) (fn-lbc (fn-lc-replay-move move fn-lbc))) (mv answer fn-lbc))
 :exec (let* ((n (fn-lc-count fn-lbc))
              (i (fn-lc-move-sequence move))
              (fn-lbc (fn-lc-replay-move move fn-lbc)))
         (mv (and (equal n (fn-lc-count fn-lbc))
                  (equal (ec-call (fn-lbc-loc0 i fn-lbc)) (fn-lc-move-loc0 move))
                  (equal (ec-call (fn-lbc-loc1 i fn-lbc)) (fn-lc-move-loc1 move))) fn-lbc)))))

(local (verify-guards lcrp-replay-tooth
 :hints (("Goal" :use
 ((:instance lcoc-nonlocators-update-loc0
   (i (fn-lc-move-sequence move)) (v (fn-lc-move-loc0 move)))
  (:instance lcoc-nonlocators-update-loc1
   (i (fn-lc-move-sequence move)) (v (fn-lc-move-loc1 move))
   (fn-lbc (update-fn-lbc-loc0 (fn-lc-move-sequence move) (fn-lc-move-loc0 move) fn-lbc)))) :in-theory (union-theories (theory 'minimal-theory) '((:COMPOUND-RECOGNIZER NATP-COMPOUND-RECOGNIZER)
(:COMPOUND-RECOGNIZER ZP-COMPOUND-RECOGNIZER)
(:DEFINITION FN-LBC-COUNT)
(:DEFINITION FN-LBC-LOC0)
(:DEFINITION FN-LBC-LOC1)
(:DEFINITION FN-LBC-ROW-STORE)
(:DEFINITION FN-LC-COUNT)
(:DEFINITION FN-LC-REPLAY-MOVE)
(:DEFINITION FN-LOCP)
(:DEFINITION INTEGER-RANGE-P)
(:DEFINITION LCRP-WHOLE-CONCLUSION)
(:DEFINITION MAX)
(:DEFINITION NATP)
(:DEFINITION NOT)
(:DEFINITION UNSIGNED-BYTE-P)
(:DEFINITION UPDATE-FN-LBC-LOC0)
(:DEFINITION UPDATE-FN-LBC-LOC1)
(:DEFINITION UPDATE-FN-LBC-ROW-STORE)
(:DEFINITION UPDATE-NTH)
(:EXECUTABLE-COUNTERPART BINARY-+)
(:EXECUTABLE-COUNTERPART CAR)
(:EXECUTABLE-COUNTERPART CDR)
(:EXECUTABLE-COUNTERPART EXPT)
(:EXECUTABLE-COUNTERPART ZP)
(:REWRITE ADT-CAR-OF-UPDATE-NTH)
(:REWRITE ADT-CDR-OF-UPDATE-NTH)
(:REWRITE ADT-LEN-UPDATE-NTH-LOCAL)
(:REWRITE CAR-CONS)
(:REWRITE CDR-CONS)
(:REWRITE FN-CP-LEN-OF-SET-COLUMN)
(:REWRITE FN-DM-NTH-UPDATE-NTH)
(:REWRITE FN-LBC-ROWWORDS-COUNT-IS-LEN)
(:REWRITE FN-LBC-ROWWORDS-GET-LOC0-IS-NTH)
(:REWRITE FN-LBC-ROWWORDS-GET-LOC1-IS-NTH)
(:REWRITE FN-LBC-ROWWORDS-SET-LOC0-IS-UPDATE-NTH)
(:REWRITE FN-LBC-ROWWORDS-SET-LOC1-IS-UPDATE-NTH)
(:REWRITE FN-LC-NTH-1-ALIAS)
(:REWRITE FN-LC-NTH-2-ALIAS)
(:DEFINITION NTH)
(:DEFINITION LEN)
(:REWRITE PGS-X-NFIX-WHEN-NATP)
(:TYPE-PRESCRIPTION FN-LBC-P)
(:TYPE-PRESCRIPTION FN-LC-COUNT)
(:TYPE-PRESCRIPTION FN-LC-MOVE-LOC1)
(:TYPE-PRESCRIPTION FN-LOCP)
(:TYPE-PRESCRIPTION LEN)))))))

(local (defun lcrp-whole-tooth (move fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)))
 (ec-call (lcrp-replay-tooth move fn-lbc))))

(local (defun lcrp-count-mutant-tooth (move fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)))
 (let ((n (fn-lc-count fn-lbc)))
  (let ((fn-lbc (ec-call (fn-lc-replay-move move fn-lbc))))
   (mv (equal (fn-lc-count fn-lbc) (+ 1 n)) fn-lbc)))))

(local (defun lcrp-fixture-move-worker (fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)))
 (let* ((input (lcm-test-input 1)) (fn-lbc (lcm-complete-seed fn-lbc)))
  (mv (fn-lc-plan-move 0 (fn-lc-at 2 input) 1 :lc :eager (fn-lc-at 1 input) fn-lbc) fn-lbc))))

(local (defun lcrp-fixture-move ()
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-lbc
  (mv-let (move fn-lbc) (lcrp-fixture-move-worker fn-lbc) move))))

(local (verify-guards lcrp-fixture-move))

(local (defun lcrp-control (mutant fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)))
 (let* ((input (lcm-test-input 1)) (segs (fn-lc-at 1 input))
        (fn-lbc (lcm-complete-seed fn-lbc)) (move (lcrp-fixture-move))
        (beforep (fn-lbc-p fn-lbc)) (valid (fn-lc-move-recordp move fn-lbc segs)))
  (mv-let (whole fn-lbc)
   (if mutant (lcrp-count-mutant-tooth move fn-lbc) (lcrp-whole-tooth move fn-lbc))
   (mv (list beforep valid whole (fn-lc-count fn-lbc)
     (ec-call (fn-lbc-loc0 0 fn-lbc)) (ec-call (fn-lbc-loc1 0 fn-lbc))) fn-lbc)))))

(local (defun lcrp-run (mutant)
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-lbc (mv-let (out fn-lbc) (lcrp-control mutant fn-lbc) out))))

(local (verify-guards lcrp-run))

(assert-event (equal (lcrp-run nil) '(t t t 1 2 231928234004)))

(assert-event (equal (lcrp-run t) '(t t nil 1 2 231928234004)))

(local (defun lcrp-build (seed-kind fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)))
 (if (equal seed-kind :empty) fn-lbc (lcm-complete-seed fn-lbc))))

(local (defthm lcrp-empty-index-removes-recordp
 (let* ((move '(:lc-move 0 2 nil (0 0 75 54 20 0 nil nil 0) nil nil nil nil))
        (segs (fn-lc-at 1 (lcm-test-input 1)))
        (fn-lbc (create-fn-lbc))
        (fn-lbc (lcrp-build :empty fn-lbc)))
  (and (not (fn-lc-move-recordp move fn-lbc segs))
       (not (lcrp-whole-conclusion move fn-lbc))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(lcrp-build fn-lc-move-recordp lcrp-whole-conclusion fn-lc-replay-move fn-lc-count
 fn-lc-move-sequence fn-lc-move-loc0 fn-lc-move-loc1 fn-lc-head fn-lc-at-is-nth
 lcoc-count-of-loc0 lcoc-count-of-loc1 max lcoc-created-count
 fn-lbc-rowwords-count-is-len nth len car-cons cdr-cons
 (:executable-counterpart equal) (:executable-counterpart zp)
 (:executable-counterpart nfix) (:executable-counterpart max)
 (:executable-counterpart binary-+) (:executable-counterpart <)
 (:executable-counterpart true-listp) (:executable-counterpart natp)))))))

(local (defthm lcrp-move-index-bounds
 (implies (fn-lc-move-recordp move fn-lbc segs)
  (and (natp (fn-lc-move-sequence move))
       (< (fn-lc-move-sequence move) (fn-lbc-count fn-lbc))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-move-recordp))))))
(defthm fn-lc-replay-move-is-a-locator-update
  (implies (fn-lc-move-recordp move fn-lbc segs)
           (and (equal (fn-lc-replay-move move fn-lbc)
                       (update-fn-lbc-loc1
                         (fn-lc-move-sequence move) (fn-lc-move-loc1 move)
                         (update-fn-lbc-loc0
                           (fn-lc-move-sequence move) (fn-lc-move-loc0 move) fn-lbc)))
                (equal (fn-lc-count (fn-lc-replay-move move fn-lbc))
                       (fn-lc-count fn-lbc))
                (equal (fn-lc-without-locators
                         (fn-lc-columns (fn-lc-replay-move move fn-lbc)))
                       (fn-lc-without-locators (fn-lc-columns fn-lbc)))))
  :rule-classes nil
 :hints (("Goal" :use
 ((:instance lcrp-move-index-bounds)
  (:instance lcoc-nonlocators-update-loc0
   (i (fn-lc-move-sequence move)) (v (fn-lc-move-loc0 move)))
  (:instance lcoc-nonlocators-update-loc1
   (i (fn-lc-move-sequence move)) (v (fn-lc-move-loc1 move))
   (fn-lbc (update-fn-lbc-loc0 (fn-lc-move-sequence move) (fn-lc-move-loc0 move) fn-lbc))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-replay-move fn-lc-count lcoc-count-of-loc0 lcoc-count-of-loc1
 max natp nfix (:compound-recognizer natp-compound-recognizer)
 (:type-prescription fn-lbc-count))))))

(local (defun lcrp-recordp-tooth (move segs fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)))
 (mv (fn-lc-move-recordp move fn-lbc segs) fn-lbc)))
(make-event (mv-let (err expansion state) (fn-dt-expand 'fn-lc-replay-move-is-a-locator-update 'defteeth '(:claim (((record (fn-lc-move-recordp move fn-lbc segs))) (and (equal (fn-lc-replay-move move fn-lbc) (update-fn-lbc-loc1 (fn-lc-move-sequence move) (fn-lc-move-loc1 move) (update-fn-lbc-loc0 (fn-lc-move-sequence move) (fn-lc-move-loc0 move) fn-lbc))) (equal (fn-lc-count (fn-lc-replay-move move fn-lbc)) (fn-lc-count fn-lbc)) (equal (fn-lc-without-locators (fn-lc-columns (fn-lc-replay-move move fn-lbc))) (fn-lc-without-locators (fn-lc-columns fn-lbc)))))
 :subject fn-lc-replay-move
 :witness ((seed-kind :live) (move (lcrp-fixture-move)) (segs (fn-lc-at 1 (lcm-test-input 1))))
 :stobjs ((fn-lbc (lcrp-build seed-kind fn-lbc)))
 :stobj-checks
 (((fn-lc-move-recordp move fn-lbc segs) (lcrp-recordp-tooth move segs fn-lbc)
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
    '(lcrp-recordp-tooth mv-nth nth car-cons cdr-cons (:executable-counterpart zp))))))
  ((and (equal (fn-lc-replay-move move fn-lbc) (update-fn-lbc-loc1 (fn-lc-move-sequence move) (fn-lc-move-loc1 move) (update-fn-lbc-loc0 (fn-lc-move-sequence move) (fn-lc-move-loc0 move) fn-lbc))) (equal (fn-lc-count (fn-lc-replay-move move fn-lbc)) (fn-lc-count fn-lbc)) (equal (fn-lc-without-locators (fn-lc-columns (fn-lc-replay-move move fn-lbc))) (fn-lc-without-locators (fn-lc-columns fn-lbc)))) (lcrp-whole-tooth move fn-lbc)
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
    '(lcrp-whole-tooth lcrp-replay-tooth lcrp-whole-conclusion mv-nth nth car-cons cdr-cons
      (:executable-counterpart zp))))))
  ((equal (fn-lc-count (fn-lc-replay-move move fn-lbc)) (+ 1 (fn-lc-count fn-lbc))) (lcrp-count-mutant-tooth move fn-lbc)
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
    '(lcrp-count-mutant-tooth mv-nth nth car-cons cdr-cons (:executable-counterpart zp)))))))
 :breaks ((record ((seed-kind :empty)
    (move '(:lc-move 0 2 nil (0 0 75 54 20 0 nil nil 0) nil nil nil nil)))
   :logical "the empty logical creator has no row 0; total setters grow the row store"))
 :mutations ((appends-row (:conclusion (equal (fn-lc-count (fn-lc-replay-move move fn-lbc)) (+ 1 (fn-lc-count fn-lbc)))) nil
    :fault "MOVE is incorrectly charged as a newly appended catalog row"))
 :hints (("Goal" :use lcrp-empty-index-removes-recordp
   :in-theory (union-theories (theory 'minimal-theory) '(lcrp-whole-conclusion))))) state) (if err (mv err expansion state) (value (cons 'progn (fn-lc-teeth-prepare-wrappers (cdr expansion) '(("Goal" :in-theory (enable lcrp-build)))))))))

(defteeth fn-lc-replay-move-is-a-locator-update :claim (((record (fn-lc-move-recordp move fn-lbc segs))) (and (equal (fn-lc-replay-move move fn-lbc) (update-fn-lbc-loc1 (fn-lc-move-sequence move) (fn-lc-move-loc1 move) (update-fn-lbc-loc0 (fn-lc-move-sequence move) (fn-lc-move-loc0 move) fn-lbc))) (equal (fn-lc-count (fn-lc-replay-move move fn-lbc)) (fn-lc-count fn-lbc)) (equal (fn-lc-without-locators (fn-lc-columns (fn-lc-replay-move move fn-lbc))) (fn-lc-without-locators (fn-lc-columns fn-lbc)))))
 :subject fn-lc-replay-move
 :witness ((seed-kind :live) (move (lcrp-fixture-move)) (segs (fn-lc-at 1 (lcm-test-input 1))))
 :stobjs ((fn-lbc (lcrp-build seed-kind fn-lbc)))
 :stobj-checks
 (((fn-lc-move-recordp move fn-lbc segs) (lcrp-recordp-tooth move segs fn-lbc)
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
    '(lcrp-recordp-tooth mv-nth nth car-cons cdr-cons (:executable-counterpart zp))))))
  ((and (equal (fn-lc-replay-move move fn-lbc) (update-fn-lbc-loc1 (fn-lc-move-sequence move) (fn-lc-move-loc1 move) (update-fn-lbc-loc0 (fn-lc-move-sequence move) (fn-lc-move-loc0 move) fn-lbc))) (equal (fn-lc-count (fn-lc-replay-move move fn-lbc)) (fn-lc-count fn-lbc)) (equal (fn-lc-without-locators (fn-lc-columns (fn-lc-replay-move move fn-lbc))) (fn-lc-without-locators (fn-lc-columns fn-lbc)))) (lcrp-whole-tooth move fn-lbc)
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
    '(lcrp-whole-tooth lcrp-replay-tooth lcrp-whole-conclusion mv-nth nth car-cons cdr-cons
      (:executable-counterpart zp))))))
  ((equal (fn-lc-count (fn-lc-replay-move move fn-lbc)) (+ 1 (fn-lc-count fn-lbc))) (lcrp-count-mutant-tooth move fn-lbc)
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
    '(lcrp-count-mutant-tooth mv-nth nth car-cons cdr-cons (:executable-counterpart zp)))))))
 :breaks ((record ((seed-kind :empty)
    (move '(:lc-move 0 2 nil (0 0 75 54 20 0 nil nil 0) nil nil nil nil)))
   :logical "the empty logical creator has no row 0; total setters grow the row store"))
 :mutations ((appends-row (:conclusion (equal (fn-lc-count (fn-lc-replay-move move fn-lbc)) (+ 1 (fn-lc-count fn-lbc)))) nil
    :fault "MOVE is incorrectly charged as a newly appended catalog row"))
 :hints (("Goal" :use lcrp-empty-index-removes-recordp
   :in-theory (union-theories (theory 'minimal-theory) '(lcrp-whole-conclusion)))))

(defteeth-check (fn-lc-replay-move-is-a-locator-update))

; Statement first, proposed status-only DROP (not yet a proved keystone):
; (defthm fn-lc-clean-moves-only-the-locator (let* ((before (fn-lc-columns fn-lbc)) (i (fn-lc-move-sequence move)) (a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc)) (out (fn-lc-clean move disk segs outcome fn-lbc))) (implies (equal (mv-nth 0 out) :ok) (and (equal (fn-lc-without-locators (fn-lc-columns (mv-nth 1 out))) (fn-lc-without-locators before)) (equal (fn-lc-columns (mv-nth 1 out)) (fn-lc-columns (fn-lc-replay-move move fn-lbc))) (equal (fn-lc-read-range (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) (mv-nth 3 out)) (fn-lc-read-range a b segs)) (equal (fn-lc-read-home-frame (fn-lc-home-position (fn-lc-move-loc0 move) (fn-lc-move-loc1 move)) (mv-nth 3 out)) (fn-lc-read-home-frame (fn-lc-home-position a b) segs)) (equal (fn-lc-read-suf (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) (mv-nth 3 out)) (fn-lc-read-suf a b segs))))) :rule-classes nil)

(local (defthm lccm-non-nil-nth-is-in-range
 (implies (and (natp i) (nth i xs)) (< i (len xs)))
 :hints (("Goal" :induct (nth i xs) :expand ((nth i xs))
 :in-theory (union-theories (theory 'minimal-theory)
 '(nth len natp zp (:induction nth) (:type-prescription len) endp car-cons cdr-cons))))))

(local (defthm lccm-update-current-value
 (implies (and (natp i) (< i (len xs)))
  (equal (update-nth i (nth i xs) xs) xs))
 :hints (("Goal" :induct (nth i xs)
 :expand ((nth i xs) (:free (v) (update-nth i v xs)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(nth update-nth len natp zp (:induction nth) (:type-prescription len)
 endp car-cons cdr-cons fold-consts-in-+ fix unicity-of-0))))))

(local (defthm lccm-columns-determine-nonempty-row-store
 (implies (and (consp (nth *fn-lbc-row-store* a))
               (consp (nth *fn-lbc-row-store* b))
               (equal (fn-lc-columns-value a) (fn-lc-columns-value b)))
  (equal (nth *fn-lbc-row-store* a) (nth *fn-lbc-row-store* b)))
 :hints (("Goal" :use
 ((:instance fn-lc-column-row-store-of-columns-value (value a))
  (:instance fn-lc-column-row-store-of-columns-value (value b)))
 :in-theory (theory 'minimal-theory)))))

(local (defthm lccm-set-current-loc0
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)) (fn-lbc-loc0 i fn-lbc))
  (equal (update-fn-lbc-loc0 i (fn-lbc-loc0 i fn-lbc) fn-lbc) fn-lbc))
 :hints (("Goal" :cases ((consp fn-lbc)) :expand ((len fn-lbc)) :use ((:instance lccm-update-current-value (i 0) (xs fn-lbc)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-count fn-lbc-loc0 fn-lbc-row-store update-fn-lbc-loc0 update-fn-lbc-row-store
 fn-lbc-rowwords-count-is-len fn-lbc-rowwords-get-loc0-is-nth
 fn-lbc-rowwords-set-loc0-is-update-nth lccm-update-current-value
 lccm-non-nil-nth-is-in-range fn-dm-nth-update-nth fn-dm-nth-of-zeros
 nth len natp zp (:type-prescription len) car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal)
 (:executable-counterpart zp)))))))

(local (defthm lccm-loc0-of-replay
 (implies (natp (fn-lc-move-sequence move))
  (equal (fn-lbc-loc0 (fn-lc-move-sequence move) (fn-lc-replay-move move fn-lbc))
         (fn-lc-move-loc0 move)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-loc0 fn-lbc-row-store fn-lc-replay-move
 update-fn-lbc-loc0 update-fn-lbc-loc1 update-fn-lbc-row-store
 fn-lbc-rowwords-get-loc0-is-nth fn-lbc-rowwords-set-loc0-is-update-nth
 fn-lbc-rowwords-set-loc1-is-update-nth fn-dm-nth-update-nth
 (:executable-counterpart nfix) (:executable-counterpart equal)))))))

(local (defthm lccm-set-current-loc1
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)) (fn-lbc-loc1 i fn-lbc))
  (equal (update-fn-lbc-loc1 i (fn-lbc-loc1 i fn-lbc) fn-lbc) fn-lbc))
 :hints (("Goal" :cases ((consp fn-lbc)) :expand ((len fn-lbc)) :use ((:instance lccm-update-current-value (i 0) (xs fn-lbc)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-count fn-lbc-loc1 fn-lbc-row-store update-fn-lbc-loc1 update-fn-lbc-row-store
 fn-lbc-rowwords-count-is-len fn-lbc-rowwords-get-loc1-is-nth
 fn-lbc-rowwords-set-loc1-is-update-nth lccm-update-current-value
 lccm-non-nil-nth-is-in-range fn-dm-nth-update-nth fn-dm-nth-of-zeros
 nth len natp zp (:type-prescription len) car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal)
 (:executable-counterpart zp)))))))

(local (defthm lccm-loc1-of-replay
 (implies (natp (fn-lc-move-sequence move))
  (equal (fn-lbc-loc1 (fn-lc-move-sequence move) (fn-lc-replay-move move fn-lbc))
         (fn-lc-move-loc1 move)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-loc1 fn-lbc-row-store fn-lc-replay-move
 update-fn-lbc-loc0 update-fn-lbc-loc1 update-fn-lbc-row-store
 fn-lbc-rowwords-get-loc1-is-nth fn-lbc-rowwords-set-loc0-is-update-nth
 fn-lbc-rowwords-set-loc1-is-update-nth fn-dm-nth-update-nth
 (:executable-counterpart nfix) (:executable-counterpart equal)))))))

(local (defthm lccm-positive-count-has-row-store
 (implies (< 0 (fn-lbc-count fn-lbc)) (consp (nth *fn-lbc-row-store* fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-count fn-lbc-row-store fn-lbc-rowwords-count-is-len len))))))

(local (defthm lccm-count-of-bounded-replay
 (implies (and (natp (fn-lc-move-sequence move))
               (< (fn-lc-move-sequence move) (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-count (fn-lc-replay-move move fn-lbc)) (fn-lbc-count fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-replay-move lcoc-count-of-loc0 lcoc-count-of-loc1 max natp nfix
 (:compound-recognizer natp-compound-recognizer) (:type-prescription fn-lbc-count)))))))

(local (defthm lccm-row-store-determines-locators
 (implies (equal (nth *fn-lbc-row-store* a) (nth *fn-lbc-row-store* b))
  (and (equal (fn-lbc-loc0 i a) (fn-lbc-loc0 i b))
       (equal (fn-lbc-loc1 i a) (fn-lbc-loc1 i b))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-loc0 fn-lbc-loc1 fn-lbc-row-store
 fn-lbc-rowwords-get-loc0-is-nth fn-lbc-rowwords-get-loc1-is-nth))))))

(local (defthm lccm-replay-fixed-when-locators-match
 (implies (and (natp (fn-lc-move-sequence move))
               (< (fn-lc-move-sequence move) (fn-lbc-count fn-lbc))
               (fn-locp (fn-lc-move-loc0 move) (fn-lc-move-loc1 move))
               (equal (fn-lbc-loc0 (fn-lc-move-sequence move) fn-lbc) (fn-lc-move-loc0 move))
               (equal (fn-lbc-loc1 (fn-lc-move-sequence move) fn-lbc) (fn-lc-move-loc1 move)))
  (equal (fn-lc-replay-move move fn-lbc) fn-lbc))
 :hints (("Goal" :use
 ((:instance lccm-set-current-loc0 (i (fn-lc-move-sequence move)))
  (:instance lccm-set-current-loc1 (i (fn-lc-move-sequence move))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-replay-move fn-locp unsigned-byte-p integer-range-p
 (:executable-counterpart expt) (:executable-counterpart integerp)))))))

(local (defthm lccm-replay-columns-equal-iff-locators-match
 (implies (and (natp (fn-lc-move-sequence move))
               (< (fn-lc-move-sequence move) (fn-lbc-count fn-lbc))
               (fn-locp (fn-lc-move-loc0 move) (fn-lc-move-loc1 move)))
  (equal (equal (fn-lc-columns (fn-lc-replay-move move fn-lbc)) (fn-lc-columns fn-lbc))
   (and (equal (fn-lbc-loc0 (fn-lc-move-sequence move) fn-lbc) (fn-lc-move-loc0 move))
        (equal (fn-lbc-loc1 (fn-lc-move-sequence move) fn-lbc) (fn-lc-move-loc1 move)))))
 :hints (("Goal" :use
 ((:instance lccm-columns-determine-nonempty-row-store
   (a (fn-lc-replay-move move fn-lbc)) (b fn-lbc))
  (:instance lccm-positive-count-has-row-store)
  (:instance lccm-positive-count-has-row-store (fn-lbc (fn-lc-replay-move move fn-lbc)))
  (:instance lccm-row-store-determines-locators
   (i (fn-lc-move-sequence move)) (a (fn-lc-replay-move move fn-lbc)) (b fn-lbc))
  (:instance lccm-replay-fixed-when-locators-match))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-columns lccm-count-of-bounded-replay lccm-loc0-of-replay lccm-loc1-of-replay
 natp (:compound-recognizer natp-compound-recognizer) (:type-prescription fn-lbc-count)))))))

(local (defthm lccm-bounded-replay-keeps-other-columns
 (implies (and (natp (fn-lc-move-sequence move))
               (< (fn-lc-move-sequence move) (fn-lbc-count fn-lbc)))
  (equal (fn-lc-without-locators (fn-lc-columns (fn-lc-replay-move move fn-lbc)))
         (fn-lc-without-locators (fn-lc-columns fn-lbc))))
 :hints (("Goal" :use
 ((:instance lcoc-nonlocators-update-loc0
   (i (fn-lc-move-sequence move)) (v (fn-lc-move-loc0 move)))
  (:instance lcoc-nonlocators-update-loc1
   (i (fn-lc-move-sequence move)) (v (fn-lc-move-loc1 move))
   (fn-lbc (update-fn-lbc-loc0 (fn-lc-move-sequence move) (fn-lc-move-loc0 move) fn-lbc))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-replay-move lcoc-count-of-loc0 max natp nfix
 (:compound-recognizer natp-compound-recognizer) (:type-prescription fn-lbc-count)))))))

(local (defthm lccm-clean-column-observation
 (let ((out (fn-lc-clean move disk segs outcome fn-lbc)))
  (implies (and (natp (fn-lc-move-sequence move))
                (< (fn-lc-move-sequence move) (fn-lbc-count fn-lbc))
                (fn-locp (fn-lc-move-loc0 move) (fn-lc-move-loc1 move)))
   (equal
    (and (equal (fn-lc-without-locators (fn-lc-columns (mv-nth 1 out)))
                (fn-lc-without-locators (fn-lc-columns fn-lbc)))
         (equal (fn-lc-columns (mv-nth 1 out))
                (fn-lc-columns (fn-lc-replay-move move fn-lbc))))
    (and (equal (fn-lbc-loc0 (fn-lc-move-sequence move) (mv-nth 1 out)) (fn-lc-move-loc0 move))
         (equal (fn-lbc-loc1 (fn-lc-move-sequence move) (mv-nth 1 out)) (fn-lc-move-loc1 move))))))
 :hints (("Goal" :use ((:instance lccm-replay-columns-equal-iff-locators-match))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-clean-column-effect-by-definition lccm-bounded-replay-keeps-other-columns
 lccm-loc0-of-replay lccm-loc1-of-replay))))))

(local (defun-nx lccm-whole-clean-conclusion (mutant move disk segs outcome fn-lbc)
 (let* ((before (fn-lc-columns fn-lbc)) (i (fn-lc-move-sequence move)) (a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc)) (out (fn-lc-clean move disk segs outcome fn-lbc))) (and (equal (fn-lc-without-locators (fn-lc-columns (mv-nth 1 out))) (fn-lc-without-locators before)) (equal (fn-lc-columns (mv-nth 1 out)) (fn-lc-columns (fn-lc-replay-move move fn-lbc))) (equal (fn-lc-read-range (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) (mv-nth 3 out)) (fn-lc-read-range a b segs)) (equal (fn-lc-read-home-frame (fn-lc-home-position (fn-lc-move-loc0 move) (fn-lc-move-loc1 move)) (mv-nth 3 out)) (fn-lc-read-home-frame (fn-lc-home-position a b) segs)) (if mutant (not (equal (fn-lc-read-suf (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) (mv-nth 3 out)) (fn-lc-read-suf a b segs))) (equal (fn-lc-read-suf (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) (mv-nth 3 out)) (fn-lc-read-suf a b segs)))))))

(local (defun lccm-clean-tooth (mutant move disk segs outcome fn-lbc)
 (declare (xargs :stobjs fn-lbc :verify-guards nil
 :guard (and (fn-lbc-p fn-lbc) (natp (fn-lc-move-sequence move))
   (< (fn-lc-move-sequence move) (fn-lc-count fn-lbc))
   (fn-locp (fn-lc-move-loc0 move) (fn-lc-move-loc1 move)))))
 (mbe :logic
  (let ((answer (lccm-whole-clean-conclusion mutant move disk segs outcome fn-lbc)))
   (mv-let (status fn-lbc afterdisk aftersegs trace) (fn-lc-clean move disk segs outcome fn-lbc)
    (declare (ignore status afterdisk aftersegs trace)) (mv answer fn-lbc)))
 :exec
  (let* ((i (fn-lc-move-sequence move))
         (a (ec-call (fn-lbc-loc0 i fn-lbc))) (b (ec-call (fn-lbc-loc1 i fn-lbc)))
         (wire (ec-call (fn-lc-read-range a b segs)))
         (home (ec-call (fn-lc-read-home-frame (ec-call (fn-lc-home-position a b)) segs)))
         (suf (fn-lc-read-suf a b segs))
         (new0 (fn-lc-move-loc0 move)) (new1 (fn-lc-move-loc1 move)))
   (mv-let (status fn-lbc afterdisk aftersegs trace) (fn-lc-clean move disk segs outcome fn-lbc)
    (declare (ignore status afterdisk trace))
    (mv (and (equal (ec-call (fn-lbc-loc0 i fn-lbc)) new0)
             (equal (ec-call (fn-lbc-loc1 i fn-lbc)) new1)
             (equal (ec-call (fn-lc-read-range new0 new1 aftersegs)) wire)
             (equal (ec-call (fn-lc-read-home-frame (ec-call (fn-lc-home-position new0 new1)) aftersegs)) home)
             (if mutant (not (equal (fn-lc-read-suf new0 new1 aftersegs) suf))
                        (equal (fn-lc-read-suf new0 new1 aftersegs) suf))) fn-lbc))))))

(local (verify-guards lccm-clean-tooth
 :hints (("Goal" :use ((:instance lccm-clean-column-observation))
 :in-theory (union-theories (theory 'minimal-theory)
 '(lccm-whole-clean-conclusion fn-lc-count mv-nth nth car-cons cdr-cons
 (:executable-counterpart zp)))))))

(local (defun lccm-whole-clean-tooth (mutant move disk segs outcome fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)))
 (ec-call (lccm-clean-tooth mutant move disk segs outcome fn-lbc))))

(local (defun lccm-clean-control (mutant fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)))
 (let* ((input (lcm-test-input 1)) (segs (fn-lc-at 1 input))
        (fn-lbc (lcm-complete-seed fn-lbc)) (move (lcrp-fixture-move))
        (beforep (fn-lbc-p fn-lbc))
        (resolves (ec-call (fn-lc-locators-resolve fn-lbc segs)))
        (valid (fn-lc-move-recordp move fn-lbc segs)))
  (mv-let (whole fn-lbc)
   (lccm-whole-clean-tooth mutant move (fn-lc-at 0 input) segs '(:ok :ok) fn-lbc)
   (mv (list beforep resolves valid whole
        (ec-call (fn-lbc-loc0 0 fn-lbc)) (ec-call (fn-lbc-loc1 0 fn-lbc))) fn-lbc)))))

(local (defun lccm-clean-run (mutant)
 (declare (xargs :guard t :verify-guards nil))
 (with-local-stobj fn-lbc
  (mv-let (out fn-lbc) (lccm-clean-control mutant fn-lbc) out))))

(local (verify-guards lccm-clean-run))

(assert-event (equal (lccm-clean-run nil) '(t t t t 2 231928234004)))

(assert-event (equal (lccm-clean-run t) '(t t t nil 2 231928234004)))

(assert-event (equal (fn-lc-at 2 (lcm-test-move-fixture 1 0 1 '(:ok :ok))) :ok))

; Retained success-premise removal: a total logical creator, no live bad index.
(local (defthm lccm-empty-replay-columns-differ
 (let* ((move '(:lc-move 0 2 nil (0 0 75 54 20 0 nil nil 0) nil nil nil nil))
        (fn-lbc (create-fn-lbc)))
  (not (equal (fn-lc-columns (fn-lc-replay-move move fn-lbc)) (fn-lc-columns fn-lbc))))
 :rule-classes nil
 :hints (("Goal" :use
 ((:instance fn-lc-column-row-store-of-columns-value (value (create-fn-lbc)))
  (:instance fn-lc-column-row-store-of-columns-value
   (value (fn-lc-replay-move '(:lc-move 0 2 nil (0 0 75 54 20 0 nil nil 0) nil nil nil nil) (create-fn-lbc)))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-columns fn-lc-replay-move fn-lc-move-sequence fn-lc-move-loc0 fn-lc-move-loc1
 fn-lc-head fn-lc-at-is-nth create-fn-lbc update-fn-lbc-loc0 update-fn-lbc-loc1
 fn-lbc-row-store update-fn-lbc-row-store
 fn-lbc-rowwords-set-loc0-is-update-nth fn-lbc-rowwords-set-loc1-is-update-nth
 fn-dm-nth-update-nth nth update-nth len car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal)
 (:executable-counterpart zp) (:executable-counterpart binary-+)
 (:executable-counterpart binary-*)))))))

(local (defthm lccm-empty-state-removes-success
 (let* ((move '(:lc-move 0 2 nil (0 0 75 54 20 0 nil nil 0) nil nil nil nil))
        (fn-lbc (create-fn-lbc)))
  (and (not (equal (mv-nth 0 (fn-lc-clean move nil nil '(:ok :ok) fn-lbc)) :ok))
       (not (lccm-whole-clean-conclusion nil move nil nil '(:ok :ok) fn-lbc))))
 :rule-classes nil
 :hints (("Goal" :use lccm-empty-replay-columns-differ
 :in-theory (union-theories (theory 'minimal-theory)
 '(lccm-whole-clean-conclusion fn-lc-clean fn-lc-move-recordp lcoc-created-count
 fn-lc-move-sequence fn-lc-at-is-nth fn-lc-head fn-lc-count mv-nth nth
 car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart equal)
 (:executable-counterpart natp) (:executable-counterpart true-listp)
 (:executable-counterpart len) (:executable-counterpart <)))))))

; Small, closed-theory facts for the real MOVE frame and served readers.
(local (defthm lccm-range-read-is-list
 (implies (not (equal (fn-lb-log-model-read-range id off n segs) :bad))
  (true-listp (fn-lb-log-model-read-range id off n segs)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-log-model-read-range lccm-true-listp-take))))))

(local (defthm lccm-home-read-is-list
 (implies (not (equal (fn-lb-log-model-read-home-frame pos segs) :bad))
  (true-listp (fn-lb-log-model-read-home-frame pos segs)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-log-model-read-home-frame lccm-range-read-is-list))))))

(local (defthm lccm-list-fix-of-list
 (implies (true-listp xs) (equal (true-list-fix xs) xs))
 :hints (("Goal" :induct (true-listp xs)
 :in-theory (union-theories (theory 'minimal-theory)
 '(true-listp true-list-fix (:induction true-listp) car-cons cdr-cons))))))

(local (defthm lccm-range-read-needs-segments
 (implies (not (equal (fn-lb-log-model-read-range id off n segs) :bad)) (consp segs))
 :hints (("Goal" :cases ((consp segs))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-log-model-read-range fn-lb-log-model-segment))))))

(local (defthm lccm-plan-move-by-definition
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lc-plan-move i header k r mode segs fn-lbc) (let* ((row (ec-call (fn-lc-bound-row i fn-lbc segs))) (a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc)) (id (fn-lc-last-segment-id (fn-lc-ordered-segments segs))) (segment (ec-call (fn-lb-log-model-segment id segs))) (start (len (fn-lc-at 1 segment))) (wire (ec-call (fn-lc-read-range a b segs))) (home (fn-lc-read-suf a b segs)) (prev (fn-lc-at 3 (fn-lc-tail-scan segs header))) (frame (ec-call (fn-lc-move-frame prev i wire home))) (payload (ec-call (fn-lb-log-payload row segs))) (entry (list (len (fn-lc-at 2 segment)) start (- (len frame) *fn-frame-trailer-octets*) (+ start *fn-frame-header-octets* 32 12) (len wire) (fn-record-payload row) payload (ec-call (fn-lb-log-model-homes row)) i))) (list :lc-move i id frame entry header k r mode))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lc-plan-move))))))

(local (defthm lccm-fresh-home-entry-in-append
 (implies (and (posp pos) (not (fn-lb-log-model-home-entry pos entries))
               (equal pos (+ (nfix (nth 3 entry)) (nfix (nth 4 entry)))))
  (equal (fn-lb-log-model-home-entry pos (append entries (list entry))) entry))
 :hints (("Goal" :induct (len entries)
 :expand ((fn-lb-log-model-home-entry pos (append entries (list entry))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-log-model-home-entry binary-append len posp nfix nth (:executable-counterpart binary-+) (:induction len) car-cons cdr-cons))))))

(local (defthm lccm-packed-locator-accessors
 (implies (and (unsigned-byte-p 64 id) (unsigned-byte-p 32 off) (unsigned-byte-p 32 n))
  (and (equal (fn-loc-segment id (+ (* off 4294967296) n)) id)
       (equal (fn-loc-offset id (+ (* off 4294967296) n)) off)
       (equal (fn-loc-len id (+ (* off 4294967296) n)) n)))
 :hints (("Goal" :use ((:instance fn-loc-accessors-of-make (seg id) (len n)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-loc-make nfix natp unsigned-byte-p integer-range-p mv-nth nth
 car-cons cdr-cons (:executable-counterpart expt) (:executable-counterpart zp)))))))

(local (defthm lccm-clean-accepted-effects-by-definition
 (let ((out (fn-lc-clean move disk segs outcome fn-lbc)))
  (implies (equal (mv-nth 0 out) :ok)
   (and (fn-lc-move-recordp move fn-lbc segs)
        (equal (mv-nth 1 out) (fn-lc-replay-move move fn-lbc))
        (equal (mv-nth 3 out)
         (fn-lc-append-prepared (fn-lc-move-packet move)
          (fn-lc-last-segment-id (fn-lc-ordered-segments segs))
          (fn-lc-tail-unit (fn-lc-at 5 move)) segs)))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-clean fn-lc-commit fn-lc-commit-prepared fn-lc-append-prepared-columns
 fn-lc-prepare-tail fn-lc-move-packet fn-lc-head fn-lc-at-is-nth
 mv-nth nth car-cons cdr-cons (:executable-counterpart zp)
 (:executable-counterpart equal)))))))

(local (defthm lccm-range-permission-at-head
 (implies (and (fn-lb-log-model-entryp entry) (natp off) (natp n)
               (<= (nth 1 entry) off)
               (<= (+ off n) (+ (nth 1 entry) (nth 2 entry) 32)))
  (fn-lb-log-model-range-in-entries off n (list entry)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-log-model-range-in-entries car-cons cdr-cons))))))

(local (defthm lccm-entryp-is-consp
 (implies (fn-lb-log-model-entryp entry) (consp entry))
 :rule-classes :forward-chaining
 :hints (("Goal" :cases ((consp entry))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-log-model-entryp len true-listp (:executable-counterpart len)
 (:executable-counterpart equal)))))))

(local (defthm lccm-framed-wire-copy
 (let* ((old (fn-lb-log-model-segment id segs)) (start (len (cadr old)))
        (frame (fn-lc-move-frame prev i wire home))
        (word (+ (* (+ start 54) 4294967296) (len wire))))
  (implies (and (fn-lc-segsp segs) old
                (unsigned-byte-p 64 id) (unsigned-byte-p 32 (+ start 54))
                (unsigned-byte-p 32 (len wire))
                (equal (len prev) 32) (true-listp wire)
                (fn-lb-log-model-entryp entry)
                (equal (nth 1 entry) start)
                (equal (nth 2 entry) (- (len frame) 32)))
   (equal (fn-lc-read-range id word
            (fn-lc-append-prepared (list nil frame entry) id unit segs)) wire)))
 :hints (("Goal" :use
 ((:instance lccm-prepared-frame-range
   (frame (fn-lc-move-frame prev i wire home)) (offset 54) (n (len wire)))
  (:instance lccm-packed-locator-accessors
   (off (+ (len (cadr (fn-lb-log-model-segment id segs))) 54)) (n (len wire)))
  (:instance lccm-move-frame-wire-slice))
 :in-theory (union-theories (theory 'minimal-theory)
 '(lccm-entryp-is-consp fn-lc-read-range lccm-range-permission-at-head lccm-move-frame-length
 lccm-list-fix-of-list natp (:type-prescription len) car-cons cdr-cons
 (:executable-counterpart equal) (:executable-counterpart natp)))))))

(local (defthm lccm-nth-cons
 (equal (nth n (cons a xs)) (if (zp n) a (nth (+ -1 n) xs)))
 :hints (("Goal" :expand ((nth n (cons a xs)))
 :in-theory (union-theories (theory 'minimal-theory) '(nth car-cons cdr-cons))))))

(local (defthm lccm-len-cons
 (equal (len (cons a xs)) (+ 1 (len xs)))
 :hints (("Goal" :expand ((len (cons a xs)))
 :in-theory (union-theories (theory 'minimal-theory) '(len cdr-cons))))))

(local (defthm lccm-listp-cons
 (equal (true-listp (cons a xs)) (true-listp xs))
 :hints (("Goal" :expand ((true-listp (cons a xs)))
 :in-theory (union-theories (theory 'minimal-theory) '(true-listp cdr-cons))))))

(local (defthm lccm-nfix-nat
 (implies (natp x) (equal (nfix x) x))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))

(local (defthm lccm-locp-id-type
 (implies (fn-locp a b) (unsigned-byte-p 64 a))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-locp))))))

(local (defthm lccm-frame-locator-bounds
 (implies (and (natp start) (natp n) (natp home) (< (+ start 86 n home) 4294967296))
  (and (unsigned-byte-p 32 (+ start 54)) (unsigned-byte-p 32 n)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(natp unsigned-byte-p integer-range-p (:executable-counterpart expt)))))))

(local (defthm lccm-protected-length-normalize
 (implies (and (natp wire) (natp home))
  (equal (+ (+ 86 wire home) -32) (+ 54 wire home)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(natp))))))

(local (defthm lccm-planned-move-geometry
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)) (fn-lc-move-recordp (fn-lc-plan-move i header k r mode segs fn-lbc) fn-lbc segs))
  (and (fn-lc-segsp segs) (fn-lb-log-model-segment (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) segs) (unsigned-byte-p 64 (fn-lc-last-segment-id (fn-lc-ordered-segments segs)))
       (unsigned-byte-p 32 (+ (len (fn-lc-at 1 (fn-lb-log-model-segment (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) segs))) 54)) (unsigned-byte-p 32 (len (fn-lc-read-range (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs)))
       (equal (len (fn-lc-at 3 (fn-lc-tail-scan segs header))) 32) (true-listp (fn-lc-read-range (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs)) (true-listp (fn-lc-read-suf (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs))
       (fn-lb-log-model-entryp (list (len (fn-lc-at 2 (fn-lb-log-model-segment (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) segs))) (len (fn-lc-at 1 (fn-lb-log-model-segment (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) segs))) (- (len (fn-lc-move-frame (fn-lc-at 3 (fn-lc-tail-scan segs header)) i (fn-lc-read-range (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs) (fn-lc-read-suf (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs))) 32) (+ (len (fn-lc-at 1 (fn-lb-log-model-segment (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) segs))) 54) (len (fn-lc-read-range (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs)) (fn-record-payload (fn-lc-bound-row i fn-lbc segs)) (fn-lb-log-payload (fn-lc-bound-row i fn-lbc segs) segs) (fn-lb-log-model-homes (fn-lc-bound-row i fn-lbc segs)) i))))
 :hints (("Goal" :use
 ((:instance lccm-frame-locator-bounds (start (len (fn-lc-at 1 (fn-lb-log-model-segment (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) segs)))) (n (len (fn-lc-read-range (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs))) (home (len (fn-lc-read-suf (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs))))
  (:instance lccm-move-frame-prev-width (frame (fn-lc-move-frame (fn-lc-at 3 (fn-lc-tail-scan segs header)) i (fn-lc-read-range (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs) (fn-lc-read-suf (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs))) (prev (fn-lc-at 3 (fn-lc-tail-scan segs header))) (max (fn-lc-tail-max header)))
  (:instance lccm-locp-id-type (a (fn-lc-last-segment-id (fn-lc-ordered-segments segs))) (b (fn-lc-move-loc1 (fn-lc-plan-move i header k r mode segs fn-lbc)))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(lccm-protected-length-normalize lccm-plan-move-by-definition fn-lc-move-recordp fn-lc-move-loc0 fn-lc-move-loc1
 fn-lc-move-sequence fn-lc-at-is-nth fn-lc-head fn-lc-nth-1-alias fn-lc-nth-2-alias
 lccm-nth-cons lccm-len-cons lccm-listp-cons lccm-nfix-nat
 fn-lc-read-range fn-lc-read-suf fn-lc-read-home-frame fn-lc-home-position
 lccm-move-frame-length lccm-range-read-needs-segments lccm-last-ordered-segment-exists
 lccm-range-read-is-list lccm-home-read-is-list
 natp (:type-prescription len) (:compound-recognizer natp-compound-recognizer)
 car-cons cdr-cons (:executable-counterpart true-listp) (:executable-counterpart len)
 (:executable-counterpart equal) (:executable-counterpart zp) (:executable-counterpart binary-+)
 fold-consts-in-+))))))

(local (defthm lccm-planned-wire-copy
 (let* ((move (fn-lc-plan-move i header k r mode segs fn-lbc))
        (after (fn-lc-append-prepared (fn-lc-move-packet move) (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) (fn-lc-tail-unit header) segs)))
  (implies (and (natp i) (< i (fn-lbc-count fn-lbc)) (fn-lc-move-recordp move fn-lbc segs))
   (equal (fn-lc-read-range (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) after) (fn-lc-read-range (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs))))
 :hints (("Goal" :use
 ((:instance lccm-planned-move-geometry)
  (:instance lccm-framed-wire-copy (id (fn-lc-last-segment-id (fn-lc-ordered-segments segs))) (entry (list (len (fn-lc-at 2 (fn-lb-log-model-segment (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) segs))) (len (fn-lc-at 1 (fn-lb-log-model-segment (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) segs))) (- (len (fn-lc-move-frame (fn-lc-at 3 (fn-lc-tail-scan segs header)) i (fn-lc-read-range (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs) (fn-lc-read-suf (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs))) 32) (+ (len (fn-lc-at 1 (fn-lb-log-model-segment (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) segs))) 54) (len (fn-lc-read-range (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs)) (fn-record-payload (fn-lc-bound-row i fn-lbc segs)) (fn-lb-log-payload (fn-lc-bound-row i fn-lbc segs) segs) (fn-lb-log-model-homes (fn-lc-bound-row i fn-lbc segs)) i))
    (prev (fn-lc-at 3 (fn-lc-tail-scan segs header))) (wire (fn-lc-read-range (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs)) (home (fn-lc-read-suf (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs)) (unit (fn-lc-tail-unit header))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(lccm-plan-move-by-definition fn-lc-move-loc0 fn-lc-move-loc1 fn-lc-move-packet
 fn-lc-at-is-nth fn-lc-nth-1-alias fn-lc-nth-2-alias lccm-nth-cons lccm-len-cons
 lccm-nfix-nat natp (:type-prescription len) car-cons cdr-cons
 (:executable-counterpart equal) (:executable-counterpart len) (:executable-counterpart zp)
 (:executable-counterpart binary-+) associativity-of-+ commutativity-of-+ commutativity-2-of-+ fold-consts-in-+))))))

(local (defthm lccm-home-length-cancel
 (implies (and (natp start) (natp wire) (natp home)
               (equal protected (+ 54 home wire)))
  (equal (+ start protected (- (+ 54 wire start))) home))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(natp))))))

(local (defthm lccm-framed-home-copy
 (let* ((old (fn-lb-log-model-segment id segs)) (start (len (cadr old)))
        (frame (fn-lc-move-frame prev i wire home))
        (word (+ (* (+ start 54) 4294967296) (len wire))))
  (implies (and (fn-lc-segsp segs) old
                (unsigned-byte-p 64 id) (unsigned-byte-p 32 (+ start 54))
                (unsigned-byte-p 32 (len wire))
                (equal (len prev) 32) (true-listp home)
                (fn-lb-log-model-entryp entry)
                (equal (nth 1 entry) start)
                (equal (nth 2 entry) (- (len frame) 32))
                (equal (nth 3 entry) (+ start 54)) (equal (nth 4 entry) (len wire))
                (not (fn-lb-log-model-home-entry (+ start 54 (len wire)) (caddr old))))
   (equal (fn-lc-read-home-frame (fn-lc-home-position id word)
            (fn-lc-append-prepared (list nil frame entry) id unit segs)) home)))
 :hints (("Goal" :use
 ((:instance lccm-home-length-cancel (start (nth 1 entry)) (wire (len wire)) (home (len home)) (protected (nth 2 entry)))
  (:instance lccm-prepared-frame-range
   (frame (fn-lc-move-frame prev i wire home)) (offset (+ 54 (len wire))) (n (len home)))
  (:instance lccm-packed-locator-accessors
   (off (+ (len (cadr (fn-lb-log-model-segment id segs))) 54)) (n (len wire)))
  (:instance lccm-fresh-home-entry-in-append
   (entries (caddr (fn-lb-log-model-segment id segs)))
   (pos (+ (len (cadr (fn-lb-log-model-segment id segs))) 54 (len wire))))
  (:instance lccm-move-frame-home-slice))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-read-home-frame fn-lc-home-position fn-lb-log-model-read-home-frame
 lccm-entryp-is-consp lccm-segment-of-append-prepared lccm-range-permission-at-head
 lccm-move-frame-length lccm-list-fix-of-list lccm-nfix-nat
 natp posp lccm-nth-cons (:type-prescription len) car-cons cdr-cons
 (:executable-counterpart zp) (:executable-counterpart equal) (:executable-counterpart natp)
 associativity-of-+ commutativity-of-+ commutativity-2-of-+ fold-consts-in-+ fix unicity-of-0))))))

(local (defthm lccm-planned-home-is-fresh
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)) (fn-lc-move-recordp (fn-lc-plan-move i header k r mode segs fn-lbc) fn-lbc segs))
 (not (fn-lb-log-model-home-entry (+ (len (fn-lc-at 1 (fn-lb-log-model-segment (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) segs))) 54 (len (fn-lc-read-range (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs))) (fn-lc-at 2 (fn-lb-log-model-segment (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) segs)))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-move-recordp fn-lc-move-target-freshp lccm-plan-move-by-definition fn-lc-move-loc0
 fn-lc-at-is-nth fn-lc-nth-1-alias fn-lc-nth-2-alias lccm-nth-cons lccm-len-cons
 lccm-nfix-nat natp (:type-prescription len) car-cons cdr-cons
 (:executable-counterpart equal) (:executable-counterpart len) (:executable-counterpart zp)
 (:executable-counterpart binary-+) associativity-of-+ commutativity-of-+
 commutativity-2-of-+ fold-consts-in-+))))))

(local (defthm lccm-planned-home-copy
 (let* ((move (fn-lc-plan-move i header k r mode segs fn-lbc))
        (after (fn-lc-append-prepared (fn-lc-move-packet move) (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) (fn-lc-tail-unit header) segs)))
  (implies (and (natp i) (< i (fn-lbc-count fn-lbc)) (fn-lc-move-recordp move fn-lbc segs))
   (equal (fn-lc-read-home-frame (fn-lc-home-position (fn-lc-move-loc0 move) (fn-lc-move-loc1 move)) after) (fn-lc-read-suf (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs))))
 :hints (("Goal" :use
 ((:instance lccm-planned-move-geometry)
  (:instance lccm-planned-home-is-fresh)
  (:instance lccm-framed-home-copy (id (fn-lc-last-segment-id (fn-lc-ordered-segments segs))) (entry (list (len (fn-lc-at 2 (fn-lb-log-model-segment (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) segs))) (len (fn-lc-at 1 (fn-lb-log-model-segment (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) segs))) (- (len (fn-lc-move-frame (fn-lc-at 3 (fn-lc-tail-scan segs header)) i (fn-lc-read-range (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs) (fn-lc-read-suf (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs))) 32) (+ (len (fn-lc-at 1 (fn-lb-log-model-segment (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) segs))) 54) (len (fn-lc-read-range (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs)) (fn-record-payload (fn-lc-bound-row i fn-lbc segs)) (fn-lb-log-payload (fn-lc-bound-row i fn-lbc segs) segs) (fn-lb-log-model-homes (fn-lc-bound-row i fn-lbc segs)) i))
    (prev (fn-lc-at 3 (fn-lc-tail-scan segs header))) (wire (fn-lc-read-range (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs)) (home (fn-lc-read-suf (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs)) (unit (fn-lc-tail-unit header))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(lccm-plan-move-by-definition fn-lc-move-loc0 fn-lc-move-loc1 fn-lc-move-packet
 fn-lc-at-is-nth fn-lc-nth-1-alias fn-lc-nth-2-alias lccm-nth-cons lccm-len-cons
 lccm-nfix-nat natp (:type-prescription len) car-cons cdr-cons
 (:executable-counterpart equal) (:executable-counterpart len) (:executable-counterpart zp)
 (:executable-counterpart binary-+) associativity-of-+ commutativity-of-+ commutativity-2-of-+ fold-consts-in-+))))))

(local (defthm lccm-valid-move-is-plan
 (implies (fn-lc-move-recordp move fn-lbc segs)
  (and (natp (fn-lc-move-sequence move)) (< (fn-lc-move-sequence move) (fn-lbc-count fn-lbc))
   (equal move (fn-lc-plan-move (fn-lc-move-sequence move) (fn-lc-at 5 move)
       (fn-lc-at 6 move) (fn-lc-at 7 move) (fn-lc-at 8 move) segs fn-lbc))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lc-move-recordp))))))

(local (defthm lccm-valid-move-byte-copies
 (let* ((i (fn-lc-move-sequence move))
        (after (fn-lc-append-prepared (fn-lc-move-packet move)
         (fn-lc-last-segment-id (fn-lc-ordered-segments segs))
         (fn-lc-tail-unit (fn-lc-at 5 move)) segs)))
  (implies (fn-lc-move-recordp move fn-lbc segs)
    (and (equal (fn-lc-read-range (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) after)
                (fn-lc-read-range (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs))
         (equal (fn-lc-read-suf (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) after)
                (fn-lc-read-suf (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs)))))
 :hints (("Goal" :use
 ((:instance lccm-valid-move-is-plan)
  (:instance lccm-planned-wire-copy (i (fn-lc-move-sequence move)) (header (fn-lc-at 5 move))
    (k (fn-lc-at 6 move)) (r (fn-lc-at 7 move)) (mode (fn-lc-at 8 move)))
  (:instance lccm-planned-home-copy (i (fn-lc-move-sequence move)) (header (fn-lc-at 5 move))
    (k (fn-lc-at 6 move)) (r (fn-lc-at 7 move)) (mode (fn-lc-at 8 move))))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lc-read-suf))))))

(defthm fn-lc-clean-moves-only-the-locator
  (let* ((before (fn-lc-columns fn-lbc))
         (i (fn-lc-move-sequence move))
         (a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc))
         (out (fn-lc-clean move disk segs outcome fn-lbc)))
    (implies (equal (mv-nth 0 out) :ok)
             (and (equal (fn-lc-without-locators (fn-lc-columns (mv-nth 1 out)))
                         (fn-lc-without-locators before))
                  (equal (fn-lc-columns (mv-nth 1 out))
                         (fn-lc-columns (fn-lc-replay-move move fn-lbc)))
                  (equal (fn-lc-read-range (fn-lc-move-loc0 move)
                                          (fn-lc-move-loc1 move) (mv-nth 3 out))
                         (fn-lc-read-range a b segs))
                  (equal (fn-lc-read-home-frame
                           (fn-lc-home-position (fn-lc-move-loc0 move)
                                                (fn-lc-move-loc1 move)) (mv-nth 3 out))
                         (fn-lc-read-home-frame (fn-lc-home-position a b) segs))
                  (equal (fn-lc-read-suf (fn-lc-move-loc0 move)
                                        (fn-lc-move-loc1 move) (mv-nth 3 out))
                         (fn-lc-read-suf a b segs)))))
  :rule-classes nil :hints (("Goal" :use
 ((:instance lccm-clean-accepted-effects-by-definition)
  (:instance lccm-valid-move-is-plan)
  (:instance lccm-valid-move-byte-copies)
  (:instance lccm-bounded-replay-keeps-other-columns))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lc-read-suf)))))

(local (defun lccm-success-tooth (move disk segs outcome fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-p fn-lbc)))
 (mv-let (answer fn-lbc disk segs trace) (fn-lc-clean move disk segs outcome fn-lbc)
  (declare (ignore disk segs trace)) (mv (equal answer :ok) fn-lbc))))

(make-event (mv-let (err expansion state)
 (fn-dt-expand 'fn-lc-clean-moves-only-the-locator 'defteeth '( :claim (let* ((before (fn-lc-columns fn-lbc)) (i (fn-lc-move-sequence move)) (a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc)) (out (fn-lc-clean move disk segs outcome fn-lbc))) (((success (equal (mv-nth 0 out) :ok))) (and (equal (fn-lc-without-locators (fn-lc-columns (mv-nth 1 out))) (fn-lc-without-locators before)) (equal (fn-lc-columns (mv-nth 1 out)) (fn-lc-columns (fn-lc-replay-move move fn-lbc))) (equal (fn-lc-read-range (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) (mv-nth 3 out)) (fn-lc-read-range a b segs)) (equal (fn-lc-read-home-frame (fn-lc-home-position (fn-lc-move-loc0 move) (fn-lc-move-loc1 move)) (mv-nth 3 out)) (fn-lc-read-home-frame (fn-lc-home-position a b) segs)) (equal (fn-lc-read-suf (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) (mv-nth 3 out)) (fn-lc-read-suf a b segs)))))
 :subject fn-lc-clean
 :witness ((seed-kind :live) (move (lcrp-fixture-move))
  (disk (fn-lc-at 0 (lcm-test-input 1))) (segs (fn-lc-at 1 (lcm-test-input 1)))
  (outcome '(:ok :ok)))
 :stobjs ((fn-lbc (lcrp-build seed-kind fn-lbc)))
 :stobj-checks (((let* ((before (fn-lc-columns fn-lbc)) (i (fn-lc-move-sequence move)) (a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc)) (out (fn-lc-clean move disk segs outcome fn-lbc))) (declare (ignorable before i a b out)) (equal (mv-nth 0 out) :ok)) (lccm-success-tooth move disk segs outcome fn-lbc)  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(lccm-whole-clean-tooth lccm-clean-tooth lccm-whole-clean-conclusion
 lccm-success-tooth mv-nth nth car-cons cdr-cons (:executable-counterpart zp))))))
  ((let* ((before (fn-lc-columns fn-lbc)) (i (fn-lc-move-sequence move)) (a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc)) (out (fn-lc-clean move disk segs outcome fn-lbc))) (declare (ignorable before i a b out)) (and (equal (fn-lc-without-locators (fn-lc-columns (mv-nth 1 out))) (fn-lc-without-locators before)) (equal (fn-lc-columns (mv-nth 1 out)) (fn-lc-columns (fn-lc-replay-move move fn-lbc))) (equal (fn-lc-read-range (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) (mv-nth 3 out)) (fn-lc-read-range a b segs)) (equal (fn-lc-read-home-frame (fn-lc-home-position (fn-lc-move-loc0 move) (fn-lc-move-loc1 move)) (mv-nth 3 out)) (fn-lc-read-home-frame (fn-lc-home-position a b) segs)) (equal (fn-lc-read-suf (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) (mv-nth 3 out)) (fn-lc-read-suf a b segs)))) (lccm-whole-clean-tooth nil move disk segs outcome fn-lbc)  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(lccm-whole-clean-tooth lccm-clean-tooth lccm-whole-clean-conclusion
 lccm-success-tooth mv-nth nth car-cons cdr-cons (:executable-counterpart zp))))))
  ((let* ((before (fn-lc-columns fn-lbc)) (i (fn-lc-move-sequence move)) (a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc)) (out (fn-lc-clean move disk segs outcome fn-lbc))) (declare (ignorable before i a b out)) (and (equal (fn-lc-without-locators (fn-lc-columns (mv-nth 1 out))) (fn-lc-without-locators before)) (equal (fn-lc-columns (mv-nth 1 out)) (fn-lc-columns (fn-lc-replay-move move fn-lbc))) (equal (fn-lc-read-range (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) (mv-nth 3 out)) (fn-lc-read-range a b segs)) (equal (fn-lc-read-home-frame (fn-lc-home-position (fn-lc-move-loc0 move) (fn-lc-move-loc1 move)) (mv-nth 3 out)) (fn-lc-read-home-frame (fn-lc-home-position a b) segs)) (not (equal (fn-lc-read-suf (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) (mv-nth 3 out)) (fn-lc-read-suf a b segs))))) (lccm-whole-clean-tooth t move disk segs outcome fn-lbc)  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(lccm-whole-clean-tooth lccm-clean-tooth lccm-whole-clean-conclusion
 lccm-success-tooth mv-nth nth car-cons cdr-cons (:executable-counterpart zp)))))))
 :breaks ((success ((seed-kind :empty) (disk nil) (segs nil)
   (move '(:lc-move 0 2 nil (0 0 75 54 20 0 nil nil 0) nil nil nil nil)))
   :logical "no accepted MOVE exists at the empty creator; total locator setters change its columns"))
 :mutations ((corrupts-suf (:conclusion (and (equal (fn-lc-without-locators (fn-lc-columns (mv-nth 1 out))) (fn-lc-without-locators before)) (equal (fn-lc-columns (mv-nth 1 out)) (fn-lc-columns (fn-lc-replay-move move fn-lbc))) (equal (fn-lc-read-range (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) (mv-nth 3 out)) (fn-lc-read-range a b segs)) (equal (fn-lc-read-home-frame (fn-lc-home-position (fn-lc-move-loc0 move) (fn-lc-move-loc1 move)) (mv-nth 3 out)) (fn-lc-read-home-frame (fn-lc-home-position a b) segs)) (not (equal (fn-lc-read-suf (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) (mv-nth 3 out)) (fn-lc-read-suf a b segs))))) nil
   :fault "successful relocation changes the served home/SUF bytes"))
 :hints (("Goal" :use lccm-empty-state-removes-success
  :in-theory (union-theories (theory 'minimal-theory) '(lccm-whole-clean-conclusion lcrp-build (:executable-counterpart equal)))))) state)
 (if err (mv err expansion state)
  (value (cons 'progn (fn-lc-teeth-prepare-wrappers (cdr expansion)
   '(("Goal" :in-theory (union-theories (theory 'minimal-theory) '(lcrp-build))))))))))

(defteeth fn-lc-clean-moves-only-the-locator :claim (let* ((before (fn-lc-columns fn-lbc)) (i (fn-lc-move-sequence move)) (a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc)) (out (fn-lc-clean move disk segs outcome fn-lbc))) (((success (equal (mv-nth 0 out) :ok))) (and (equal (fn-lc-without-locators (fn-lc-columns (mv-nth 1 out))) (fn-lc-without-locators before)) (equal (fn-lc-columns (mv-nth 1 out)) (fn-lc-columns (fn-lc-replay-move move fn-lbc))) (equal (fn-lc-read-range (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) (mv-nth 3 out)) (fn-lc-read-range a b segs)) (equal (fn-lc-read-home-frame (fn-lc-home-position (fn-lc-move-loc0 move) (fn-lc-move-loc1 move)) (mv-nth 3 out)) (fn-lc-read-home-frame (fn-lc-home-position a b) segs)) (equal (fn-lc-read-suf (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) (mv-nth 3 out)) (fn-lc-read-suf a b segs)))))
 :subject fn-lc-clean
 :witness ((seed-kind :live) (move (lcrp-fixture-move))
  (disk (fn-lc-at 0 (lcm-test-input 1))) (segs (fn-lc-at 1 (lcm-test-input 1)))
  (outcome '(:ok :ok)))
 :stobjs ((fn-lbc (lcrp-build seed-kind fn-lbc)))
 :stobj-checks (((let* ((before (fn-lc-columns fn-lbc)) (i (fn-lc-move-sequence move)) (a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc)) (out (fn-lc-clean move disk segs outcome fn-lbc))) (declare (ignorable before i a b out)) (equal (mv-nth 0 out) :ok)) (lccm-success-tooth move disk segs outcome fn-lbc)  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(lccm-whole-clean-tooth lccm-clean-tooth lccm-whole-clean-conclusion
 lccm-success-tooth mv-nth nth car-cons cdr-cons (:executable-counterpart zp))))))
  ((let* ((before (fn-lc-columns fn-lbc)) (i (fn-lc-move-sequence move)) (a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc)) (out (fn-lc-clean move disk segs outcome fn-lbc))) (declare (ignorable before i a b out)) (and (equal (fn-lc-without-locators (fn-lc-columns (mv-nth 1 out))) (fn-lc-without-locators before)) (equal (fn-lc-columns (mv-nth 1 out)) (fn-lc-columns (fn-lc-replay-move move fn-lbc))) (equal (fn-lc-read-range (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) (mv-nth 3 out)) (fn-lc-read-range a b segs)) (equal (fn-lc-read-home-frame (fn-lc-home-position (fn-lc-move-loc0 move) (fn-lc-move-loc1 move)) (mv-nth 3 out)) (fn-lc-read-home-frame (fn-lc-home-position a b) segs)) (equal (fn-lc-read-suf (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) (mv-nth 3 out)) (fn-lc-read-suf a b segs)))) (lccm-whole-clean-tooth nil move disk segs outcome fn-lbc)  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(lccm-whole-clean-tooth lccm-clean-tooth lccm-whole-clean-conclusion
 lccm-success-tooth mv-nth nth car-cons cdr-cons (:executable-counterpart zp))))))
  ((let* ((before (fn-lc-columns fn-lbc)) (i (fn-lc-move-sequence move)) (a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc)) (out (fn-lc-clean move disk segs outcome fn-lbc))) (declare (ignorable before i a b out)) (and (equal (fn-lc-without-locators (fn-lc-columns (mv-nth 1 out))) (fn-lc-without-locators before)) (equal (fn-lc-columns (mv-nth 1 out)) (fn-lc-columns (fn-lc-replay-move move fn-lbc))) (equal (fn-lc-read-range (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) (mv-nth 3 out)) (fn-lc-read-range a b segs)) (equal (fn-lc-read-home-frame (fn-lc-home-position (fn-lc-move-loc0 move) (fn-lc-move-loc1 move)) (mv-nth 3 out)) (fn-lc-read-home-frame (fn-lc-home-position a b) segs)) (not (equal (fn-lc-read-suf (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) (mv-nth 3 out)) (fn-lc-read-suf a b segs))))) (lccm-whole-clean-tooth t move disk segs outcome fn-lbc)  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(lccm-whole-clean-tooth lccm-clean-tooth lccm-whole-clean-conclusion
 lccm-success-tooth mv-nth nth car-cons cdr-cons (:executable-counterpart zp)))))))
 :breaks ((success ((seed-kind :empty) (disk nil) (segs nil)
   (move '(:lc-move 0 2 nil (0 0 75 54 20 0 nil nil 0) nil nil nil nil)))
   :logical "no accepted MOVE exists at the empty creator; total locator setters change its columns"))
 :mutations ((corrupts-suf (:conclusion (and (equal (fn-lc-without-locators (fn-lc-columns (mv-nth 1 out))) (fn-lc-without-locators before)) (equal (fn-lc-columns (mv-nth 1 out)) (fn-lc-columns (fn-lc-replay-move move fn-lbc))) (equal (fn-lc-read-range (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) (mv-nth 3 out)) (fn-lc-read-range a b segs)) (equal (fn-lc-read-home-frame (fn-lc-home-position (fn-lc-move-loc0 move) (fn-lc-move-loc1 move)) (mv-nth 3 out)) (fn-lc-read-home-frame (fn-lc-home-position a b) segs)) (not (equal (fn-lc-read-suf (fn-lc-move-loc0 move) (fn-lc-move-loc1 move) (mv-nth 3 out)) (fn-lc-read-suf a b segs))))) nil
   :fault "successful relocation changes the served home/SUF bytes"))
 :hints (("Goal" :use lccm-empty-state-removes-success
  :in-theory (union-theories (theory 'minimal-theory) '(lccm-whole-clean-conclusion lcrp-build (:executable-counterpart equal))))))

(defteeth-check (fn-lc-clean-moves-only-the-locator))

; Complete-cleaning proof: capture, successful MOVE effects and the actual work fold.
(local (defthm lccp-word-of-loc0
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc))
               (not (equal field :loc0)) (not (equal field :loc1)))
  (equal (fn-lbc-word field n (update-fn-lbc-loc0 i v fn-lbc))
         (fn-lbc-word field n fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-word fn-lbc-row-store update-fn-lbc-loc0 update-fn-lbc-loc1 update-fn-lbc-row-store
 fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-loc0-is-update-nth fn-lbc-rowwords-set-loc1-is-update-nth
 fn-dm-nth-update-nth fn-dm-nth-of-zeros fn-dm-len-update-nth
 nth len natp nfix zp car-cons cdr-cons
 (:type-prescription len) (:executable-counterpart nfix) (:executable-counterpart zp)
 (:executable-counterpart equal) (:executable-counterpart binary-+)
fn-lbc-rowwords-get-handle-is-nth fn-lbc-rowwords-get-loc0-is-nth fn-lbc-rowwords-get-loc1-is-nth fn-lbc-rowwords-get-head-length-is-nth fn-lbc-rowwords-get-stamp-is-nth fn-lbc-rowwords-get-prefix-max-is-nth fn-lbc-rowwords-get-txid-is-nth fn-lbc-rowwords-get-generation-is-nth fn-lbc-rowwords-get-charge-is-nth fn-lbc-rowwords-get-msgid-hash-is-nth fn-lbc-rowwords-get-msgid-offset-is-nth fn-lbc-rowwords-get-msgid-length-is-nth fn-lbc-rowwords-get-withdrawal-at-is-nth fn-lbc-rowwords-get-withdrawal-by-is-nth fn-lbc-rowwords-get-overview-offset-is-nth fn-lbc-rowwords-get-flags-is-nth fn-lbc-count))))))

(local (defthm lccp-word-of-loc1
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc))
               (not (equal field :loc0)) (not (equal field :loc1)))
  (equal (fn-lbc-word field n (update-fn-lbc-loc1 i v fn-lbc))
         (fn-lbc-word field n fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-word fn-lbc-row-store update-fn-lbc-loc0 update-fn-lbc-loc1 update-fn-lbc-row-store
 fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-loc0-is-update-nth fn-lbc-rowwords-set-loc1-is-update-nth
 fn-dm-nth-update-nth fn-dm-nth-of-zeros fn-dm-len-update-nth
 nth len natp nfix zp car-cons cdr-cons
 (:type-prescription len) (:executable-counterpart nfix) (:executable-counterpart zp)
 (:executable-counterpart equal) (:executable-counterpart binary-+)
fn-lbc-rowwords-get-handle-is-nth fn-lbc-rowwords-get-loc0-is-nth fn-lbc-rowwords-get-loc1-is-nth fn-lbc-rowwords-get-head-length-is-nth fn-lbc-rowwords-get-stamp-is-nth fn-lbc-rowwords-get-prefix-max-is-nth fn-lbc-rowwords-get-txid-is-nth fn-lbc-rowwords-get-generation-is-nth fn-lbc-rowwords-get-charge-is-nth fn-lbc-rowwords-get-msgid-hash-is-nth fn-lbc-rowwords-get-msgid-offset-is-nth fn-lbc-rowwords-get-msgid-length-is-nth fn-lbc-rowwords-get-withdrawal-at-is-nth fn-lbc-rowwords-get-withdrawal-by-is-nth fn-lbc-rowwords-get-overview-offset-is-nth fn-lbc-rowwords-get-flags-is-nth fn-lbc-count))))))

(local (defthm lccp-directory-field-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-directory-field field i (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-directory-field field i fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-directory-field fn-lbc-directory-store lccp-word-of-loc0 lccp-word-of-loc1
 update-fn-lbc-loc0 update-fn-lbc-loc1 update-fn-lbc-row-store
 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) ))))))

(local (defthm lccp-directory-field-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-directory-field field i (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-directory-field field i fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-directory-field fn-lbc-directory-store lccp-word-of-loc0 lccp-word-of-loc1
 update-fn-lbc-loc0 update-fn-lbc-loc1 update-fn-lbc-row-store
 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) ))))))

(local (defthm lccp-membership-field-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-membership-field field i (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-membership-field field i fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-membership-field fn-lbc-membership-store lccp-word-of-loc0 lccp-word-of-loc1
 update-fn-lbc-loc0 update-fn-lbc-loc1 update-fn-lbc-row-store
 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1))))))

(local (defthm lccp-membership-field-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-membership-field field i (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-membership-field field i fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-membership-field fn-lbc-membership-store lccp-word-of-loc0 lccp-word-of-loc1
 update-fn-lbc-loc0 update-fn-lbc-loc1 update-fn-lbc-row-store
 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1))))))

(local (defthm lccp-nov-field-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-nov-field field i (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-nov-field field i fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-nov-field fn-lbc-nov-store lccp-word-of-loc0 lccp-word-of-loc1
 update-fn-lbc-loc0 update-fn-lbc-loc1 update-fn-lbc-row-store
 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1))))))

(local (defthm lccp-nov-field-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-nov-field field i (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-nov-field field i fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-nov-field fn-lbc-nov-store lccp-word-of-loc0 lccp-word-of-loc1
 update-fn-lbc-loc0 update-fn-lbc-loc1 update-fn-lbc-row-store
 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1))))))

(local (defthm lccp-msgid-pool-count-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-msgid-pool-count (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-msgid-pool-count fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid-pool-count fn-lbc-msgid-store lccp-word-of-loc0 lccp-word-of-loc1
 update-fn-lbc-loc0 update-fn-lbc-loc1 update-fn-lbc-row-store
 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1))))))

(local (defthm lccp-msgid-pool-count-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-msgid-pool-count (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-msgid-pool-count fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid-pool-count fn-lbc-msgid-store lccp-word-of-loc0 lccp-word-of-loc1
 update-fn-lbc-loc0 update-fn-lbc-loc1 update-fn-lbc-row-store
 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1))))))

(local (defthm lccp-msgid-pool-octet-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-msgid-pool-octet i (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-msgid-pool-octet i fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid-pool-octet fn-lbc-msgid-store lccp-word-of-loc0 lccp-word-of-loc1
 update-fn-lbc-loc0 update-fn-lbc-loc1 update-fn-lbc-row-store
 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1))))))

(local (defthm lccp-msgid-pool-octet-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-msgid-pool-octet i (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-msgid-pool-octet i fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid-pool-octet fn-lbc-msgid-store lccp-word-of-loc0 lccp-word-of-loc1
 update-fn-lbc-loc0 update-fn-lbc-loc1 update-fn-lbc-row-store
 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1))))))

(local (defthm lccp-overview-pool-count-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-overview-pool-count (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-overview-pool-count fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-overview-pool-count fn-lbc-overview-store lccp-word-of-loc0 lccp-word-of-loc1
 update-fn-lbc-loc0 update-fn-lbc-loc1 update-fn-lbc-row-store
 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1))))))

(local (defthm lccp-overview-pool-count-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-overview-pool-count (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-overview-pool-count fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-overview-pool-count fn-lbc-overview-store lccp-word-of-loc0 lccp-word-of-loc1
 update-fn-lbc-loc0 update-fn-lbc-loc1 update-fn-lbc-row-store
 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1))))))

(local (defthm lccp-overview-pool-octet-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-overview-pool-octet i (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-overview-pool-octet i fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-overview-pool-octet fn-lbc-overview-store lccp-word-of-loc0 lccp-word-of-loc1
 update-fn-lbc-loc0 update-fn-lbc-loc1 update-fn-lbc-row-store
 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1))))))

(local (defthm lccp-overview-pool-octet-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-overview-pool-octet i (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-overview-pool-octet i fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-overview-pool-octet fn-lbc-overview-store lccp-word-of-loc0 lccp-word-of-loc1
 update-fn-lbc-loc0 update-fn-lbc-loc1 update-fn-lbc-row-store
 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1))))))

(local (defthm lccp-msgid-pool-range-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-msgid-pool-range off n (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-msgid-pool-range off n fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-msgid-pool-range off n fn-lbc) :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid-pool-range  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 (:induction fn-lbc-msgid-pool-range)))))))

(local (defthm lccp-msgid-pool-range-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-msgid-pool-range off n (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-msgid-pool-range off n fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-msgid-pool-range off n fn-lbc) :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid-pool-range  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 (:induction fn-lbc-msgid-pool-range)))))))

(local (defthm lccp-overview-pool-range-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-overview-pool-range off n (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-overview-pool-range off n fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-overview-pool-range off n fn-lbc) :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-overview-pool-range  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 (:induction fn-lbc-overview-pool-range)))))))

(local (defthm lccp-overview-pool-range-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-overview-pool-range off n (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-overview-pool-range off n fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-overview-pool-range off n fn-lbc) :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-overview-pool-range  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 (:induction fn-lbc-overview-pool-range)))))))

(local (defthm lccp-escape-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-escape i field (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-escape i field fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-escape fn-lbc-escape-store-get lccp-word-of-loc0 lccp-word-of-loc1
 update-fn-lbc-loc0 update-fn-lbc-loc1 update-fn-lbc-row-store
 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1))))))

(local (defthm lccp-escape-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-escape i field (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-escape i field fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-escape fn-lbc-escape-store-get lccp-word-of-loc0 lccp-word-of-loc1
 update-fn-lbc-loc0 update-fn-lbc-loc1 update-fn-lbc-row-store
 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1))))))

(local (defthm lccp-value-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc)) (not (equal field :loc0)) (not (equal field :loc1))) (equal (fn-lbc-value i field (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-value i field fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-value  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1))))))

(local (defthm lccp-value-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc)) (not (equal field :loc0)) (not (equal field :loc1))) (equal (fn-lbc-value i field (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-value i field fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-value  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1))))))

(local (defthm lccp-directory-value-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-directory-value i field (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-directory-value i field fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-directory-value  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1))))))

(local (defthm lccp-directory-value-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-directory-value i field (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-directory-value i field fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-directory-value  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1))))))

(local (defthm lccp-msgid-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-msgid i (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-msgid i fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1 lccp-directory-value-of-loc0 lccp-directory-value-of-loc1))))))

(local (defthm lccp-msgid-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-msgid i (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-msgid i fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-msgid  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1 lccp-directory-value-of-loc0 lccp-directory-value-of-loc1))))))

(local (defthm lccp-flag-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-flag i bit (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-flag i bit fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-flag  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1 lccp-directory-value-of-loc0 lccp-directory-value-of-loc1 lccp-msgid-of-loc0 lccp-msgid-of-loc1))))))

(local (defthm lccp-flag-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-flag i bit (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-flag i bit fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-flag  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1 lccp-directory-value-of-loc0 lccp-directory-value-of-loc1 lccp-msgid-of-loc0 lccp-msgid-of-loc1))))))

(local (defthm lccp-withdrawn-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-withdrawn i (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-withdrawn i fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-withdrawn  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1 lccp-directory-value-of-loc0 lccp-directory-value-of-loc1 lccp-msgid-of-loc0 lccp-msgid-of-loc1 lccp-flag-of-loc0 lccp-flag-of-loc1))))))

(local (defthm lccp-withdrawn-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-withdrawn i (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-withdrawn i fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-withdrawn  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1 lccp-directory-value-of-loc0 lccp-directory-value-of-loc1 lccp-msgid-of-loc0 lccp-msgid-of-loc1 lccp-flag-of-loc0 lccp-flag-of-loc1))))))

(local (defthm lccp-membership-group-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-membership-group j (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-membership-group j fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-membership-group  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1 lccp-directory-value-of-loc0 lccp-directory-value-of-loc1 lccp-msgid-of-loc0 lccp-msgid-of-loc1 lccp-flag-of-loc0 lccp-flag-of-loc1 lccp-withdrawn-of-loc0 lccp-withdrawn-of-loc1))))))

(local (defthm lccp-membership-group-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-membership-group j (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-membership-group j fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-membership-group  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1 lccp-directory-value-of-loc0 lccp-directory-value-of-loc1 lccp-msgid-of-loc0 lccp-msgid-of-loc1 lccp-flag-of-loc0 lccp-flag-of-loc1 lccp-withdrawn-of-loc0 lccp-withdrawn-of-loc1))))))

(local (defthm lccp-membership-run-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-membership-run start count numbersp (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-membership-run start count numbersp fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-membership-run start count numbersp fn-lbc) :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-membership-run  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1 lccp-directory-value-of-loc0 lccp-directory-value-of-loc1 lccp-msgid-of-loc0 lccp-msgid-of-loc1 lccp-flag-of-loc0 lccp-flag-of-loc1 lccp-withdrawn-of-loc0 lccp-withdrawn-of-loc1 lccp-membership-group-of-loc0 lccp-membership-group-of-loc1 (:induction fn-lbc-membership-run)))))))

(local (defthm lccp-membership-run-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-membership-run start count numbersp (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-membership-run start count numbersp fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-membership-run start count numbersp fn-lbc) :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-membership-run  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1 lccp-directory-value-of-loc0 lccp-directory-value-of-loc1 lccp-msgid-of-loc0 lccp-msgid-of-loc1 lccp-flag-of-loc0 lccp-flag-of-loc1 lccp-withdrawn-of-loc0 lccp-withdrawn-of-loc1 lccp-membership-group-of-loc0 lccp-membership-group-of-loc1 (:induction fn-lbc-membership-run)))))))

(local (defthm lccp-groups-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-groups i (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-groups i fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-groups  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1 lccp-directory-value-of-loc0 lccp-directory-value-of-loc1 lccp-msgid-of-loc0 lccp-msgid-of-loc1 lccp-flag-of-loc0 lccp-flag-of-loc1 lccp-withdrawn-of-loc0 lccp-withdrawn-of-loc1 lccp-membership-group-of-loc0 lccp-membership-group-of-loc1 lccp-membership-run-of-loc0 lccp-membership-run-of-loc1))))))

(local (defthm lccp-groups-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-groups i (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-groups i fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-groups  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1 lccp-directory-value-of-loc0 lccp-directory-value-of-loc1 lccp-msgid-of-loc0 lccp-msgid-of-loc1 lccp-flag-of-loc0 lccp-flag-of-loc1 lccp-withdrawn-of-loc0 lccp-withdrawn-of-loc1 lccp-membership-group-of-loc0 lccp-membership-group-of-loc1 lccp-membership-run-of-loc0 lccp-membership-run-of-loc1))))))

(local (defthm lccp-numbers-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-numbers i (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-numbers i fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-numbers  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1 lccp-directory-value-of-loc0 lccp-directory-value-of-loc1 lccp-msgid-of-loc0 lccp-msgid-of-loc1 lccp-flag-of-loc0 lccp-flag-of-loc1 lccp-withdrawn-of-loc0 lccp-withdrawn-of-loc1 lccp-membership-group-of-loc0 lccp-membership-group-of-loc1 lccp-membership-run-of-loc0 lccp-membership-run-of-loc1 lccp-groups-of-loc0 lccp-groups-of-loc1))))))

(local (defthm lccp-numbers-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-numbers i (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-numbers i fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-numbers  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1 lccp-directory-value-of-loc0 lccp-directory-value-of-loc1 lccp-msgid-of-loc0 lccp-msgid-of-loc1 lccp-flag-of-loc0 lccp-flag-of-loc1 lccp-withdrawn-of-loc0 lccp-withdrawn-of-loc1 lccp-membership-group-of-loc0 lccp-membership-group-of-loc1 lccp-membership-run-of-loc0 lccp-membership-run-of-loc1 lccp-groups-of-loc0 lccp-groups-of-loc1))))))

(local (defthm lccp-nov-text-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-nov-text start length (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-nov-text start length fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-nov-text  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1 lccp-directory-value-of-loc0 lccp-directory-value-of-loc1 lccp-msgid-of-loc0 lccp-msgid-of-loc1 lccp-flag-of-loc0 lccp-flag-of-loc1 lccp-withdrawn-of-loc0 lccp-withdrawn-of-loc1 lccp-membership-group-of-loc0 lccp-membership-group-of-loc1 lccp-membership-run-of-loc0 lccp-membership-run-of-loc1 lccp-groups-of-loc0 lccp-groups-of-loc1 lccp-numbers-of-loc0 lccp-numbers-of-loc1))))))

(local (defthm lccp-nov-text-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-nov-text start length (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-nov-text start length fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-nov-text  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1 lccp-directory-value-of-loc0 lccp-directory-value-of-loc1 lccp-msgid-of-loc0 lccp-msgid-of-loc1 lccp-flag-of-loc0 lccp-flag-of-loc1 lccp-withdrawn-of-loc0 lccp-withdrawn-of-loc1 lccp-membership-group-of-loc0 lccp-membership-group-of-loc1 lccp-membership-run-of-loc0 lccp-membership-run-of-loc1 lccp-groups-of-loc0 lccp-groups-of-loc1 lccp-numbers-of-loc0 lccp-numbers-of-loc1))))))

(local (defthm lccp-nov-at-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-nov-at j (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-nov-at j fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-nov-at  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1 lccp-directory-value-of-loc0 lccp-directory-value-of-loc1 lccp-msgid-of-loc0 lccp-msgid-of-loc1 lccp-flag-of-loc0 lccp-flag-of-loc1 lccp-withdrawn-of-loc0 lccp-withdrawn-of-loc1 lccp-membership-group-of-loc0 lccp-membership-group-of-loc1 lccp-membership-run-of-loc0 lccp-membership-run-of-loc1 lccp-groups-of-loc0 lccp-groups-of-loc1 lccp-numbers-of-loc0 lccp-numbers-of-loc1 lccp-nov-text-of-loc0 lccp-nov-text-of-loc1))))))

(local (defthm lccp-nov-at-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-nov-at j (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-nov-at j fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-nov-at  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1 lccp-directory-value-of-loc0 lccp-directory-value-of-loc1 lccp-msgid-of-loc0 lccp-msgid-of-loc1 lccp-flag-of-loc0 lccp-flag-of-loc1 lccp-withdrawn-of-loc0 lccp-withdrawn-of-loc1 lccp-membership-group-of-loc0 lccp-membership-group-of-loc1 lccp-membership-run-of-loc0 lccp-membership-run-of-loc1 lccp-groups-of-loc0 lccp-groups-of-loc1 lccp-numbers-of-loc0 lccp-numbers-of-loc1 lccp-nov-text-of-loc0 lccp-nov-text-of-loc1))))))

(local (defthm lccp-original-nov-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-original-nov i (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-original-nov i fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-original-nov  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1 lccp-directory-value-of-loc0 lccp-directory-value-of-loc1 lccp-msgid-of-loc0 lccp-msgid-of-loc1 lccp-flag-of-loc0 lccp-flag-of-loc1 lccp-withdrawn-of-loc0 lccp-withdrawn-of-loc1 lccp-membership-group-of-loc0 lccp-membership-group-of-loc1 lccp-membership-run-of-loc0 lccp-membership-run-of-loc1 lccp-groups-of-loc0 lccp-groups-of-loc1 lccp-numbers-of-loc0 lccp-numbers-of-loc1 lccp-nov-text-of-loc0 lccp-nov-text-of-loc1 lccp-nov-at-of-loc0 lccp-nov-at-of-loc1))))))

(local (defthm lccp-original-nov-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-original-nov i (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-original-nov i fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-original-nov  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1 lccp-directory-value-of-loc0 lccp-directory-value-of-loc1 lccp-msgid-of-loc0 lccp-msgid-of-loc1 lccp-flag-of-loc0 lccp-flag-of-loc1 lccp-withdrawn-of-loc0 lccp-withdrawn-of-loc1 lccp-membership-group-of-loc0 lccp-membership-group-of-loc1 lccp-membership-run-of-loc0 lccp-membership-run-of-loc1 lccp-groups-of-loc0 lccp-groups-of-loc1 lccp-numbers-of-loc0 lccp-numbers-of-loc1 lccp-nov-text-of-loc0 lccp-nov-text-of-loc1 lccp-nov-at-of-loc0 lccp-nov-at-of-loc1))))))

(local (defthm lccp-served-row-of-loc0
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-served-row i (update-fn-lbc-loc0 m v fn-lbc)) (fn-lbc-served-row i fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-served-row  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1 lccp-directory-value-of-loc0 lccp-directory-value-of-loc1 lccp-msgid-of-loc0 lccp-msgid-of-loc1 lccp-flag-of-loc0 lccp-flag-of-loc1 lccp-withdrawn-of-loc0 lccp-withdrawn-of-loc1 lccp-membership-group-of-loc0 lccp-membership-group-of-loc1 lccp-membership-run-of-loc0 lccp-membership-run-of-loc1 lccp-groups-of-loc0 lccp-groups-of-loc1 lccp-numbers-of-loc0 lccp-numbers-of-loc1 lccp-nov-text-of-loc0 lccp-nov-text-of-loc1 lccp-nov-at-of-loc0 lccp-nov-at-of-loc1 lccp-original-nov-of-loc0 lccp-original-nov-of-loc1))))))

(local (defthm lccp-served-row-of-loc1
 (implies (and (natp m) (< m (fn-lbc-count fn-lbc))) (equal (fn-lbc-served-row i (update-fn-lbc-loc1 m v fn-lbc)) (fn-lbc-served-row i fn-lbc)))
 :hints (("Goal"  :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-served-row  lccp-word-of-loc0 lccp-word-of-loc1

 fn-dm-nth-update-nth fn-dm-nth-of-zeros nth nfix natp car-cons cdr-cons
 (:executable-counterpart nfix) (:executable-counterpart equal) (:executable-counterpart zp) lccp-directory-field-of-loc0 lccp-directory-field-of-loc1 lccp-membership-field-of-loc0 lccp-membership-field-of-loc1 lccp-nov-field-of-loc0 lccp-nov-field-of-loc1 lccp-msgid-pool-count-of-loc0 lccp-msgid-pool-count-of-loc1 lccp-msgid-pool-octet-of-loc0 lccp-msgid-pool-octet-of-loc1 lccp-overview-pool-count-of-loc0 lccp-overview-pool-count-of-loc1 lccp-overview-pool-octet-of-loc0 lccp-overview-pool-octet-of-loc1 lccp-msgid-pool-range-of-loc0 lccp-msgid-pool-range-of-loc1 lccp-overview-pool-range-of-loc0 lccp-overview-pool-range-of-loc1 lccp-escape-of-loc0 lccp-escape-of-loc1 lccp-value-of-loc0 lccp-value-of-loc1 lccp-directory-value-of-loc0 lccp-directory-value-of-loc1 lccp-msgid-of-loc0 lccp-msgid-of-loc1 lccp-flag-of-loc0 lccp-flag-of-loc1 lccp-withdrawn-of-loc0 lccp-withdrawn-of-loc1 lccp-membership-group-of-loc0 lccp-membership-group-of-loc1 lccp-membership-run-of-loc0 lccp-membership-run-of-loc1 lccp-groups-of-loc0 lccp-groups-of-loc1 lccp-numbers-of-loc0 lccp-numbers-of-loc1 lccp-nov-text-of-loc0 lccp-nov-text-of-loc1 lccp-nov-at-of-loc0 lccp-nov-at-of-loc1 lccp-original-nov-of-loc0 lccp-original-nov-of-loc1))))))

(local (defthm lccp-fix-cons
 (equal (true-list-fix (cons a b)) (cons a (true-list-fix b)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(true-list-fix car-cons cdr-cons))))))

(local (defthm lccp-fix-atom
 (implies (not (consp x)) (equal (true-list-fix x) nil))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(true-list-fix))))))

(local (defthm lccp-fix-idempotent
 (equal (true-list-fix (true-list-fix x)) (true-list-fix x))
 :hints (("Goal" :induct (len x) :in-theory (union-theories (theory 'minimal-theory)
 '(true-list-fix len (:induction len) car-cons cdr-cons))))))

(local (defthm lccp-len-fix
 (equal (len (true-list-fix x)) (len x))
 :hints (("Goal" :induct (len x) :in-theory (union-theories (theory 'minimal-theory)
 '(true-list-fix len (:induction len) car-cons cdr-cons))))))

(local (defthm lccp-fix-append
 (equal (true-list-fix (append a b)) (append (true-list-fix a) (true-list-fix b)))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'minimal-theory)
 '(true-list-fix len binary-append (:induction len) car-cons cdr-cons))))))

(local (defthm lccp-control-home-roundtrip
 (let* ((control (true-list-fix x))
        (home (list (len control) (take (min 3 (len control)) control) (nthcdr 4 control)))
        (after (fn-lbc-restore-control home nov)))
  (equal (list (len (true-list-fix after))
               (take (min 3 (len (true-list-fix after))) (true-list-fix after))
               (nthcdr 4 (true-list-fix after))) home))
 :hints (("Goal" :cases ((consp x) (consp (cdr x)) (consp (cddr x)) (consp (cdddr x)))
  :expand ((true-list-fix x) (true-list-fix (cdr x)) (true-list-fix (cddr x)) (true-list-fix (cdddr x)) (len x) (len (cdr x)) (len (cddr x)) (len (cdddr x)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-restore-control lccp-fix-cons lccp-fix-atom lccp-fix-idempotent lccp-fix-append lccp-len-fix take nthcdr nth min nfix natp
     lccm-len-take lccm-len-append lccm-len-cons lccm-nth-cons car-cons cdr-cons
     (:type-prescription len) (:executable-counterpart zp)
     (:executable-counterpart equal) (:executable-counterpart <)
     (:executable-counterpart len) (:executable-counterpart binary-+)
     binary-append associativity-of-+ fold-consts-in-+))))))

(local (defthm lccp-row-entry-in-append
 (implies (not (equal seq nil))
 (equal (fn-lb-log-model-row-entry-in seq handle (append a b))
        (or (fn-lb-log-model-row-entry-in seq handle a)
            (fn-lb-log-model-row-entry-in seq handle b))))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-log-model-row-entry-in binary-append len (:induction len) car-cons cdr-cons (:executable-counterpart nth)))))))

(local (defthm lccp-row-entry-in-singleton
 (equal (fn-lb-log-model-row-entry-in seq handle (list entry))
   (if (and (equal seq (nth 8 entry)) (equal handle (nth 5 entry))) entry nil))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-log-model-row-entry-in car-cons cdr-cons (:executable-counterpart nth))))) ))

(local (defthm lccp-row-entry-in-NIL
 (equal (fn-lb-log-model-row-entry-in seq handle nil) nil)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lb-log-model-row-entry-in))))))

(local (defthm lccp-global-entry-after-prepared
 (let* ((new (fn-lb-log-model-row-entry row (fn-lc-append-prepared record id unit segs)))
        (old (fn-lb-log-model-row-entry row segs)) (entry (nth 2 record)))
  (implies (not (equal (fn-record-sequence row) nil))
 (or (equal new old)
      (and (equal new entry) (equal (fn-record-sequence row) (nth 8 entry))
           (equal (fn-record-payload row) (nth 5 entry))))))
 :hints (("Goal" :induct (fn-lc-append-prepared record id unit segs)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-append-prepared fn-lb-log-model-row-entry lccp-row-entry-in-append
   lccp-row-entry-in-singleton lccp-row-entry-in-NIL lccm-nth-cons car-cons cdr-cons (:executable-counterpart nth)
   (:induction fn-lc-append-prepared) (:executable-counterpart zp)
   (:executable-counterpart equal)))))))

(local (defthm lccp-valid-move-entry-fields
 (let* ((i (fn-lc-move-sequence move)) (row (fn-lc-bound-row i fn-lbc segs)) (entry (fn-lc-at 4 move)))
  (implies (fn-lc-move-recordp move fn-lbc segs)
   (and (equal (nth 8 entry) (fn-record-sequence row))
        (equal (nth 5 entry) (fn-record-payload row))
        (equal (nth 6 entry) (fn-lb-log-payload row segs))
        (equal (nth 7 entry) (fn-lb-log-model-homes row)))))
 :hints (("Goal" :use lccm-valid-move-is-plan
 :in-theory (union-theories (theory 'minimal-theory)
 '(lccm-plan-move-by-definition fn-lc-move-recordp fn-lc-move-sequence fn-lc-at-is-nth
 lccm-nth-cons car-cons cdr-cons natp (:executable-counterpart zp) (:executable-counterpart equal)))))))

(local (defthm lccp-payload-key-congruence
 (implies (and (equal (fn-record-sequence a) (fn-record-sequence b))
               (equal (fn-record-payload a) (fn-record-payload b)))
  (equal (fn-lb-log-payload a segs) (fn-lb-log-payload b segs)))
 :hints (("Goal" :induct (len segs) :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-log-payload fn-lb-log-model-row-entry len (:induction len) car-cons cdr-cons))))))

(local (defthm lccp-move-append-preserves-global-payload
 (implies (and (fn-lc-move-recordp move fn-lbc segs) (fn-record-sequence query))
  (equal (fn-lb-log-payload query (fn-lc-append-prepared (fn-lc-move-packet move) id unit segs))
         (fn-lb-log-payload query segs)))
 :hints (("Goal" :use
 ((:instance lccp-global-entry-after-prepared (row query) (record (fn-lc-move-packet move)))
  (:instance lccp-valid-move-entry-fields)
  (:instance lccp-payload-key-congruence (a query) (b (fn-lc-bound-row (fn-lc-move-sequence move) fn-lbc segs))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-move-packet lccm-nth-cons fn-lb-log-payload car-cons cdr-cons
 (:executable-counterpart zp)))))))

(local (defthm lccp-listp-fix
 (true-listp (true-list-fix x))
 :hints (("Goal" :induct (len x) :in-theory (union-theories (theory 'minimal-theory)
 '(true-list-fix true-listp len (:induction len) car-cons cdr-cons))))))

(local (defthm lccp-listp-append
 (equal (true-listp (append a b)) (true-listp b))
 :hints (("Goal" :induct (len a) :in-theory (union-theories (theory 'minimal-theory)
 '(true-listp binary-append len (:induction len) car-cons cdr-cons))))))

(local (defthm lccp-listp-nthcdr
 (implies (true-listp xs) (true-listp (nthcdr n xs)))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (union-theories (theory 'minimal-theory)
 '(true-listp nthcdr (:induction nthcdr) car-cons cdr-cons))))))

(local (defthm lccp-canonical-restore-is-list
 (true-listp (fn-lbc-restore-control
   (list (len (true-list-fix x)) (take (min 3 (len (true-list-fix x))) (true-list-fix x))
         (nthcdr 4 (true-list-fix x))) nov))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-restore-control lccp-listp-fix lccp-listp-append lccp-listp-nthcdr
 lccm-true-listp-take lccm-nth-cons lccm-listp-cons car-cons cdr-cons
 (:executable-counterpart zp)))))))

(local (defthm lccp-rehomed-row-observations
 (let* ((facts (nth 6 r)) (identity (nth 7 r))
        (row (fn-held-make (nth 8 r) (car identity) (cadr identity) (nth 0 r) (nth 1 r) (nth 2 r) (nth 0 old-homes) (nth 1 old-homes) (nth 2 old-homes) (caddr identity) (nth 4 r) (fn-hf-make (nth 0 facts) (nth 1 facts) (nth 2 facts) (fn-lbc-restore-control (nth 4 old-homes) (nth 3 facts))) (nth 3 old-homes) (nth 3 r) (nth 5 r)))
        (homes (fn-lb-log-model-homes row)) (after (fn-held-make (nth 8 r) (car identity) (cadr identity) (nth 0 r) (nth 1 r) (nth 2 r) (nth 0 homes) (nth 1 homes) (nth 2 homes) (caddr identity) (nth 4 r) (fn-hf-make (nth 0 facts) (nth 1 facts) (nth 2 facts) (fn-lbc-restore-control (nth 4 homes) (nth 3 facts))) (nth 3 homes) (nth 3 r) (nth 5 r))))
  (implies (fn-held-p row)
   (and (fn-held-p after)
        (equal (fn-record-sequence after) (fn-record-sequence row))
        (equal (fn-record-payload after) (fn-record-payload row))
        (equal (fn-lb-log-model-homes after) (fn-lb-log-model-homes row))
        (equal (fn-lc-expected-home-frame after) (fn-lc-expected-home-frame row)))))
 :hints (("Goal" :use
 ((:instance lccp-control-home-roundtrip (x (fn-hf-control (fn-held-facts (fn-held-make (nth 8 r) (car (nth 7 r)) (cadr (nth 7 r)) (nth 0 r) (nth 1 r) (nth 2 r) (nth 0 old-homes) (nth 1 old-homes) (nth 2 old-homes) (caddr (nth 7 r)) (nth 4 r) (fn-hf-make (nth 0 (nth 6 r)) (nth 1 (nth 6 r)) (nth 2 (nth 6 r)) (fn-lbc-restore-control (nth 4 old-homes) (nth 3 (nth 6 r)))) (nth 3 old-homes) (nth 3 r) (nth 5 r))))) (nov (nth 3 (nth 6 r))))
  (:instance lccp-canonical-restore-is-list (x (fn-hf-control (fn-held-facts (fn-held-make (nth 8 r) (car (nth 7 r)) (cadr (nth 7 r)) (nth 0 r) (nth 1 r) (nth 2 r) (nth 0 old-homes) (nth 1 old-homes) (nth 2 old-homes) (caddr (nth 7 r)) (nth 4 r) (fn-hf-make (nth 0 (nth 6 r)) (nth 1 (nth 6 r)) (nth 2 (nth 6 r)) (fn-lbc-restore-control (nth 4 old-homes) (nth 3 (nth 6 r)))) (nth 3 old-homes) (nth 3 r) (nth 5 r))))) (nov (nth 3 (nth 6 r)))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-held-p fn-held-shapep-of-fn-held-make fn-held-accessors-are-the-wire-accessors
 fn-record-accessors-of-held-make fn-hf-p fn-hf-shapep-of-fn-hf-make
 fn-hf-octets-of-fn-hf-make fn-hf-body-start-of-fn-hf-make
 fn-hf-body-lines-of-fn-hf-make fn-hf-control-of-fn-hf-make
 fn-lb-log-model-homes fn-lc-expected-home-frame fn-lb-log-model-home-frame
 fn-held-p-implies-cat-rowp lccm-nth-cons car-cons cdr-cons
 (:executable-counterpart zp)))))))

(local (defthm lccp-home-entry-after-prepared
 (let* ((old (fn-lb-log-model-segment id segs)) (start (len (cadr old)))
        (position (+ start 54 (len wire))))
  (implies (and (fn-lc-segsp segs) old entry
                (equal (nth 3 entry) (+ start 54)) (equal (nth 4 entry) (len wire))
                (not (fn-lb-log-model-home-entry position (caddr old))))
   (equal (fn-lb-log-model-home-entry position
            (caddr (fn-lb-log-model-segment id
              (fn-lc-append-prepared (list nil frame entry) id unit segs)))) entry)))
 :hints (("Goal" :use
 ((:instance lccm-fresh-home-entry-in-append
  (pos (+ (len (cadr (fn-lb-log-model-segment id segs))) 54 (len wire)))
  (entries (caddr (fn-lb-log-model-segment id segs)))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(lccm-segment-of-append-prepared lccm-nth-cons lccm-nfix-nat natp posp
 (:type-prescription len) car-cons cdr-cons (:executable-counterpart zp)
 (:executable-counterpart equal) associativity-of-+ commutativity-of-+ commutativity-2-of-+))))))

(local (defthm lccp-replay-loc0-at
 (implies (and (natp i) (natp (fn-lc-move-sequence move)))
  (equal (fn-lbc-loc0 i (fn-lc-replay-move move fn-lbc))
   (if (equal i (fn-lc-move-sequence move)) (fn-lc-move-loc0 move) (fn-lbc-loc0 i fn-lbc))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-replay-move fn-lbc-loc0 fn-lbc-row-store update-fn-lbc-loc0 update-fn-lbc-loc1
 update-fn-lbc-row-store fn-lbc-rowwords-get-loc0-is-nth
 fn-lbc-rowwords-set-loc0-is-update-nth fn-lbc-rowwords-set-loc1-is-update-nth
 fn-dm-nth-update-nth fn-dm-nth-of-zeros lccm-nfix-nat natp (:executable-counterpart nfix)
 (:executable-counterpart equal)))))))

(local (defthm lccp-replay-loc1-at
 (implies (and (natp i) (natp (fn-lc-move-sequence move)))
  (equal (fn-lbc-loc1 i (fn-lc-replay-move move fn-lbc))
   (if (equal i (fn-lc-move-sequence move)) (fn-lc-move-loc1 move) (fn-lbc-loc1 i fn-lbc))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-replay-move fn-lbc-loc1 fn-lbc-row-store update-fn-lbc-loc0 update-fn-lbc-loc1
 update-fn-lbc-row-store fn-lbc-rowwords-get-loc1-is-nth
 fn-lbc-rowwords-set-loc0-is-update-nth fn-lbc-rowwords-set-loc1-is-update-nth
 fn-dm-nth-update-nth fn-dm-nth-of-zeros lccm-nfix-nat natp (:executable-counterpart nfix)
 (:executable-counterpart equal)))))))

(local (defthm lccp-served-row-of-replay
 (implies (and (natp (fn-lc-move-sequence move)) (< (fn-lc-move-sequence move) (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-served-row i (fn-lc-replay-move move fn-lbc)) (fn-lbc-served-row i fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-replay-move lccp-served-row-of-loc0 lccp-served-row-of-loc1 lcoc-count-of-loc0 max lccm-nfix-nat natp (:type-prescription fn-lbc-count)))))))

(local (defthm lccp-home-read-needs-entry
 (implies (not (equal (fn-lc-read-home-frame position segs) :bad))
  (fn-lb-log-model-home-entry (cadr position) (caddr (fn-lb-log-model-segment (car position) segs))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-read-home-frame fn-lb-log-model-read-home-frame))))))

(local (defthm lccp-planned-home-entry
 (let* ((move (fn-lc-plan-move i header k r mode segs fn-lbc))
        (after (fn-lc-append-prepared (fn-lc-move-packet move) (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) (fn-lc-tail-unit header) segs)))
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)) (fn-lc-move-recordp move fn-lbc segs))
  (equal (fn-lbc-home-entry i (fn-lc-replay-move move fn-lbc) after) (fn-lc-at 4 move))))
 :hints (("Goal" :use
 ((:instance lccm-planned-move-geometry)
  (:instance lccm-planned-home-is-fresh)
  (:instance lccm-packed-locator-accessors (id (fn-lc-last-segment-id (fn-lc-ordered-segments segs))) (off (+ (len (fn-lc-at 1 (fn-lb-log-model-segment (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) segs))) 54)) (n (len (fn-lc-read-range (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs))))
  (:instance lccp-home-entry-after-prepared (id (fn-lc-last-segment-id (fn-lc-ordered-segments segs))) (entry (list (len (fn-lc-at 2 (fn-lb-log-model-segment (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) segs))) (len (fn-lc-at 1 (fn-lb-log-model-segment (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) segs))) (- (len (fn-lc-move-frame (fn-lc-at 3 (fn-lc-tail-scan segs header)) i (fn-lc-read-range (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs) (fn-lc-read-suf (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs))) 32) (+ (len (fn-lc-at 1 (fn-lb-log-model-segment (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) segs))) 54) (len (fn-lc-read-range (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs)) (fn-record-payload (fn-lc-bound-row i fn-lbc segs)) (fn-lb-log-payload (fn-lc-bound-row i fn-lbc segs) segs) (fn-lb-log-model-homes (fn-lc-bound-row i fn-lbc segs)) i))
    (wire (fn-lc-read-range (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs)) (frame (fn-lc-move-frame (fn-lc-at 3 (fn-lc-tail-scan segs header)) i (fn-lc-read-range (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs) (fn-lc-read-suf (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc) segs))) (unit (fn-lc-tail-unit header))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(lccm-plan-move-by-definition fn-lbc-home-entry lccp-replay-loc0-at lccp-replay-loc1-at
 fn-lc-move-sequence fn-lc-move-loc0 fn-lc-move-loc1 fn-lc-move-packet
 fn-lc-at-is-nth fn-lc-nth-1-alias fn-lc-nth-2-alias lccm-nth-cons lccm-len-cons
 lccm-nfix-nat natp (:type-prescription len) car-cons cdr-cons
 (:executable-counterpart equal) (:executable-counterpart len) (:executable-counterpart zp)
 (:executable-counterpart binary-+) associativity-of-+ commutativity-of-+ commutativity-2-of-+ fold-consts-in-+))))))

(local (defthm lccp-valid-move-new-home-entry
 (implies (fn-lc-move-recordp move fn-lbc segs)
  (equal (fn-lbc-home-entry (fn-lc-move-sequence move) (fn-lc-replay-move move fn-lbc)
   (fn-lc-append-prepared (fn-lc-move-packet move)
    (fn-lc-last-segment-id (fn-lc-ordered-segments segs))
    (fn-lc-tail-unit (fn-lc-at 5 move)) segs)) (fn-lc-at 4 move)))
 :hints (("Goal" :use
 ((:instance lccm-valid-move-is-plan)
  (:instance lccp-planned-home-entry (i (fn-lc-move-sequence move)) (header (fn-lc-at 5 move))
   (k (fn-lc-at 6 move)) (r (fn-lc-at 7 move)) (mode (fn-lc-at 8 move))))
 :in-theory (theory 'minimal-theory)))))

(local (defthm lccp-held-sequence-not-nil
 (implies (fn-held-p row) (fn-record-sequence row))
 :hints (("Goal" :use ((:instance fn-held-p-forward-natural-head (x row)))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-record-sequence fn-cbor-ag-car natp (:executable-counterpart car)))))))

(local (defthm lccp-locator-required-home-entry
 (implies (fn-lc-locator-resolves fn-lbc i segs)
   (fn-lbc-home-entry i fn-lbc segs))
 :hints (("Goal" :use
 ((:instance lccp-home-read-needs-entry (position (fn-lc-home-position (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-locator-resolves fn-lbc-home-entry fn-lc-home-position car-cons cdr-cons))))))

(local (defthm lccp-other-row-home-entry-after-move
 (let* ((after (fn-lc-append-prepared (fn-lc-move-packet move) id unit segs))
        (next (fn-lc-replay-move move fn-lbc)))
  (implies (and (fn-lc-segsp segs) (natp i) (natp (fn-lc-move-sequence move))
                (not (equal i (fn-lc-move-sequence move)))
                (fn-lc-locator-resolves fn-lbc i segs))
   (equal (fn-lbc-home-entry i next after) (fn-lbc-home-entry i fn-lbc segs))))
 :hints (("Goal" :use ((:instance lccp-locator-required-home-entry))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-home-entry lccp-replay-loc0-at lccp-replay-loc1-at lccm-segment-of-append-prepared
 lccm-existing-home-entry-survives-append car-cons cdr-cons))))))

(local (defthm lccp-other-bound-row-after-move
 (let* ((after (fn-lc-append-prepared (fn-lc-move-packet move) id unit segs))
        (next (fn-lc-replay-move move fn-lbc)))
  (implies (and (fn-lc-segsp segs) (natp i) (fn-lc-move-recordp move fn-lbc segs)
                (not (equal i (fn-lc-move-sequence move)))
                (fn-lc-locator-resolves fn-lbc i segs))
   (equal (fn-lc-bound-row i next after) (fn-lc-bound-row i fn-lbc segs))))
 :hints (("Goal" :use
 ((:instance lccm-valid-move-is-plan)
  (:instance lccp-other-row-home-entry-after-move))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-bound-row fn-lbc-at lccp-served-row-of-replay))))))

(local (defthm lccp-valid-move-input-shape
 (implies (fn-lc-move-recordp move fn-lbc segs)
  (and (fn-lc-segsp segs) (fn-held-p (fn-lc-bound-row (fn-lc-move-sequence move) fn-lbc segs))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lc-move-recordp))))))

(local (defthm lccp-moved-bound-row-observations
 (let* ((i (fn-lc-move-sequence move))
        (old (fn-lc-bound-row i fn-lbc segs))
        (after (fn-lc-append-prepared (fn-lc-move-packet move)
                (fn-lc-last-segment-id (fn-lc-ordered-segments segs))
                (fn-lc-tail-unit (fn-lc-at 5 move)) segs))
        (row (fn-lc-bound-row i (fn-lc-replay-move move fn-lbc) after)))
  (implies (fn-lc-move-recordp move fn-lbc segs)
   (and (fn-held-p row)
        (equal (fn-record-sequence row) (fn-record-sequence old))
        (equal (fn-record-payload row) (fn-record-payload old))
        (equal (fn-lb-log-model-homes row) (fn-lb-log-model-homes old))
        (equal (fn-lc-expected-home-frame row) (fn-lc-expected-home-frame old)))))
 :hints (("Goal" :use
 ((:instance lccm-valid-move-is-plan)
  (:instance lccp-valid-move-input-shape)
  (:instance lccp-valid-move-entry-fields)
  (:instance lccp-valid-move-new-home-entry)
  (:instance lccp-rehomed-row-observations
    (r (fn-lbc-served-row (fn-lc-move-sequence move) fn-lbc))
    (old-homes (nth 7 (fn-lbc-home-entry (fn-lc-move-sequence move) fn-lbc segs)))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-bound-row fn-lbc-at lccp-served-row-of-replay fn-lc-at-is-nth))))))

(local (defthm lccp-valid-move-locator-type
 (implies (fn-lc-move-recordp move fn-lbc segs)
  (fn-locp (fn-lc-move-loc0 move) (fn-lc-move-loc1 move)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-lc-move-recordp))))))

(local (defthm lccp-move-post-row-payload
 (implies (and (fn-lc-move-recordp move fn-lbc segs) (natp i)
                (fn-lc-locator-resolves fn-lbc i segs))
   (equal (fn-lb-log-payload (fn-lc-bound-row i (fn-lc-replay-move move fn-lbc) (fn-lc-append-prepared (fn-lc-move-packet move) (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) (fn-lc-tail-unit (fn-lc-at 5 move)) segs)) (fn-lc-append-prepared (fn-lc-move-packet move) (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) (fn-lc-tail-unit (fn-lc-at 5 move)) segs)) (fn-lb-log-payload (fn-lc-bound-row i fn-lbc segs) segs)))
 :hints (("Goal" :cases ((equal i (fn-lc-move-sequence move))) :use
 ((:instance lccp-valid-move-input-shape)
  (:instance lccp-moved-bound-row-observations)
  (:instance lccp-other-bound-row-after-move (id (fn-lc-last-segment-id (fn-lc-ordered-segments segs))) (unit (fn-lc-tail-unit (fn-lc-at 5 move))))
  (:instance lccp-held-sequence-not-nil (row (fn-lc-bound-row i fn-lbc segs)))
  (:instance lccp-move-append-preserves-global-payload (query (fn-lc-bound-row i fn-lbc segs)) (id (fn-lc-last-segment-id (fn-lc-ordered-segments segs))) (unit (fn-lc-tail-unit (fn-lc-at 5 move))))
  (:instance lccp-payload-key-congruence (a (fn-lc-bound-row i (fn-lc-replay-move move fn-lbc) (fn-lc-append-prepared (fn-lc-move-packet move) (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) (fn-lc-tail-unit (fn-lc-at 5 move)) segs))) (b (fn-lc-bound-row i fn-lbc segs)) (segs (fn-lc-append-prepared (fn-lc-move-packet move) (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) (fn-lc-tail-unit (fn-lc-at 5 move)) segs))))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lc-locator-resolves))))))

(local (defthm lccp-move-preserves-row-resolution
 (implies (and (fn-lc-move-recordp move fn-lbc segs) (natp i)
               (fn-lc-locator-resolves fn-lbc i segs))
  (fn-lc-locator-resolves (fn-lc-replay-move move fn-lbc) i (fn-lc-append-prepared (fn-lc-move-packet move) (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) (fn-lc-tail-unit (fn-lc-at 5 move)) segs)))
 :hints (("Goal" :cases ((equal i (fn-lc-move-sequence move))) :use
 ((:instance lccm-valid-move-is-plan)
  (:instance lccp-valid-move-input-shape)
  (:instance lccp-valid-move-locator-type)
  (:instance lccm-valid-move-byte-copies)
  (:instance lccp-moved-bound-row-observations)
  (:instance lccp-other-bound-row-after-move (id (fn-lc-last-segment-id (fn-lc-ordered-segments segs))) (unit (fn-lc-tail-unit (fn-lc-at 5 move))))
  (:instance lccp-move-post-row-payload)
  (:instance lccm-existing-range-survives-prepared (record (fn-lc-move-packet move))
   (id (fn-lc-last-segment-id (fn-lc-ordered-segments segs))) (unit (fn-lc-tail-unit (fn-lc-at 5 move))) (query (fn-loc-segment (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))
   (offset (fn-loc-offset (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc))) (n (fn-loc-len (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc))))
  (:instance lccm-existing-home-survives-prepared (record (fn-lc-move-packet move))
   (id (fn-lc-last-segment-id (fn-lc-ordered-segments segs))) (unit (fn-lc-tail-unit (fn-lc-at 5 move))) (position (fn-lc-home-position (fn-lbc-loc0 i fn-lbc) (fn-lbc-loc1 i fn-lbc)))))
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-locator-resolves fn-lc-read-range fn-lc-read-home-frame fn-lc-read-suf
 lccp-replay-loc0-at lccp-replay-loc1-at))))))

(local (defthm lccp-move-preserves-resolution-from
 (implies (and (fn-lc-move-recordp move fn-lbc segs) (natp i) (fn-lc-resolve-from i fn-lbc segs))
  (fn-lc-resolve-from i (fn-lc-replay-move move fn-lbc) (fn-lc-append-prepared (fn-lc-move-packet move) (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) (fn-lc-tail-unit (fn-lc-at 5 move)) segs)))
 :hints (("Goal" :induct (fn-lc-resolve-from i fn-lbc segs)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-resolve-from fn-lc-count lccm-count-of-bounded-replay
 lcrp-move-index-bounds lccp-move-preserves-row-resolution
 (:induction fn-lc-resolve-from) natp (:type-prescription fn-lbc-count)))))))

(local (defthm lccp-clean-success-preserves-resolution
 (let ((out (fn-lc-clean move disk segs outcome fn-lbc)))
  (implies (and (equal (mv-nth 0 out) :ok) (fn-lc-locators-resolve fn-lbc segs))
   (fn-lc-locators-resolve (mv-nth 1 out) (mv-nth 3 out))))
 :hints (("Goal" :use
 ((:instance lccm-clean-accepted-effects-by-definition)
  (:instance lccp-move-preserves-resolution-from (i 0)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lc-locators-resolve (:executable-counterpart natp)))))))

(local (defthm lccp-victims-of-replay
 (implies (and (natp i) (natp n) (fn-lc-move-recordp move fn-lbc segs)
               (not (equal (fn-lc-move-loc0 move) victim)))
  (equal (fn-lc-victim-rows-from i n victim (fn-lc-replay-move move fn-lbc))
         (remove-equal (fn-lc-move-sequence move) (fn-lc-victim-rows-from i n victim fn-lbc))))
 :hints (("Goal" :induct (fn-lc-victim-rows-from i n victim fn-lbc)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-victim-rows-from remove-equal lccm-count-of-bounded-replay
 lcrp-move-index-bounds lccp-replay-loc0-at lccm-nfix-nat
 (:induction fn-lc-victim-rows-from) natp nfix zp
 (:type-prescription fn-lbc-count) (:type-prescription nfix)
 car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart zp)
 (:executable-counterpart nfix)))))))

(local (defthm lccp-clean-success-count
 (implies (equal (mv-nth 0 (fn-lc-clean move disk segs outcome fn-lbc)) :ok)
  (equal (fn-lbc-count (mv-nth 1 (fn-lc-clean move disk segs outcome fn-lbc))) (fn-lbc-count fn-lbc)))
 :hints (("Goal" :use
 ((:instance lccm-clean-accepted-effects-by-definition) (:instance lccm-valid-move-is-plan))
 :in-theory (union-theories (theory 'minimal-theory) '(lccm-count-of-bounded-replay))))))

(local (defthm lccp-complete-work-preserves-resolution
 (let ((out (fn-lc-clean-work work fuel victim header k r mode disk segs outcome fn-lbc)))
  (implies (and (equal (mv-nth 0 out) :ok) (fn-lc-locators-resolve fn-lbc segs))
   (fn-lc-locators-resolve (mv-nth 1 out) (mv-nth 3 out))))
 :hints (("Goal" :induct (fn-lc-clean-work work fuel victim header k r mode disk segs outcome fn-lbc)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-clean-work lccp-clean-success-preserves-resolution fn-lc-head fn-lc-at-is-nth
 (:induction fn-lc-clean-work) mv-nth nth car-cons cdr-cons (:executable-counterpart zp)
 (:executable-counterpart equal)))))))

(local (defthm lccp-victim-indices-are-natural
 (nat-listp (fn-lc-victim-rows-from i n victim fn-lbc))
 :hints (("Goal" :induct (fn-lc-victim-rows-from i n victim fn-lbc)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-victim-rows-from nat-listp natp nfix
 (:induction fn-lc-victim-rows-from) (:type-prescription nfix)
 car-cons cdr-cons (:executable-counterpart nat-listp)))))))

(local (defthm lccp-difference-of-remove
 (equal (set-difference-equal (remove-equal x xs) rest)
        (set-difference-equal xs (cons x rest)))
 :hints (("Goal" :induct (len xs) :in-theory (union-theories (theory 'minimal-theory)
 '(set-difference-equal remove-equal member-equal len (:induction len) car-cons cdr-cons))))))

(local (defthm lccp-complete-work-count
 (let ((out (fn-lc-clean-work work fuel victim header k r mode disk segs outcome fn-lbc)))
  (implies (equal (mv-nth 0 out) :ok)
   (equal (fn-lbc-count (mv-nth 1 out)) (fn-lbc-count fn-lbc))))
 :hints (("Goal" :induct (fn-lc-clean-work work fuel victim header k r mode disk segs outcome fn-lbc)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-clean-work lccp-clean-success-count fn-lc-head fn-lc-at-is-nth
 (:induction fn-lc-clean-work) mv-nth nth car-cons cdr-cons (:executable-counterpart zp)
 (:executable-counterpart equal)))))))

(local (defthm lccp-valid-plan-index-and-target
 (let ((move (fn-lc-plan-move i header k r mode segs fn-lbc)))
  (implies (fn-lc-move-recordp move fn-lbc segs)
   (and (natp i) (< i (fn-lbc-count fn-lbc))
        (equal (fn-lc-move-sequence move) i)
        (equal (fn-lc-move-loc0 move) (fn-lc-last-segment-id (fn-lc-ordered-segments segs))))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-plan-move fn-lc-move-recordp fn-lc-move-sequence fn-lc-move-loc0
 fn-lc-at-is-nth fn-lc-head lccm-nth-cons lccm-len-cons
 car-cons cdr-cons (:executable-counterpart len) (:executable-counterpart true-listp)
 (:executable-counterpart zp) (:executable-counterpart equal)))))))

(local (defthm lccp-difference-of-subset
 (implies (subsetp-equal xs ys) (equal (set-difference-equal xs ys) nil))
 :hints (("Goal" :induct (len xs) :in-theory (union-theories (theory 'minimal-theory)
 '(subsetp-equal set-difference-equal len (:induction len) car-cons cdr-cons))))))

(local (defthm lccp-difference-of-self
 (equal (set-difference-equal xs xs) nil)
 :hints (("Goal" :use ((:instance lccp-difference-of-subset (ys xs)))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lc-subset-self))))))

(local (defthm lccp-victim-indices-are-list
 (true-listp (fn-lc-victim-rows-from i n victim fn-lbc))
 :hints (("Goal" :induct (fn-lc-victim-rows-from i n victim fn-lbc)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-victim-rows-from true-listp (:induction fn-lc-victim-rows-from)
 car-cons cdr-cons (:executable-counterpart true-listp)))))))

(local (defthm lccp-difference-of-nil
 (equal (set-difference-equal xs nil) (true-list-fix xs))
 :hints (("Goal" :induct (len xs) :in-theory (union-theories (theory 'minimal-theory)
 '(set-difference-equal member-equal true-list-fix len (:induction len) car-cons cdr-cons))))))

(local (defthm lccp-clean-success-victim-list
 (let ((out (fn-lc-clean move disk segs outcome fn-lbc)))
  (implies (and (equal (mv-nth 0 out) :ok) (not (equal (fn-lc-move-loc0 move) victim)))
   (equal (fn-lc-victim-rows-from 0 (fn-lbc-count (mv-nth 1 out)) victim (mv-nth 1 out))
          (remove-equal (fn-lc-move-sequence move)
           (fn-lc-victim-rows-from 0 (fn-lbc-count fn-lbc) victim fn-lbc)))))
 :hints (("Goal" :use
 ((:instance lccm-clean-accepted-effects-by-definition)
  (:instance lccp-victims-of-replay (i 0) (n (fn-lbc-count fn-lbc)))
  (:instance lccp-clean-success-count))
 :in-theory (union-theories (theory 'minimal-theory)
 '(natp (:type-prescription fn-lbc-count) (:executable-counterpart natp)))))))

(local (defthm lccp-planned-clean-success-victim-list
 (let* ((move (fn-lc-plan-move i header k r mode segs fn-lbc))
        (out (fn-lc-clean move disk segs outcome fn-lbc)))
  (implies (and (equal (mv-nth 0 out) :ok)
                (not (equal (fn-lc-last-segment-id (fn-lc-ordered-segments segs)) victim)))
   (equal (fn-lc-victim-rows-from 0 (fn-lbc-count (mv-nth 1 out)) victim (mv-nth 1 out))
          (remove-equal i (fn-lc-victim-rows-from 0 (fn-lbc-count fn-lbc) victim fn-lbc)))))
 :hints (("Goal" :use
 ((:instance lccm-clean-accepted-effects-by-definition (move (fn-lc-plan-move i header k r mode segs fn-lbc)))
  (:instance lccp-valid-plan-index-and-target)
  (:instance lccp-clean-success-victim-list (move (fn-lc-plan-move i header k r mode segs fn-lbc))))
 :in-theory (theory 'minimal-theory)))))

(local (defthm lccp-cons-car-cdr
 (implies (consp x) (equal (cons (car x) (cdr x)) x))
 :hints (("Goal" :use car-cdr-elim :in-theory (theory 'minimal-theory)))))

(local (defthm lccp-complete-work-victim-difference
 (let ((out (fn-lc-clean-work work fuel victim header k r mode disk segs outcome fn-lbc)))
  (implies (and (nat-listp work) (equal (mv-nth 0 out) :ok))
   (equal (fn-lc-victim-rows-from 0 (fn-lbc-count (mv-nth 1 out)) victim (mv-nth 1 out))
          (set-difference-equal (fn-lc-victim-rows-from 0 (fn-lbc-count fn-lbc) victim fn-lbc) work))))
 :hints (("Goal" :induct (fn-lc-clean-work work fuel victim header k r mode disk segs outcome fn-lbc)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-clean-work  lccp-planned-clean-success-victim-list

 lccp-difference-of-remove
 lccp-difference-of-nil lccp-victim-indices-are-list lccm-list-fix-of-list
 lccp-cons-car-cdr fn-lc-head fn-lc-at-is-nth nat-listp natp nfix
 (:induction fn-lc-clean-work) mv-nth nth car-cons cdr-cons (:executable-counterpart zp)
 (:executable-counterpart equal) (:executable-counterpart nat-listp)))))))

(local (defthm lccp-mv-nth-is-nth
 (equal (mv-nth n x) (nth n x))
 :hints (("Goal" :induct (mv-nth n x)
 :in-theory (union-theories (theory 'minimal-theory) '(mv-nth nth endp (:induction mv-nth)))))))

(defthm fn-lc-complete-cleaning-leaves-no-victim-locator
  (let ((out (fn-lc-clean-segment victim profile context disk segs outcome fn-lbc)))
    (implies (and (fn-lc-locators-resolve fn-lbc segs)
                  (fn-lc-segment-moves-completep out victim))
             (and (not (fn-lc-any-row-names-segment victim (mv-nth 1 out)))
                  (fn-lc-locators-resolve (mv-nth 1 out) (mv-nth 3 out)))))
  :rule-classes nil :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lc-clean-segment fn-lc-segment-moves-completep fn-lc-any-row-names-segment
 lccp-complete-work-victim-difference lccp-complete-work-preserves-resolution
 lccp-victim-indices-are-natural lccp-difference-of-self
 fn-lc-head fn-lc-at-is-nth mv-nth nth car-cons cdr-cons
 (:executable-counterpart zp) (:executable-counterpart equal))))))

(make-event (mv-let (err expansion state)
 (fn-dt-expand 'fn-lc-complete-cleaning-leaves-no-victim-locator 'defteeth '(:claim
 (let ((out (fn-lc-clean-segment victim profile context disk segs outcome fn-lbc)))
  (((resolves (fn-lc-locators-resolve fn-lbc segs))
    (complete (fn-lc-segment-moves-completep out victim)))
   (and (not (fn-lc-any-row-names-segment victim (mv-nth 1 out)))
        (fn-lc-locators-resolve (mv-nth 1 out) (mv-nth 3 out)))))
 :subject fn-lc-clean-segment
 :witness ((victim 1) (profile '(1))
   (context (list :lc :eager (fn-lc-at 2 (lcm-test-input 1)) 1))
   (disk (fn-lc-at 0 (lcm-test-input 1)))
   (segs (fn-lc-at 1 (lcm-test-input 1))) (outcome '(:ok :ok)))
 :stobjs ((fn-lbc (lcm-complete-seed fn-lbc)))
 :stobj-checks
 (((let ((out (fn-lc-clean-segment victim profile context disk segs outcome fn-lbc))) (declare (ignorable out)) (fn-lc-locators-resolve fn-lbc segs)) (lcm-complete-pre-tooth segs fn-lbc)
    :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(lcm-complete-pre-tooth lcm-complete-ack-tooth lcm-complete-post-tooth lcm-complete-inverted-tooth fn-lc-segment-moves-completep fn-lc-head fn-lc-at-is-nth lccp-mv-nth-is-nth nth car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart equal))))))
  ((let ((out (fn-lc-clean-segment victim profile context disk segs outcome fn-lbc)))
    (declare (ignorable out)) (fn-lc-segment-moves-completep out victim))
   (lcm-complete-ack-tooth victim profile context disk segs outcome fn-lbc)
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(lcm-complete-pre-tooth lcm-complete-ack-tooth lcm-complete-post-tooth lcm-complete-inverted-tooth fn-lc-segment-moves-completep fn-lc-head fn-lc-at-is-nth lccp-mv-nth-is-nth nth car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart equal))))))
  ((let ((out (fn-lc-clean-segment victim profile context disk segs outcome fn-lbc)))
    (declare (ignorable out))
    (and (not (fn-lc-any-row-names-segment victim (mv-nth 1 out)))
         (fn-lc-locators-resolve (mv-nth 1 out) (mv-nth 3 out))))
   (lcm-complete-post-tooth victim profile context disk segs outcome fn-lbc)
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(lcm-complete-pre-tooth lcm-complete-ack-tooth lcm-complete-post-tooth lcm-complete-inverted-tooth fn-lc-segment-moves-completep fn-lc-head fn-lc-at-is-nth lccp-mv-nth-is-nth nth car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart equal))))))
  ((let ((out (fn-lc-clean-segment victim profile context disk segs outcome fn-lbc)))
    (declare (ignorable out)) (fn-lc-any-row-names-segment victim (mv-nth 1 out)))
   (lcm-complete-inverted-tooth victim profile context disk segs outcome fn-lbc)
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(lcm-complete-pre-tooth lcm-complete-ack-tooth lcm-complete-post-tooth lcm-complete-inverted-tooth fn-lc-segment-moves-completep fn-lc-head fn-lc-at-is-nth lccp-mv-nth-is-nth nth car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart equal)))))))
 :breaks ((resolves ((victim 2) (segs nil)))
          (complete ((profile '(0)))))
 :mutations ((victim-survives
  (:conclusion (fn-lc-any-row-names-segment victim (mv-nth 1 out))) nil
  :fault "completed relocation retained a victim locator"))) state)
 (if err (mv err expansion state)
  (value (cons 'progn (fn-lc-teeth-prepare-wrappers (cdr expansion)
   '(("Goal" :in-theory (union-theories (theory 'minimal-theory) '(lcm-complete-seed))))))))))

(defteeth fn-lc-complete-cleaning-leaves-no-victim-locator
 :claim
 (let ((out (fn-lc-clean-segment victim profile context disk segs outcome fn-lbc)))
  (((resolves (fn-lc-locators-resolve fn-lbc segs))
    (complete (fn-lc-segment-moves-completep out victim)))
   (and (not (fn-lc-any-row-names-segment victim (mv-nth 1 out)))
        (fn-lc-locators-resolve (mv-nth 1 out) (mv-nth 3 out)))))
 :subject fn-lc-clean-segment
 :witness ((victim 1) (profile '(1))
   (context (list :lc :eager (fn-lc-at 2 (lcm-test-input 1)) 1))
   (disk (fn-lc-at 0 (lcm-test-input 1)))
   (segs (fn-lc-at 1 (lcm-test-input 1))) (outcome '(:ok :ok)))
 :stobjs ((fn-lbc (lcm-complete-seed fn-lbc)))
 :stobj-checks
 (((let ((out (fn-lc-clean-segment victim profile context disk segs outcome fn-lbc))) (declare (ignorable out)) (fn-lc-locators-resolve fn-lbc segs)) (lcm-complete-pre-tooth segs fn-lbc)
    :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(lcm-complete-pre-tooth lcm-complete-ack-tooth lcm-complete-post-tooth lcm-complete-inverted-tooth fn-lc-segment-moves-completep fn-lc-head fn-lc-at-is-nth lccp-mv-nth-is-nth nth car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart equal))))))
  ((let ((out (fn-lc-clean-segment victim profile context disk segs outcome fn-lbc)))
    (declare (ignorable out)) (fn-lc-segment-moves-completep out victim))
   (lcm-complete-ack-tooth victim profile context disk segs outcome fn-lbc)
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(lcm-complete-pre-tooth lcm-complete-ack-tooth lcm-complete-post-tooth lcm-complete-inverted-tooth fn-lc-segment-moves-completep fn-lc-head fn-lc-at-is-nth lccp-mv-nth-is-nth nth car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart equal))))))
  ((let ((out (fn-lc-clean-segment victim profile context disk segs outcome fn-lbc)))
    (declare (ignorable out))
    (and (not (fn-lc-any-row-names-segment victim (mv-nth 1 out)))
         (fn-lc-locators-resolve (mv-nth 1 out) (mv-nth 3 out))))
   (lcm-complete-post-tooth victim profile context disk segs outcome fn-lbc)
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(lcm-complete-pre-tooth lcm-complete-ack-tooth lcm-complete-post-tooth lcm-complete-inverted-tooth fn-lc-segment-moves-completep fn-lc-head fn-lc-at-is-nth lccp-mv-nth-is-nth nth car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart equal))))))
  ((let ((out (fn-lc-clean-segment victim profile context disk segs outcome fn-lbc)))
    (declare (ignorable out)) (fn-lc-any-row-names-segment victim (mv-nth 1 out)))
   (lcm-complete-inverted-tooth victim profile context disk segs outcome fn-lbc)
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(lcm-complete-pre-tooth lcm-complete-ack-tooth lcm-complete-post-tooth lcm-complete-inverted-tooth fn-lc-segment-moves-completep fn-lc-head fn-lc-at-is-nth lccp-mv-nth-is-nth nth car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart equal)))))))
 :breaks ((resolves ((victim 2) (segs nil)))
          (complete ((profile '(0)))))
 :mutations ((victim-survives
  (:conclusion (fn-lc-any-row-names-segment victim (mv-nth 1 out))) nil
  :fault "completed relocation retained a victim locator")))

(defteeth-check (fn-lc-complete-cleaning-leaves-no-victim-locator))
