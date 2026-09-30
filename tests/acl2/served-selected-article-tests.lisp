(in-package "ACL2")
(include-book "../../books/served-selected-article")

(defun ssat-row (number id payload)
 (declare (xargs :guard t))
 (fn-held-with-numbers
  (fn-held-plain (fn-record-make 0 1 0 id '(65) '("fn.test") "o" "s" "e" 1 5) payload)
  (list (cons "fn.test" number))))
(defun-nx ssat-source-conclusionp (number fn-arena fn-cat)
 (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
 (let* ((seq (fn-cnx-view-seq "fn.test" number 1 fn-cat))
        (h (fn-record-payload (fn-cat-at seq fn-cat))))
  (equal (fn-nntp-article-bytes
            (fn-scat-available-article "fn.test" number 1 fn-arena fn-cat) fn-arena)
         (nth h fn-arena))))

(defthm ssat-actual-selected-source-positive
 (let* ((number 1) (fn-arena '((65)))
        (fn-cat (list (ssat-row number "<e@x>" 0)))
        (seq (fn-cnx-view-seq "fn.test" number 1 fn-cat))
        (h (fn-record-payload (fn-cat-at seq fn-cat))))
  (and (posp number) (<= number *fn-nntp-max-article-number*) seq
       (fn-nntp-article-idp (fn-cat-row-article seq fn-arena fn-cat))
       (natp h) (equal seq 0)
       (ssat-source-conclusionp number fn-arena fn-cat)))
 :rule-classes nil)

; Corrupted-state literal removal: all four retained hypotheses hold.
(defthm ssat-without-positive-number-corrupted-state
 (let* ((number 0) (fn-arena '((65)))
        (fn-cat (list (ssat-row 0 "<e@x>" 0)))
        (seq (fn-cnx-view-seq "fn.test" number 1 fn-cat))
        (h (fn-record-payload (fn-cat-at seq fn-cat))))
  (and (not (posp number)) (<= number *fn-nntp-max-article-number*) seq (fn-nntp-article-idp (fn-cat-row-article seq fn-arena fn-cat)) (natp h)
       (not (ssat-source-conclusionp number fn-arena fn-cat))))
 :rule-classes nil)

; Corrupted-state literal removal: all four retained hypotheses hold.
(defthm ssat-without-number-bound-corrupted-state
 (let* ((number (+ 1 *fn-nntp-max-article-number*)) (fn-arena '((65)))
        (fn-cat (list (ssat-row (+ 1 *fn-nntp-max-article-number*) "<e@x>" 0)))
        (seq (fn-cnx-view-seq "fn.test" number 1 fn-cat))
        (h (fn-record-payload (fn-cat-at seq fn-cat))))
  (and (posp number) (not (<= number *fn-nntp-max-article-number*)) seq (fn-nntp-article-idp (fn-cat-row-article seq fn-arena fn-cat)) (natp h)
       (not (ssat-source-conclusionp number fn-arena fn-cat))))
 :rule-classes nil)

; Corrupted-state literal removal: all four retained hypotheses hold.
(defthm ssat-without-selected-sequence-corrupted-state
 (let* ((number 2) (fn-arena '((65)))
        (fn-cat (list (ssat-row 1 "<e@x>" 0)))
        (seq (fn-cnx-view-seq "fn.test" number 1 fn-cat))
        (h (fn-record-payload (fn-cat-at seq fn-cat))))
  (and (posp number) (<= number *fn-nntp-max-article-number*) (not seq) (fn-nntp-article-idp (fn-cat-row-article seq fn-arena fn-cat)) (natp h)
       (not (ssat-source-conclusionp number fn-arena fn-cat))))
 :rule-classes nil)

; Corrupted-state literal removal: all four retained hypotheses hold.
(defthm ssat-without-article-id-corrupted-state
 (let* ((number 1) (fn-arena '((65)))
        (fn-cat (list (ssat-row 1 "bad" 0)))
        (seq (fn-cnx-view-seq "fn.test" number 1 fn-cat))
        (h (fn-record-payload (fn-cat-at seq fn-cat))))
  (and (posp number) (<= number *fn-nntp-max-article-number*) seq (not (fn-nntp-article-idp (fn-cat-row-article seq fn-arena fn-cat))) (natp h)
       (not (ssat-source-conclusionp number fn-arena fn-cat))))
 :rule-classes nil)

; Corrupted-state literal removal: all four retained hypotheses hold.
(defthm ssat-without-natural-handle-corrupted-state
 (let* ((number 1) (fn-arena '((65)))
        (fn-cat (list (ssat-row 1 "<e@x>" -1)))
        (seq (fn-cnx-view-seq "fn.test" number 1 fn-cat))
        (h (fn-record-payload (fn-cat-at seq fn-cat))))
  (and (posp number) (<= number *fn-nntp-max-article-number*) seq (fn-nntp-article-idp (fn-cat-row-article seq fn-arena fn-cat)) (not (natp h))
       (not (ssat-source-conclusionp number fn-arena fn-cat))))
 :rule-classes nil)

(defun ssat-actual-committed-row (fn-arena fn-cat)
 (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
 (let* ((fn-arena (fn-arena-clear fn-arena)) (fn-cat (fn-cat-clear fn-cat))
        (wire (fn-record-make 0 1 0 "<e@x>" '(65) '("fn.test") "o" "s" "e" 1 5)))
  (mv-let (row fn-arena) (fn-cat-intern-list wire nil 0 fn-arena)
   (let* ((fn-cat (fn-cat-commit (fn-held-plain wire (fn-record-payload row)) fn-cat))
          (seq (fn-cnx-view-seq "fn.test" 1 1 fn-cat))
          (h (fn-record-payload (fn-cat-at seq fn-cat))))
    (mv (and (fn-arena-p fn-arena) (fn-cat-p fn-cat)
             (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
             (posp 1) (<= 1 *fn-nntp-max-article-number*) seq
             (fn-nntp-article-idp (fn-cat-row-article seq fn-arena fn-cat))
             (natp h) (equal seq 0)
             (equal (fn-nntp-article-bytes
                       (fn-scat-available-article "fn.test" 1 1 fn-arena fn-cat) fn-arena)
                    (fn-arena-payload h fn-arena))) fn-arena fn-cat)))))

; Reachable witness from actual intern/commit with all real getter guards.
(assert-event
 (mv-let (good fn-arena fn-cat) (ssat-actual-committed-row fn-arena fn-cat)
  (mv good fn-arena fn-cat)) :stobjs-out '(nil fn-arena fn-cat))
