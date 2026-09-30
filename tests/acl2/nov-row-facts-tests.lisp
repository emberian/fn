(in-package "ACL2")
(include-book "../../books/nov-row-facts")
(include-book "nov-column-window-tests")

(defun nrft-replace-facts (row facts)
  (declare (xargs :guard t))
  (fn-held-make (fn-record-sequence row) (fn-record-txid row)
                (fn-record-generation row) (fn-record-msgid row)
                (fn-record-payload row) (fn-record-groups row)
                (fn-record-obligation-id row) (fn-record-content-subject row)
                (fn-record-release-evidence row) (fn-record-charge row)
                (fn-record-stamp row) facts (fn-held-context row) nil nil))

; Actual intern/commit plus the new direct row lookup. The corrupt variant
; changes only decided facts; the missing-cache variant is a legacy row.
(defun nrft-case (corruptp legacyp bad-verdictp wrong-sourcep fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let* ((fn-arena (fn-arena-clear fn-arena)) (fn-cat (fn-cat-clear fn-cat)))
    (mv-let (row fn-arena)
      (fn-cat-intern-list
       (if bad-verdictp
           (fn-record-make 0 1 0 "<nbwct@example.invalid>" '(1 2 3 255)
                           '("fn.test") "o" "s" "e" 1 5)
         (nbwct-wire)) nil 0 fn-arena)
      (let* ((row (if corruptp (nbwct-corrupt-facts row) row))
             (oldfacts (fn-held-facts row))
             (row (if legacyp
                      (nrft-replace-facts
                       row (fn-hf-make (fn-hf-octets oldfacts)
                                       (fn-hf-body-start oldfacts)
                                       (fn-hf-body-lines oldfacts)
                                       (take 3 (fn-hf-control oldfacts)))) row))
             (fn-cat (fn-cat-commit row fn-cat))
             (article (fn-make-article (fn-record-msgid row)
                                       (if wrong-sourcep nil (fn-record-payload row))
                                       (fn-record-groups row) (fn-held-numbers row)
                                       t (fn-record-stamp row)))
             (facts (fn-nrf-facts 0 fn-cat))
             (lhs (nbwct-remaining
                   (fn-nbw-column-pieces 1 facts (fn-nntp-article-length article fn-arena)) 0))
             (rhs (append (fn-nov-line 1 (fn-nov-overview article fn-arena)) '(13 10))))
        (mv (list (nbwct-f fn-arena fn-cat) facts
                  (equal facts (fn-held-facts-of (fn-nntp-article-bytes article fn-arena)))
                  (fn-hnov-ok (fn-hf-nov facts)) (equal lhs rhs)
                  (equal (fn-article-payload article)
                         (fn-record-payload (fn-cat-at 0 fn-cat))))
            fn-arena fn-cat)))))

; Complete antecedents and conclusions of both public refinements.
(assert-event
 (mv-let (r fn-arena fn-cat) (nrft-case nil nil nil nil fn-arena fn-cat)
   (mv (and (nth 0 r) (nth 1 r) (nth 2 r) (nth 3 r) (nth 4 r) (nth 5 r)) fn-arena fn-cat))
 :stobjs-out '(nil fn-arena fn-cat))

; Remove F only: true cache shape/ok and existence, wrong immutable source.
(assert-event
 (mv-let (r fn-arena fn-cat) (nrft-case t nil nil nil fn-arena fn-cat)
   (mv (and (not (nth 0 r)) (nth 1 r) (not (nth 2 r))
            (nth 3 r) (not (nth 4 r)) (nth 5 r)) fn-arena fn-cat))
 :stobjs-out '(nil fn-arena fn-cat))

; Remove existence only from facts refinement: F permits a legacy no-cache
; row, whose source is still a real article with nonnil decided byte facts.
(assert-event
 (mv-let (r fn-arena fn-cat) (nrft-case nil t nil nil fn-arena fn-cat)
   (mv (and (nth 0 r) (not (nth 1 r)) (not (nth 2 r))) fn-arena fn-cat))
 :stobjs-out '(nil fn-arena fn-cat))

; Remove ok only from full-row refinement: the truthful invalid cache is
; present and exact, but its constructor must not be emitted as a NOV row.
(assert-event
 (mv-let (r fn-arena fn-cat) (nrft-case nil nil t nil fn-arena fn-cat)
   (mv (and (nth 0 r) (nth 1 r) (nth 2 r)
            (not (nth 3 r)) (not (nth 4 r)) (nth 5 r)) fn-arena fn-cat))
 :stobjs-out '(nil fn-arena fn-cat))

; Remove exact source identity only: row facts remain truthful and valid.
(assert-event
 (mv-let (r fn-arena fn-cat) (nrft-case nil nil nil t fn-arena fn-cat)
   (mv (and (nth 0 r) (nth 1 r) (nth 3 r)
            (not (nth 5 r)) (not (nth 4 r))) fn-arena fn-cat))
 :stobjs-out '(nil fn-arena fn-cat))
