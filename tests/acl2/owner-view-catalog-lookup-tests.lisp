; fn: teeth for books/owner-view-catalog-lookup.lisp (lane s-viewidx, P1).
;
; fn-owner-view-lookup-is-the-catalog-walk, per literal theorem:
;  - the positive witness: a three-row catalog (a visible, b withdrawn by a
;    cancel at version 2, c visible), the view whose archive is the
;    catalog's visible rows, fn-scj-joinp asserted whole, and the equation
;    for the visible id, the withdrawn id and an id the catalog never held;
;  - the hypothesis-removal witness: the same view over the same catalog
;    with row b's withdrawal mark removed.  The retained conjuncts of the
;    join (marks below the count, rows below the version) hold, the omitted
;    one (the catalog's visible rows are the archive) fails, and so does the
;    conclusion.
; The catalog and arena are the logical lists, as books/catalog-delta's
; tests use them.

(in-package "ACL2")
(include-book "../../books/owner-view-catalog-lookup")
(include-book "must-fail-checked")

(defconst *ovl-p0* (append (fn-record-string-octets "Subject: a") '(13 10 13 10 65 13 10)))
(defconst *ovl-p1* (append (fn-record-string-octets "Subject: b") '(13 10 13 10 66 13 10)))
(defconst *ovl-p2* (append (fn-record-string-octets "Subject: c") '(13 10 13 10 67 13 10)))

(defun ovl-held (seq msgid handle bytes)
  (fn-held-make seq (+ 1 seq) 0 msgid handle '("fn.test") "o" "s" "e" 1 5
                (fn-held-facts-of bytes) (fn-held-context-of bytes nil 0) nil nil))

(defconst *ovl-a* (list *ovl-p0* *ovl-p1* *ovl-p2*))

(defconst *ovl-r0* (fn-cat-assign (ovl-held 0 "<a@x>" 0 *ovl-p0*) nil))
(defconst *ovl-r1* (fn-cat-assign (ovl-held 1 "<b@x>" 1 *ovl-p1*) (list *ovl-r0*)))
(defconst *ovl-r2* (fn-cat-assign (ovl-held 2 "<c@x>" 2 *ovl-p2*) (list *ovl-r0* *ovl-r1*)))

; all three rows live, and with b withdrawn at version 2 by row 2
(defconst *ovl-c-live* (list *ovl-r0* *ovl-r1* *ovl-r2*))
(defconst *ovl-c* (fn-cat-mark-withdrawn 1 2 2 *ovl-c-live*))

; the views: archive = the catalog's visible rows at its count (version 3)
(defun ovl-art (h)
  (fn-make-article (fn-record-msgid h) (fn-record-payload h) (fn-record-groups h)
                   (fn-held-numbers h) t (fn-record-stamp h)))
; newest first, built from the rows (not from the catalog's walk)
(defconst *ovl-articles* (list (ovl-art *ovl-r2*) (ovl-art *ovl-r0*)))
(defconst *ovl-view*
  (fn-own-view-make 3 nil (fn-make-state '("fn.test") (fn-initial-nexts '("fn.test"))
                                         *ovl-articles* 3 nil nil)))

(defthm ovl-w-fixture
  (and (equal (len *ovl-articles*) 2)
       (equal (fn-record-msgid (fn-cat-at 1 *ovl-c*)) "<b@x>")
       (equal (fn-held-withdrawn (fn-cat-at 1 *ovl-c*)) '(2 . 2))
       (null (fn-held-withdrawn (fn-cat-at 1 *ovl-c-live*))))
  :rule-classes nil)

; The positive witness, the whole antecedent (the join, conjunct by conjunct)
; and the whole conclusion, for a visible id, the withdrawn id, an absent id.
(defthm ovl-w-lookup-is-the-catalog-walk
  (and (equal (fn-cat-view-articles (fn-cat-count *ovl-c*) *ovl-a* *ovl-c*)
              (fn-state-articles (fn-own-view-archive *ovl-view*)))
       (fn-scj-marks-below *ovl-c* (fn-cat-count *ovl-c*))
       (fn-scj-seqs-below *ovl-c* (fn-own-view-version *ovl-view*))
       (fn-scj-joinp *ovl-view* *ovl-a* *ovl-c*)
       ; a: visible; its article is the walk's
       (fn-find-article "<a@x>" (fn-state-articles (fn-own-view-archive *ovl-view*)))
       (equal (fn-find-article "<a@x>" (fn-state-articles (fn-own-view-archive *ovl-view*)))
              (let ((seq (fn-cat-view-last-visible (fn-cat-msgid-seqs "<a@x>" *ovl-c*)
                                                   (fn-cat-count *ovl-c*) *ovl-c*)))
                (if seq (fn-cat-row-article seq *ovl-a* *ovl-c*) nil)))
       (equal (fn-find-article "<c@x>" (fn-state-articles (fn-own-view-archive *ovl-view*)))
              (let ((seq (fn-cat-view-last-visible (fn-cat-msgid-seqs "<c@x>" *ovl-c*)
                                                   (fn-cat-count *ovl-c*) *ovl-c*)))
                (if seq (fn-cat-row-article seq *ovl-a* *ovl-c*) nil)))
       ; b: withdrawn; both sides are nil
       (null (fn-find-article "<b@x>" (fn-state-articles (fn-own-view-archive *ovl-view*))))
       (null (let ((seq (fn-cat-view-last-visible (fn-cat-msgid-seqs "<b@x>" *ovl-c*)
                                                  (fn-cat-count *ovl-c*) *ovl-c*)))
               (if seq (fn-cat-row-article seq *ovl-a* *ovl-c*) nil)))
       ; d: never held
       (null (fn-find-article "<d@x>" (fn-state-articles (fn-own-view-archive *ovl-view*))))
       (null (fn-cat-msgid-seqs "<d@x>" *ovl-c*)))
  :rule-classes nil)

; Hypothesis removal: the same view over the catalog without b's mark.  The
; retained conjuncts hold; the omitted one fails; the conclusion fails at b.
(defthm ovl-w-without-the-join
  (and (fn-scj-marks-below *ovl-c-live* (fn-cat-count *ovl-c-live*))
       (fn-scj-seqs-below *ovl-c-live* (fn-own-view-version *ovl-view*))
       (not (equal (fn-cat-view-articles (fn-cat-count *ovl-c-live*) *ovl-a* *ovl-c-live*)
                   (fn-state-articles (fn-own-view-archive *ovl-view*))))
       (null (fn-find-article "<b@x>" (fn-state-articles (fn-own-view-archive *ovl-view*))))
       (equal (fn-cat-view-last-visible (fn-cat-msgid-seqs "<b@x>" *ovl-c-live*)
                                        (fn-cat-count *ovl-c-live*) *ovl-c-live*)
              1)
       (not (equal (fn-find-article "<b@x>" (fn-state-articles (fn-own-view-archive *ovl-view*)))
                   (let ((seq (fn-cat-view-last-visible (fn-cat-msgid-seqs "<b@x>" *ovl-c-live*)
                                                        (fn-cat-count *ovl-c-live*) *ovl-c-live*)))
                     (if seq (fn-cat-row-article seq *ovl-a* *ovl-c-live*) nil)))))
  :rule-classes nil)

(must-fail-checked
 (defthm ovl-r-without-the-join
   (equal (fn-find-article "<b@x>" (fn-state-articles (fn-own-view-archive *ovl-view*)))
          (let ((seq (fn-cat-view-last-visible (fn-cat-msgid-seqs "<b@x>" *ovl-c-live*)
                                               (fn-cat-count *ovl-c-live*) *ovl-c-live*)))
            (if seq (fn-cat-row-article seq *ovl-a* *ovl-c-live*) nil)))
   :rule-classes nil))
