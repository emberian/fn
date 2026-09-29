; Witnesses for books/msgid-pages.lisp (lane paged-history, PRF-957).
;
; The tag is attached here to a COLLIDING function (the salted FNV hash
; modulo 3), so every third Message-ID shares a tag and the confirmation,
; not the hash, decides: that is the property the keystone claims.
;
; REACHABLE: a four-row history (two rows under <a@x>, one under <b@x>, a
; retention event that is no article) and the two-page table a writer
; builds by home page; the keystone's complete antecedent (fn-mpx-tablep,
; fn-mpx-faithful) is checked and its conclusion, for a Message-ID with two
; records (in history order), one record, and none; then the OVERFLOW
; placement (an entry on the page after its home) and a STALE entry
; (corrupted state, labelled: an entry naming a row with another
; Message-ID, which the confirmation drops).
; HYPOTHESIS-REMOVAL: fn-mpx-table-okp dropped (a page out of sequence
; order: faithful-from holds, the conclusion fails on order) and
; fn-mpx-faithful-from dropped (an entry missing: table-okp holds, the
; conclusion fails on completeness).  fn-mpx-tablep: no removal witness
; found (a non-natural seq reads as 0 under nth and either breaks table-okp
; or is covered by the confirmation); its redundancy is a proof task, not a
; counterexample, so the hypothesis stays.
(in-package "ACL2")
(include-book "../../books/msgid-pages")
(include-book "../../tests/acl2/history-columns-tests")

; ---------------------------------------------------------------------------
; The tag for these tests: FNV-32 modulo 3 (collisions on purpose).

(defun mpxt-tag (msgid)
  (declare (xargs :guard t))
  (if (stringp msgid) (mod (fn-hist-hash msgid 0) 3) 0))

(defthm mpxt-tag-natp
  (natp (mpxt-tag msgid))
  :rule-classes :type-prescription)

(defattach fn-mpx-tag mpxt-tag)

; ---------------------------------------------------------------------------
; Fixtures: the history-columns rows (seq 0 <a@x>, 1 <b@x>, 2 a retention
; event, 3 <a@x> again) and a writer by home page.

(defconst *mpxt-rows* (list *hct-a* *hct-b* *hct-retention* *hct-a2*))

; Append (TAG . SEQ) to page I of TAB (TAB has NPAGES pages, nil when empty).
(defun mpxt-put (i entry tab)
  (declare (xargs :guard (and (natp i) (true-listp tab))))
  (if (zp i)
      (cons (append (car tab) (list entry)) (cdr tab))
    (cons (car tab) (mpxt-put (- i 1) entry (cdr tab)))))

; The writer: every held row's (tag . seq) onto its home page, in history
; order (so a page's seqs ascend).
(defun mpxt-build (seq rows npages tab)
  (declare (xargs :guard (and (natp seq) (true-listp rows) (natp npages) (true-listp tab))))
  (if (consp rows)
      (let ((rec (fn-cei-event-article (car rows))))
        (mpxt-build (+ 1 seq) (cdr rows) npages
                    (if (fn-held-p rec)
                        (let ((tag (mpxt-tag (fn-record-msgid rec))))
                          (mpxt-put (fn-mpx-home tag npages) (cons tag seq) tab))
                      tab)))
    tab))

(defconst *mpxt-empty-2* (list nil nil))
(defconst *mpxt-table* (mpxt-build 0 *mpxt-rows* 2 *mpxt-empty-2*))

; ---------------------------------------------------------------------------
; REACHABLE: the keystone's antecedent and conclusion.

(assert-event (fn-mpx-tablep *mpxt-table*))
(assert-event (fn-mpx-faithful *mpxt-table* *mpxt-rows*))
; two records under <a@x>, in history order
(assert-event (equal (fn-mpx-records "<a@x>" *mpxt-table* *mpxt-rows*)
                     (list *hct-a* *hct-a2*)))
(assert-event (equal (fn-mpx-records "<a@x>" *mpxt-table* *mpxt-rows*)
                     (fn-cei-article-records-for "<a@x>" *mpxt-rows*)))
(assert-event (equal (fn-mpx-records "<a@x>" *mpxt-table* *mpxt-rows*)
                     (fn-hist$a-msgid-records "<a@x>" *mpxt-rows*)))
; one record
(assert-event (equal (fn-mpx-records "<b@x>" *mpxt-table* *mpxt-rows*)
                     (list *hct-b*)))
; none: a Message-ID no row has (its tag collides with one that does)
(assert-event (equal (fn-mpx-records "<z@x>" *mpxt-table* *mpxt-rows*) nil))
(assert-event (equal (fn-cei-article-records-for "<z@x>" *mpxt-rows*) nil))
; the tags collide on purpose: at most three distinct
(assert-event (< (mpxt-tag "<a@x>") 3))

; OVERFLOW placement: <a@x>'s second entry on the page after its home; the
; table stays faithful (the candidates merge both pages) and the reader
; still answers in history order.
(defconst *mpxt-tag-a* (mpxt-tag "<a@x>"))
(defconst *mpxt-home-a* (fn-mpx-home *mpxt-tag-a* 2))
(defconst *mpxt-table-overflow*
  (mpxt-put (fn-mpx-home (+ 1 *mpxt-home-a*) 2) (cons *mpxt-tag-a* 3)
            (mpxt-build 0 (list *hct-a* *hct-b* *hct-retention*) 2 *mpxt-empty-2*)))
(assert-event (fn-mpx-tablep *mpxt-table-overflow*))
(assert-event (fn-mpx-faithful *mpxt-table-overflow* *mpxt-rows*))
(assert-event (equal (fn-mpx-records "<a@x>" *mpxt-table-overflow* *mpxt-rows*)
                     (list *hct-a* *hct-a2*)))

; CORRUPTED STATE (labelled): a stale entry under <a@x>'s tag naming row 1
; (<b@x>).  Faithfulness only needs presence, so it holds; the confirmation
; drops the stale row and the answer is still the specification.
(defconst *mpxt-table-stale*
  (mpxt-put *mpxt-home-a* (cons *mpxt-tag-a* 1)
            (mpxt-build 0 (list *hct-a*) 2 *mpxt-empty-2*)))
(defconst *mpxt-rows-a* (list *hct-a* *hct-b*))
(assert-event (fn-mpx-faithful *mpxt-table-stale* *mpxt-rows-a*))
(assert-event (equal (fn-mpx-records "<a@x>" *mpxt-table-stale* *mpxt-rows-a*)
                     (list *hct-a*)))

; ---------------------------------------------------------------------------
; HYPOTHESIS-REMOVAL.

; (1) fn-mpx-table-okp dropped: <a@x>'s entries on the home page out of
; order.  tablep and faithful-from hold; table-okp fails; the conclusion
; fails (the answer is out of history order).
(defconst *mpxt-table-unordered*
  (mpxt-put *mpxt-home-a* (cons *mpxt-tag-a* 0)
            (mpxt-put *mpxt-home-a* (cons *mpxt-tag-a* 3)
                      (mpxt-build 0 (list *hct-a* *hct-b*) 2 *mpxt-empty-2*))))
; the writer above put <a@x>'s seq 0 first; the two puts add 3 then 0 again,
; so the page reads (0 3 0): not ascending.  Drop the first 0 to isolate the
; order: build <b@x> alone, then put 3 then 0.
(defconst *mpxt-table-desc*
  (mpxt-put *mpxt-home-a* (cons *mpxt-tag-a* 0)
            (mpxt-put *mpxt-home-a* (cons *mpxt-tag-a* 3)
                      (mpxt-build 0 (list *hct-retention* *hct-b*) 2 *mpxt-empty-2*))))
(assert-event (fn-mpx-tablep *mpxt-table-desc*))
(assert-event (fn-mpx-faithful-from 0 *mpxt-table-desc* *mpxt-rows*))
(assert-event (not (fn-mpx-table-okp *mpxt-table-desc* (len *mpxt-rows*))))
(assert-event (not (equal (fn-mpx-records "<a@x>" *mpxt-table-desc* *mpxt-rows*)
                          (fn-cei-article-records-for "<a@x>" *mpxt-rows*))))

; (2) fn-mpx-faithful-from dropped: <a@x>'s second entry missing.  tablep and
; table-okp hold; faithful-from fails; the conclusion fails (one record
; where the history has two).
(defconst *mpxt-table-missing*
  (mpxt-build 0 (list *hct-a* *hct-b* *hct-retention*) 2 *mpxt-empty-2*))
(assert-event (fn-mpx-tablep *mpxt-table-missing*))
(assert-event (fn-mpx-table-okp *mpxt-table-missing* (len *mpxt-rows*)))
(assert-event (not (fn-mpx-faithful-from 0 *mpxt-table-missing* *mpxt-rows*)))
(assert-event (not (equal (fn-mpx-records "<a@x>" *mpxt-table-missing* *mpxt-rows*)
                          (fn-cei-article-records-for "<a@x>" *mpxt-rows*))))
