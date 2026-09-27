; served-catalog-join-tests.lisp -- teeth for books/served-catalog-join.lisp
; (the join between the owner's view and the catalog; lane sca-join).
;
; The owner is tests/acl2/owner-cancel-refresh-tests.lisp's: T posted with a
; Cancel-Lock, then C `Control: cancel <T>' with the key that opens it; both
; through the real owner transitions (:begin, the store's prepare of the
; interned row, the I/O acknowledgements, :complete).  The arena holds the two
; payloads at handles 0 and 1 (the rows' handles).
;
;   1. REACHABLE POSITIVE WITNESS of fn-scj-joinp-of-article-finish: the
;      catalog loaded at recovery over the owner after T (E), the view after
;      C is fn-crf-apply-article of the view after T (PRF-202 on this owner),
;      the host's prepare after the seal (fn-cat-prepare-sealed) and the
;      host's finish over the refreshed view: every hypothesis holds and the
;      join holds after, with T withdrawn at the count (hidden from the
;      fresh view, kept in the pinned one).
;   2. CORRUPTED STATE: a catalog loaded under an index that hides T while
;      the owner shows it breaks fn-scj-joinp and fn-sca-join.
;   3. HYPOTHESIS REMOVAL (the pending row not withdrawn): with the pending
;      row already marked withdrawn, every other hypothesis holds and the
;      conclusion fails (the view shows C, the catalog does not).
;   4. MUTATION (fn-sca-targets-of): a withdrawal record of C behind another
;      cause's record is still a target (the head-run scan it replaced
;      answered none).

(in-package "ACL2")

(include-book "owner-cancel-refresh-tests")
(include-book "../../books/served-catalog-join")
(include-book "std/testing/must-fail" :dir :system)

(defconst *scjt-o1* *ocr-t-first*)
(defconst *scjt-o2* *ocr-after*)
(defconst *scjt-view1* (fn-own-view *scjt-o1*))
(defconst *scjt-view2* (fn-own-view *scjt-o2*))
(defconst *scjt-s2* (fn-own-store *scjt-o2*))
(defconst *scjt-a* (car (fn-state-articles (fn-node-acceptance (fn-sn-node *scjt-s2*)))))
(defconst *scjt-verdict* (cdr (car (fn-sn-verdicts *scjt-s2*))))

;; The owner: T, then C; the view after C serves C only.
(assert-event (and (equal (fn-article-msgids (fn-state-articles (fn-own-view-archive *scjt-view1*)))
                          '("<lt@example>"))
                   (equal (fn-article-msgids (fn-state-articles (fn-own-view-archive *scjt-view2*)))
                          '("<lc@example>"))
                   (equal (fn-article-msgid *scjt-a*) "<lc@example>")))

;; PRF-202 on this owner: the refreshed view IS the delta's application.
(assert-event (equal *scjt-view2* (fn-crf-apply-article *scjt-view1* *scjt-a* *scjt-verdict* *scjt-s2*)))

;; fn-scj-joinp and fn-sca-join are non-executable (defun-nx); their
;; executable bodies, equal to them by definition, over the catalog's rows
;; read one by one (fn-cat-at; the logical catalog IS its row list).
(defun scjt-rows-from (k fn-cat)
  (declare (xargs :stobjs fn-cat :verify-guards nil
                  :measure (nfix (- (fn-cat-count fn-cat) (nfix k)))))
  (if (< (nfix k) (fn-cat-count fn-cat))
      (cons (fn-cat-at (nfix k) fn-cat) (scjt-rows-from (+ 1 (nfix k)) fn-cat))
    nil))
(defthm scjt-nthcdr-of-plus-one
  (implies (natp k) (equal (nthcdr (+ 1 k) c) (cdr (nthcdr k c)))))
(defthm scjt-car-of-nthcdr
  (implies (natp k) (equal (car (nthcdr k c)) (nth k c))))
(defthm scjt-consp-of-nthcdr
  (implies (natp k) (iff (consp (nthcdr k c)) (< k (len c))))
  :hints (("Goal" :induct (nthcdr k c) :in-theory (enable nthcdr))))
(defthm scjt-nthcdr-past-len
  (implies (and (true-listp c) (natp k) (<= (len c) k))
           (equal (nthcdr k c) nil)))
(defthm scjt-rows-from-is-nthcdr
  (implies (and (natp k) (true-listp fn-cat))
           (equal (scjt-rows-from k fn-cat) (nthcdr k fn-cat)))
  :hints (("Goal" :induct (scjt-rows-from k fn-cat)
           :in-theory (e/d (scjt-rows-from) (nthcdr fn-cat-count fn-cat-at)))
          ("Subgoal *1/1" :use ((:instance car-cdr-elim (x (nthcdr k fn-cat)))))))
(defun scjt-joinp (view fn-arena fn-cat rows)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (and (equal (fn-cat-view-articles (fn-cat-count fn-cat) fn-arena fn-cat)
              (fn-state-articles (fn-own-view-archive view)))
       (fn-scj-marks-below rows (fn-cat-count fn-cat))
       (fn-scj-seqs-below rows (fn-own-view-version view))))
(defthm scjt-joinp-is-joinp
  (implies (true-listp fn-cat)
           (equal (scjt-joinp view fn-arena fn-cat (scjt-rows-from 0 fn-cat))
                  (fn-scj-joinp view fn-arena fn-cat)))
  :hints (("Goal" :in-theory '(scjt-joinp fn-scj-joinp scjt-rows-from-is-nthcdr nthcdr
                               (:executable-counterpart natp) (:executable-counterpart zp)))))
(defun scjt-sca-join (o fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (equal (fn-state-articles (fn-own-view-archive (fn-own-view o)))
         (fn-cat-view-articles (fn-scr-view-of (fn-own-view-version (fn-own-view o)) fn-cat)
                               fn-arena fn-cat)))
(defthm scjt-sca-join-is-sca-join
  (equal (scjt-sca-join o fn-arena fn-cat) (fn-sca-join o fn-arena fn-cat))
  :hints (("Goal" :in-theory '(scjt-sca-join fn-sca-join))))

;; The host's sequence: recovery's load over the owner after T (E), the seal
;; of C's payload and the prepare (T1), the finish over the refreshed view.
(defun scjt-run (index1 held-mark fn-arena fn-cat)
  (declare (xargs :mode :program :stobjs (fn-arena fn-cat)))
  (let* ((fn-arena (fn-arn-seal-many (list *ocr-t-bytes* (ocr-c-bytes *ocr-key*)) fn-arena))
         (fn-cat (fn-sca-load-held-rows (fn-sf-records (fn-sn-files (fn-own-store *scjt-o1*)))
                                        index1 fn-arena fn-cat))
         (joined-before (scjt-joinp *scjt-view1* fn-arena fn-cat (scjt-rows-from 0 fn-cat)))
         (sca-before (scjt-sca-join *scjt-o1* fn-arena fn-cat))
         (pending0 (fn-cat-prepare-sealed *ocr-rc1* *ocr-rc1* nil nil nil fn-arena fn-cat))
         (pending (if held-mark
                      (fn-pc-make (fn-pc-token pending0) (fn-pc-expected pending0)
                                  (fn-held-with-withdrawn (fn-pc-held pending0) held-mark) nil nil)
                    pending0))
         (held (fn-pc-held pending))
         (count (fn-cat-count fn-cat))
         (index2 (fn-own-view-index *scjt-view2*))
         (targets (fn-sca-targets-of (fn-record-msgid held) (fn-own-view-withdrawals *scjt-view2*)))
         (hyps (list (fn-midx-correspondencep (fn-own-view-index *scjt-view1*)
                                              (fn-state-articles (fn-own-view-archive *scjt-view1*)))
                     (consp *scjt-a*)
                     (stringp (fn-article-msgid *scjt-a*))
                     (no-duplicatesp-equal
                      (fn-article-msgids (cons *scjt-a* (fn-state-articles (fn-own-view-archive *scjt-view1*)))))
                     (fn-midx-string-article-listp (fn-state-articles (fn-own-view-archive *scjt-view1*)))
                     (fn-midx-string-article-listp (fn-state-articles (fn-own-view-archive *scjt-view2*)))
                     (fn-pc-p pending)
                     (equal (fn-pc-expected pending) count)
                     (null (fn-held-withdrawn held))
                     (equal (fn-record-msgid held) (fn-article-msgid *scjt-a*))
                     (<= (nfix (fn-own-view-version *scjt-view1*)) (nfix (fn-own-view-version *scjt-view2*)))
                     (< (nfix (fn-record-sequence held)) (nfix (fn-own-view-version *scjt-view2*)))))
         (row-eq (with-local-stobj fn-cat
                   (mv-let (r fn-cat)
                     (let ((fn-cat (fn-sca-load-held-rows (fn-sf-records (fn-sn-files (fn-own-store *scjt-o1*)))
                                                          index1 fn-arena fn-cat)))
                       (let ((fn-cat (fn-cat-commit held fn-cat)))
                         (mv (equal (fn-cat-row-article count fn-arena fn-cat) *scjt-a*) fn-cat)))
                     r))))
    (mv-let (word pending2 fn-cat)
      (fn-sca-finish (fn-pc-token pending) pending index2 targets fn-cat)
      (declare (ignore pending2))
      (mv (list joined-before sca-before hyps row-eq (car word) targets
                (scjt-joinp *scjt-view2* fn-arena fn-cat (scjt-rows-from 0 fn-cat))
                (scjt-sca-join *scjt-o2* fn-arena fn-cat)
                (fn-article-msgids (fn-cat-view-articles (fn-cat-count fn-cat) fn-arena fn-cat))
                (fn-article-msgids (fn-cat-view-articles count fn-arena fn-cat)))
          fn-arena fn-cat))))

(defun scjt-exec (index1 held-mark)
  (declare (xargs :mode :program))
  (with-local-stobj fn-arena
    (mv-let (result fn-arena)
      (with-local-stobj fn-cat
        (mv-let (result fn-arena fn-cat)
          (scjt-run index1 held-mark fn-arena fn-cat)
          (mv result fn-arena)))
      result)))

;; 1. The reachable witness: joined before; every hypothesis; the row
;; equation; an :article delta; the target T; joined after (the invariant
;; and the chain's fn-sca-join); the fresh view is C, the pinned one T.
(defconst *scjt-1* (scjt-exec (fn-own-view-index *scjt-view1*) nil))
(assert-event (equal (nth 0 *scjt-1*) t))
(assert-event (equal (nth 1 *scjt-1*) t))
(assert-event (equal (nth 2 *scjt-1*) '(t t t t t t t t t t t t)))
(assert-event (equal (nth 3 *scjt-1*) t))
(assert-event (equal (nth 4 *scjt-1*) :article))
(assert-event (equal (nth 5 *scjt-1*) '("<lt@example>")))
(assert-event (equal (nth 6 *scjt-1*) t))
(assert-event (equal (nth 7 *scjt-1*) t))
(assert-event (equal (nth 8 *scjt-1*) '("<lc@example>")))
(assert-event (equal (nth 9 *scjt-1*) '("<lt@example>")))

;; 2. Corrupted state: recovery's load under an index that shows nothing
;; (the catalog hides T, the owner shows it): not joined, and the chain's
;; hypothesis fails.
(defconst *scjt-2* (scjt-exec (fn-midx-build nil) nil))
(assert-event (equal (nth 0 *scjt-2*) nil))
(assert-event (equal (nth 1 *scjt-2*) nil))

;; 3. Hypothesis removal (null (fn-held-withdrawn held)): the pending row
;; marked withdrawn; every other hypothesis holds (and the join before and
;; the row equation's projections other than the mark), the conclusion fails.
(defconst *scjt-3* (scjt-exec (fn-own-view-index *scjt-view1*) '(0 . 0)))
(assert-event (equal (nth 0 *scjt-3*) t))
(assert-event (equal (nth 2 *scjt-3*) '(t t t t t t t t nil t t t)))
(assert-event (equal (nth 3 *scjt-3*) t))
(assert-event (equal (nth 6 *scjt-3*) nil))
(assert-event (equal (nth 8 *scjt-3*) nil))

;; 4. The targets of C behind another cause's record.
(defconst *scjt-ws* (fn-own-view-withdrawals *scjt-view2*))
(defconst *scjt-other* (list :withdrawal "<x@example>" "<other@example>" :node nil nil nil))
(defun scjt-head-run (cause ws)
  (if (and (consp ws) (fn-ctl-withdrawalp (car ws)) (equal (fn-ctl-w-cause (car ws)) cause))
      (cons (fn-ctl-w-target (car ws)) (scjt-head-run cause (cdr ws)))
    nil))
(assert-event (fn-ctl-withdrawalp *scjt-other*))
(assert-event (equal (fn-sca-targets-of "<lc@example>" (cons *scjt-other* *scjt-ws*)) '("<lt@example>")))
(assert-event (equal (scjt-head-run "<lc@example>" (cons *scjt-other* *scjt-ws*)) nil))
