; served-catalog-join.lisp -- the JOIN between the owner's view and the
; catalog (lane sca-join, 2026-09-27; the R3 of catalog-slice,
; planning/evidence/catalog-slice-2026-09-26.md; the open hypothesis
; fn-sca-join of books/served-catalog-owner.lisp).
;
; The join: the catalog's view at the version the owner's view carries is the
; owner's visible archive, article for article.  It is carried as the
; invariant fn-scj-joinp (the view at the catalog's count is the visible
; list; every withdrawal mark is below the count; every row's sequence is
; below the view's version), which gives fn-sca-join
; (fn-scj-joinp-gives-sca-join) and which the host's article finish
; preserves:
;
;   fn-scj-join-of-finish-lists (KEYSTONE, list level; books/served-catalog-
;     join-step.lisp): the catalog after
;     the host's T4-then-T2 (fn-sca-finish, with the refreshed view's index
;     and fn-sca-targets-of the completed Message-ID over the refreshed
;     withdrawals) shows at the new count exactly the list the refresh's
;     one-article step makes (fn-ctl-visible-add): the articles the cancel
;     drops are the rows T4 withdraws (fn-scj-view-below-after-withdraw-
;     targets, fn-scj-drop-via-is-keep), and the completed row is visible
;     exactly when the refresh keeps the article (fn-scj-visible-add-shows-a);
;   fn-scj-joinp-of-article-finish (KEYSTONE, over the owner's view): the
;     same over fn-crf-apply-article, which IS the view fn-own-refresh
;     computes after an article completion (books/catalog-refresh.lisp
;     fn-view-apply-is-refresh, PRF-202).
;
; Hypotheses the finish keeps, and where each comes from: the old and new
; visible lists hold string Message-IDs (fn-article-listp of the acceptance);
; the completed article's Message-ID is new and the old visible Message-IDs
; are distinct (the acceptance's fn-articles-freshp; the visible list is a
; subsequence of the raw one); the pending row is the completed article's
; row (fn-cat-prepare-sealed: the store's row); THE ROW EQUATION -- the
; catalog's committed row, read as an article (fn-cat-row-article), is the
; article the acceptance installed, numbers included -- is a hypothesis of
; this book's keystones: it is the numbering half of step 8's R (catalog
; numbers are one past each group's high over the rows; the acceptance's
; are its watermarks), stated and left OPEN here.
;
; The identity finish (catalog-columns' missing equation): the owner the
; host installs at an identity completion, fn-rix-ocfg-complete, IS the
; article finish's owner fn-ocfg-with-owner of fn-ccar-own-finish when no
; configuration record is staged and the store's event index is carried
; (fn-scj-identity-finish-owner-is-article-finish-owner), so the T2
; keystone fn-sca-ocl-relation-of-finish holds at fn-owner-finish-identity
; (fn-scj-ocl-relation-of-identity-finish).
;
; Teeth: tests/acl2/served-catalog-join-tests.lisp.

(in-package "ACL2")

(include-book "served-catalog-join-step")
(include-book "owner-refresh-indexed")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:rewrite fn-col-poll-nth-past-end-is-nil))))

; The rules below never reason about a Message-ID's syntax.
(local (in-theory (disable fn-nntp-article-idp-is-consp fn-scat-article-idp-is-msgid-idp
                           fn-scat-msgid-idp fn-nntp-index-msgid-okp-stringp
                           fn-nntp-index-msgid-okp fn-cp-id-length-bound)))

; -----------------------------------------------------------------------------
; The version a pin names: every row's sequence below the view's version, so
; the bisection fn-scr-view-of names every row.

(defun fn-scj-seqs-below (c version)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp c)
      (and (< (nfix (fn-record-sequence (car c))) (nfix version))
           (fn-scj-seqs-below (cdr c) version))
    t))

(defthm fn-scj-seqs-below-nth
  (implies (and (fn-scj-seqs-below c version) (natp k) (< k (len c)))
           (< (nfix (fn-record-sequence (nth k c))) (nfix version)))
  :rule-classes (:rewrite :linear))

(defthm fn-scj-seq-bound-when-seqs-below
  (implies (and (fn-scj-seqs-below fn-cat version) (natp version)
                (natp lo) (natp hi) (<= lo hi) (<= hi (len fn-cat)))
           (equal (fn-scr-seq-bound lo hi version fn-cat) hi))
  :hints (("Goal" :induct (fn-scr-seq-bound lo hi version fn-cat)
           :in-theory (enable fn-scr-seq-bound))
          ("Subgoal *1/3" :use ((:instance fn-scj-seqs-below-nth (c fn-cat) (k (fn-scr-mid lo hi)))
                                (:instance fn-scr-mid-bounds)))
          ("Subgoal *1/2" :use ((:instance fn-scj-seqs-below-nth (c fn-cat) (k (fn-scr-mid lo hi)))
                                (:instance fn-scr-mid-bounds)))))

(defthm fn-scj-view-of-when-seqs-below
  (implies (fn-scj-seqs-below fn-cat version)
           (equal (fn-scr-view-of version fn-cat) (len fn-cat)))
  :hints (("Goal" :in-theory (enable fn-scr-view-of)
           :use ((:instance fn-scj-seq-bound-when-seqs-below (version (nfix version))
                            (lo 0) (hi (len fn-cat)))))))

(defthm fn-scj-seqs-below-monotone
  (implies (and (fn-scj-seqs-below c v1) (<= (nfix v1) (nfix v2)))
           (fn-scj-seqs-below c v2)))

(defthm fn-scj-seqs-below-of-mark
  (implies (and (fn-scj-seqs-below c version) (natp target))
           (fn-scj-seqs-below (fn-cat-mark-withdrawn target v by c) version))
  :hints (("Goal" :in-theory (enable fn-cat-mark-withdrawn update-nth))))

(defthm fn-scj-seqs-below-of-withdraw-targets
  (implies (fn-scj-seqs-below c version)
           (fn-scj-seqs-below (fn-sca-withdraw-targets targets index by c) version))
  :hints (("Goal" :induct (fn-sca-withdraw-targets targets index by c)
           :in-theory (e/d (fn-sca-withdraw-targets) (fn-cat-view-last-visible)))))

(defthm fn-scj-sequence-of-assign
  (equal (fn-record-sequence (fn-cat-assign h c)) (fn-record-sequence h))
  :hints (("Goal" :in-theory (enable fn-cat-assign fn-held-with-numbers fn-record-internals
                                     fn-held-internals))))

(defthm fn-scj-seqs-below-of-append
  (equal (fn-scj-seqs-below (append a b) version)
         (and (fn-scj-seqs-below a version) (fn-scj-seqs-below b version))))

(defthm fn-scj-seqs-below-of-commit
  (implies (and (fn-scj-seqs-below c version)
                (< (nfix (fn-record-sequence h)) (nfix version)))
           (fn-scj-seqs-below (fn-cat-commit h c) version))
  :hints (("Goal" :in-theory (enable fn-cat-commit-is-append)
           :expand ((fn-scj-seqs-below (list (fn-cat-assign h c)) version)
                    (fn-scj-seqs-below nil version)))))

(in-theory (disable fn-scj-seqs-below))

; -----------------------------------------------------------------------------
; THE INVARIANT.  The catalog's view at its count is the owner's visible
; archive; every withdrawal mark is below the count; every row's sequence is
; below the view's version.

(defun-nx fn-scj-joinp (view fn-arena fn-cat)
  (and (equal (fn-cat-view-articles (fn-cat-count fn-cat) fn-arena fn-cat)
              (fn-state-articles (fn-own-view-archive view)))
       (fn-scj-marks-below fn-cat (fn-cat-count fn-cat))
       (fn-scj-seqs-below fn-cat (fn-own-view-version view))))

; It is the join the served chain carries (fn-scr-catalogp's first conjunct
; at the owner's view).
(defthm fn-scj-joinp-gives-sca-join
  (implies (fn-scj-joinp (fn-own-view o) fn-arena fn-cat)
           (fn-sca-join o fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-sca-join fn-scj-joinp fn-cat-view-articles)
                                  (fn-cat-view-below fn-scr-view-of)))))

(defthm fn-scj-number-in-of-with-withdrawn
  (equal (fn-held-number-in g (fn-held-with-withdrawn h w)) (fn-held-number-in g h))
  :hints (("Goal" :in-theory (enable fn-held-number-in))))

(defthm fn-scj-group-high-of-mark
  (implies (natp target)
           (equal (fn-cat-group-high g (fn-cat-mark-withdrawn target v by c))
                  (fn-cat-group-high g c)))
  :hints (("Goal" :in-theory (enable fn-cat-mark-withdrawn))))

(defthm fn-scj-group-high-of-withdraw-targets
  (equal (fn-cat-group-high g (fn-sca-withdraw-targets targets index by c))
         (fn-cat-group-high g c))
  :hints (("Goal" :induct (fn-sca-withdraw-targets targets index by c)
           :in-theory (e/d (fn-sca-withdraw-targets) (fn-cat-view-last-visible fn-cat-group-high)))))

(defthm fn-scj-assign-numbers-of-withdraw-targets
  (equal (fn-cat-assign-numbers groups (fn-sca-withdraw-targets targets index by c))
         (fn-cat-assign-numbers groups c))
  :hints (("Goal" :induct (fn-cat-assign-numbers groups c)
           :in-theory (disable fn-sca-withdraw-targets))))

(defthm fn-scj-assign-of-withdraw-targets
  (equal (fn-cat-assign h (fn-sca-withdraw-targets targets index by c))
         (fn-cat-assign h c))
  :hints (("Goal" :in-theory (e/d (fn-cat-assign) (fn-sca-withdraw-targets)))))

; The committed row as an article reads only the new row.
(defthm fn-scj-row-article-at-count-of-commit
  (equal (fn-cat-row-article (len c) fn-arena (fn-cat-commit h c))
         (fn-make-article (fn-record-msgid (fn-cat-assign h c))
                          (fn-record-payload (fn-cat-assign h c))
                          (fn-record-groups (fn-cat-assign h c))
                          (fn-held-numbers (fn-cat-assign h c))
                          t
                          (fn-record-stamp (fn-cat-assign h c))))
  :hints (("Goal" :in-theory (e/d (fn-cat-row-article) (fn-cat-commit-is-append)))))

(defthm fn-scj-row-article-of-commit-after-withdraw-targets
  (equal (fn-cat-row-article (len c) fn-arena
                             (fn-cat-commit h (fn-sca-withdraw-targets targets index by c)))
         (fn-cat-row-article (len c) fn-arena (fn-cat-commit h c)))
  :hints (("Goal" :in-theory (disable fn-sca-withdraw-targets fn-cat-assign)
           :use ((:instance fn-scj-row-article-at-count-of-commit
                            (c (fn-sca-withdraw-targets targets index by c)))
                 (:instance fn-scj-row-article-at-count-of-commit)))))

; -----------------------------------------------------------------------------
; The owner's side of the host's finish.

(defthm fn-scj-articles-of-visible-state-of
  (equal (fn-state-articles (fn-ctl-visible-state-of acc visible)) visible)
  :hints (("Goal" :in-theory (enable fn-ctl-visible-state-of))))

; The view the refresh computes after an article completion
; (fn-crf-apply-article, = fn-own-refresh by PRF-202's
; fn-view-apply-is-refresh), read at the four projections the join names.
(defthm fn-scj-apply-article-projections
  (let ((view2 (fn-crf-apply-article view a verdict s)))
    (and (equal (fn-state-articles (fn-own-view-archive view2))
                (fn-ctl-visible-add a (fn-state-articles (fn-own-view-archive view))
                                    (fn-own-view-raw view)
                                    (fn-own-view-withdrawals view2)
                                    (fn-own-view-verdicts view2)))
         (equal (fn-own-view-index view2)
                (fn-midx-refresh (fn-own-view-index view)
                                 (fn-state-articles (fn-own-view-archive view))
                                 (fn-state-articles (fn-own-view-archive view2))))
         (equal (fn-own-view-version view2) (len (fn-sf-records (fn-sn-files s))))))
  :hints (("Goal" :in-theory (e/d (fn-crf-apply-article fn-own-view-fields-of-make-visible)
                                  (fn-ctl-visible-add fn-midx-refresh fn-ctl-article-withdrawals
                                   fn-ctl-prepend fn-ctl-resolve-tlocks fn-ctl-subseq-diff
                                   fn-gidx-refresh fn-ctl-visible-state-of fn-own-view-make-visible)))))

(defthm fn-scj-seqs-below-of-finish
  (implies (and (fn-scj-seqs-below fn-cat version)
                (fn-pc-p pending)
                (< (nfix (fn-record-sequence (fn-pc-held pending))) (nfix version)))
           (fn-scj-seqs-below (mv-nth 2 (fn-sca-finish token pending index targets fn-cat)) version))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-sca-finish fn-sca-complete fn-cat-complete fn-cat-complete-hidden)
                           (fn-sca-withdraw-targets fn-cat-commit-is-append fn-midx-lookup)))))

; KEYSTONE (the join at the host's article finish).  The owner's view after
; the completion (the refresh, fn-crf-apply-article) and the catalog after
; the host's fn-sca-finish -- over that view's index and the targets of the
; completed Message-ID in that view's withdrawals, as
; host/owner-host.lisp fn-owner-finish-submission and
; fn-owner-finish-identity pass them -- are joined again.  The row equation
; (the committed row read as an article is A) is the open numbering half.
(defthm fn-scj-joinp-of-article-finish
  (let* ((view2 (fn-crf-apply-article view a verdict s))
         (held (fn-pc-held pending))
         (c2 (mv-nth 2 (fn-sca-finish token pending (fn-own-view-index view2)
                                      (fn-sca-targets-of (fn-record-msgid held)
                                                         (fn-own-view-withdrawals view2))
                                      fn-cat))))
    (implies (and (fn-scj-joinp view fn-arena fn-cat)
                  (fn-midx-correspondencep (fn-own-view-index view)
                                           (fn-state-articles (fn-own-view-archive view)))
                  (consp a)
                  (stringp (fn-article-msgid a))
                  (no-duplicatesp-equal
                   (fn-article-msgids (cons a (fn-state-articles (fn-own-view-archive view)))))
                  (fn-midx-string-article-listp (fn-state-articles (fn-own-view-archive view)))
                  (fn-midx-string-article-listp (fn-state-articles (fn-own-view-archive view2)))
                  (fn-pc-p pending)
                  (equal token (fn-pc-token pending))
                  (equal (fn-pc-expected pending) (fn-cat-count fn-cat))
                  (null (fn-held-withdrawn held))
                  (equal (fn-record-msgid held) (fn-article-msgid a))
                  (equal (fn-cat-row-article (fn-cat-count fn-cat) fn-arena
                                             (fn-cat-commit held fn-cat))
                         a)
                  (<= (nfix (fn-own-view-version view)) (nfix (fn-own-view-version view2)))
                  (< (nfix (fn-record-sequence held)) (nfix (fn-own-view-version view2))))
             (fn-scj-joinp view2 fn-arena c2)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-scj-joinp fn-cat-view-articles fn-cat-count-is-len fn-midx-correspondencep
                         fn-scj-row-article-of-commit-after-withdraw-targets)
                       (theory 'minimal-theory))
           :use ((:instance fn-scj-apply-article-projections)
                 (:instance fn-midx-refresh-preserves-correspondence
                            (index (fn-own-view-index view))
                            (old-articles (fn-state-articles (fn-own-view-archive view)))
                            (new-articles (fn-state-articles
                                           (fn-own-view-archive (fn-crf-apply-article view a verdict s)))))
                 (:instance fn-scj-join-of-finish-lists
                            (old (fn-own-view-raw view))
                            (ws (fn-own-view-withdrawals (fn-crf-apply-article view a verdict s)))
                            (verdicts (fn-own-view-verdicts (fn-crf-apply-article view a verdict s))))
                 (:instance fn-scj-seqs-below-monotone
                            (c fn-cat)
                            (v1 (fn-own-view-version view))
                            (v2 (fn-own-view-version (fn-crf-apply-article view a verdict s))))
                 (:instance fn-scj-seqs-below-of-finish
                            (index (fn-own-view-index (fn-crf-apply-article view a verdict s)))
                            (targets (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                        (fn-own-view-withdrawals
                                                         (fn-crf-apply-article view a verdict s))))
                            (version (fn-own-view-version (fn-crf-apply-article view a verdict s))))))))

; -----------------------------------------------------------------------------
; The identity finish (catalog-columns' missing equation).  The host's
; fn-owner-finish-identity installs fn-rix-ocfg-complete (through
; fn-owner-finish) and then runs fn-sca-finish exactly as the article finish
; does.  With no configuration record staged and the store's event index
; carried (fn-ceis-indexedp: fn-osi-live-owner-store-is-indexed), that owner
; IS the article finish's, so T2's keystone applies there unchanged.

(defthm fn-scj-identity-finish-owner-is-article-finish-owner
  (implies (and (fn-hist-of-storep fn-hist (fn-own-store (fn-ocfg-owner oc)))
                (not (fn-ocfg-staged oc))
                (fn-sn-completion-enabledp (fn-own-store (fn-ocfg-owner oc))))
           (equal (fn-rix-ocfg-complete oc fn-hist)
                  (fn-ocfg-with-owner oc (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena)))))
  :hints (("Goal" :in-theory '(fn-rix-ocfg-complete-is-ccar-ocfg-complete fn-ccar-ocfg-complete
                               fn-ccar-own-finish fn-ccar-own-complete fn-ocfg-with-owner
                               fn-ccar-completion-enabledp-is-reference car-cons cdr-cons)))
  :rule-classes nil)
; KEYSTONE (T2 at the identity finish).  fn-sca-ocl-relation-of-finish at the
; owner fn-owner-finish-identity installs.
(defthm fn-scj-ocl-relation-of-identity-finish
  (let* ((s (fn-own-store (fn-ocfg-owner oc)))
         (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files s)))) (fn-pc-expected pending)))
         (w (fn-held-wire-of (fn-pc-held pending) fn-arena)))
    (implies (and (fn-ocl-relation oc)
                  (fn-hist-of-storep fn-hist s)
                  (not (fn-ocfg-staged oc))
                  (fn-cat-history-relation records0 fn-arena fn-cat)
                  (fn-sn-completion-enabledp s)
                  (equal (fn-sf-article-records
                          (fn-cat-history-articles (fn-sf-records (fn-sn-files s)) fn-arena))
                         (append (fn-sf-article-records records0) (list w)))
                  (fn-pc-p pending)
                  (equal token (fn-pc-token pending))
                  (equal (fn-pc-expected pending) (fn-cat-count fn-cat))
                  (< (fn-record-payload (fn-pc-held pending)) (fn-arena-count fn-arena))
                  (fn-record-p w))
             (fn-cat-ocl-relation
              (fn-rix-ocfg-complete oc fn-hist)
              fn-arena
              (mv-nth 2 (fn-sca-finish token pending view-index targets fn-cat)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance fn-sca-ocl-relation-of-finish (cfg (fn-ocfg-config oc)))
                 (:instance fn-scj-identity-finish-owner-is-article-finish-owner
                            (cfg (fn-ocfg-config oc)))))))
