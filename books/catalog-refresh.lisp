; fn: the committed delta equals the refresh (PRF-202; wave 5, lane
; catalog-boundary-owner, 2026-09-26; gpt-6's consolidation review section 2
; "the system keeps asking history what just happened" and wave-5 review
; section 5; D33; the consolidation design 1.4).
;
; TODAY the owner's refresh (books/owner.lisp fn-own-refresh, reached by every
; host step through fn-own-store-step and fn-own-complete) REDISCOVERS what
; the commit did: fn-ctl-refresh-withdrawals and fn-ctl-refresh-visible
; compare the acceptance's article list with the one the view carried
; (`(equal new old)', `(equal (cdr new) old)'), fn-ctl-verdicts-grow-by-p
; compares the verdict lists, fn-midx-refresh, fn-gidx-refresh and
; fn-ctl-refresh-withdrawn compare the visible lists, and each takes its
; incremental arm only when the comparison happens to find the one-article
; shape.  The commit KNOWS that shape: the finish installed one article A
; with one verdict.  This book states the view's incremental application of
; that delta, fn-crf-apply-article, and proves it equal to the refresh on
; every projection the view exposes (version, frontier, archive, verdicts,
; the Message-ID trie, the group buckets, the withdrawal records, the raw
; list, the withdrawn list, the keyring view):
;
;   fn-view-apply-is-refresh (KEYSTONE, PRF-202): for an owner O and the
;   store S its finish produced, idle, whose acceptance's articles are A
;   consed onto the view's raw list and whose verdicts are A's verdict consed
;   onto the view's, the view fn-own-refresh computes over S is
;   fn-crf-apply-article of the old view, A, the verdict and S's scalars.
;   No hypothesis compares two lists; the two hypotheses on S are what the
;   finish on the article arm establishes (fn-sn-finish: fn-node-complete
;   :durable is fn-install-pending, which conses fn-article-from-pending
;   onto the articles; fn-sn-update-accepted conses the verdict pair).
;
; The apply reads the delta and the old view.  Its remaining list tests are
; on the VISIBLE lists (the cancel's effect: whether A is visible and whether
; A withdrew anything), the same tests the refresh functions make there;
; the whole-archive comparisons are gone.  Where A is a plain visible
; article (no cancel, not withdrawn) the apply is the pure cons/extend/put
; case, stated as fn-crf-apply-article-plain.
;
; ON THE CATALOG the same equations are the versioned view's
; (books/catalog-view.lisp fn-cat-view-articles): a commit leaves every
; version at or below the old count unchanged (C3: a pinned reader's view
; does not move) and the view at the new count is the committed row's
; article on top of the old view (fn-cat-view-articles-of-commit-advanced:
; the :article delta PRF-203's fn-cat-complete emits is what the consumer
; conses); a withdrawal at version W leaves every version at or below W
; unchanged and removes the target from every later version
; (fn-cat-view-below-of-withdraw-advanced: the :withdraw delta).  The
; equation between the catalog's row article and the acceptance's A
; (numbers = the allocated memberships) is step 8's R-side obligation
; (PKT-585) and is NOT claimed here; this book proves both sides' delta
; equations, and names the join.
;
; ORDER for a cancel (gpt-6's publication-order case): the refresh drops the
; target in the SAME view that first shows the cancel (fn-ctl-visible-add:
; kept = drop-via when A causes a withdrawal).  On the catalog that is
; fn-cat-withdraw target BEFORE fn-cat-complete of the cancel row, so the
; withdrawal's version is the count before the cancel (fn-cat-withdraw-then-
; commit-view): the version that sees the cancel does not see the target.

(in-package "ACL2")
(include-book "catalog-view")

; -----------------------------------------------------------------------------
; The catalog: rows below the count, and their visibility, after a commit.

(defthm fn-cat-visible-at-by-row
  (equal (fn-cat-visible-at seq v fn-cat)
         (and (< seq v)
              (let ((w (fn-held-withdrawn (fn-cat-at seq fn-cat))))
                (or (null w) (<= v (car w))))))
  :hints (("Goal" :in-theory (enable fn-cat-visiblep))))

(in-theory (disable fn-cat-visible-at-by-row))

(local (defthm fn-crf-withdrawn-of-with-numbers
   (equal (fn-held-withdrawn (fn-held-with-numbers h numbers)) (fn-held-withdrawn h))
   :hints (("Goal" :in-theory (enable fn-held-with-numbers fn-record-internals fn-held-internals)))))

(local (defthm fn-crf-withdrawn-of-assign
   (equal (fn-held-withdrawn (fn-cat-assign h c)) (fn-held-withdrawn h))
   :hints (("Goal" :in-theory (enable fn-cat-assign)))))

(defthm fn-cat-view-below-of-commit
  (implies (and (natp i) (<= i (fn-cat-count fn-cat)))
           (equal (fn-cat-view-below i v fn-arena (fn-cat-commit h fn-cat))
                  (fn-cat-view-below i v fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-cat-view-below i v fn-arena fn-cat)
           :in-theory (e/d (fn-cat-view-below fn-cat-row-article fn-cat-visible-at-by-row
                            fn-cat-commit-keeps-rows)
                           (fn-cat-at-is-nth fn-cat-count-is-len fn-cat-commit-is-append
                            fn-cat-p-is-rowsp fn-cat-visible-at-is-visiblep
                            fn-cat-visible-at)))))

; C3: a version at or below the old count sees no change from the commit.
(defthm fn-cat-view-articles-of-commit-pinned
  (implies (and (natp v) (<= v (fn-cat-count fn-cat)))
           (equal (fn-cat-view-articles v fn-arena (fn-cat-commit h fn-cat))
                  (fn-cat-view-articles v fn-arena fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-cat-view-articles fn-cat-visible-at-by-row)
                                  (fn-cat-at-is-nth fn-cat-count-is-len fn-cat-commit-is-append
                                   fn-cat-p-is-rowsp fn-cat-visible-at-is-visiblep
                                   fn-cat-visible-at fn-cat-view-below fn-cat-row-article))
           :expand ((fn-cat-view-below (+ 1 (fn-cat-count fn-cat)) v fn-arena (fn-cat-commit h fn-cat)))
           :use ((:instance fn-cat-view-below-of-commit (i (fn-cat-count fn-cat)))))))

; The :article delta: the view at the new count is the committed row's
; article on top of the OLD rows AS SEEN AT THE NEW VERSION.  (Not the view
; at the old count: a row withdrawn at exactly the old count is visible at
; the old version and leaves at the new one, which is what a cancel
; committed in the same transaction does: fn-cat-withdraw-then-commit-view.)
(defthm fn-cat-view-articles-of-commit-advanced
  (implies (null (fn-held-withdrawn h))
           (equal (fn-cat-view-articles (+ 1 (fn-cat-count fn-cat)) fn-arena (fn-cat-commit h fn-cat))
                  (cons (fn-cat-row-article (fn-cat-count fn-cat) fn-arena (fn-cat-commit h fn-cat))
                        (fn-cat-view-below (fn-cat-count fn-cat) (+ 1 (fn-cat-count fn-cat))
                                           fn-arena fn-cat))))
  :hints (("Goal" :in-theory (e/d (fn-cat-view-articles fn-cat-visible-at-by-row
                                   fn-cat-commit-new-row)
                                  (fn-cat-at-is-nth fn-cat-count-is-len fn-cat-commit-is-append
                                   fn-cat-p-is-rowsp fn-cat-visible-at-is-visiblep
                                   fn-cat-visible-at fn-cat-view-below fn-cat-row-article))
           :expand ((fn-cat-view-below (+ 1 (fn-cat-count fn-cat)) (+ 1 (fn-cat-count fn-cat))
                                       fn-arena (fn-cat-commit h fn-cat)))
           :use ((:instance fn-cat-view-below-of-commit (i (fn-cat-count fn-cat))
                            (v (+ 1 (fn-cat-count fn-cat))))))))

; NOT claimed (withdrawn in this lane's budget): the version-step corollary
; that, when no row below I was withdrawn at exactly version W, the rows
; below I look the same at W and W + 1 (so the plain :article delta is the
; cons onto the old view itself); it needs the rows' withdrawn cells typed
; (fn-cat-p), and the honest statement above does not need it.

; -----------------------------------------------------------------------------
; The catalog: a withdrawal at version W (the count).

(local (defthm fn-crf-row-fields-of-with-withdrawn
   (and (equal (fn-record-msgid (fn-held-with-withdrawn h w)) (fn-record-msgid h))
        (equal (fn-record-payload (fn-held-with-withdrawn h w)) (fn-record-payload h))
        (equal (fn-record-groups (fn-held-with-withdrawn h w)) (fn-record-groups h))
        (equal (fn-held-numbers (fn-held-with-withdrawn h w)) (fn-held-numbers h))
        (equal (fn-record-stamp (fn-held-with-withdrawn h w)) (fn-record-stamp h))
        (equal (fn-held-withdrawn (fn-held-with-withdrawn h w)) w))
   :hints (("Goal" :in-theory (enable fn-held-with-withdrawn fn-record-internals fn-held-internals)))))

(local (defthm fn-crf-row-article-of-withdraw
   (implies (and (natp target) (< target (fn-cat-count fn-cat)) (natp k))
            (equal (fn-cat-row-article k fn-arena (fn-cat-withdraw target by fn-cat))
                   (fn-cat-row-article k fn-arena fn-cat)))
   :hints (("Goal" :in-theory (e/d (fn-cat-row-article fn-cat-mark-withdrawn)
                                   (fn-cat-p-is-rowsp))))))

(local (defthm fn-crf-count-of-withdraw
   (implies (and (natp target) (< target (fn-cat-count fn-cat)))
            (equal (fn-cat-count (fn-cat-withdraw target by fn-cat)) (fn-cat-count fn-cat)))
   :hints (("Goal" :in-theory (enable fn-cat-mark-withdrawn)))))

; What the withdrawal does to one row's withdrawn cell.
(local (defthm fn-crf-withdrawn-of-at-withdraw
   (implies (and (natp target) (< target (fn-cat-count fn-cat)) (natp k))
            (equal (fn-held-withdrawn (fn-cat-at k (fn-cat-withdraw target by fn-cat)))
                   (if (and (equal k target) (null (fn-held-withdrawn (fn-cat-at target fn-cat))))
                       (cons (fn-cat-count fn-cat) by)
                     (fn-held-withdrawn (fn-cat-at k fn-cat)))))
   :hints (("Goal" :in-theory (e/d (fn-cat-mark-withdrawn) (fn-cat-p-is-rowsp))))))

; A version at or below the withdrawal's version sees no change.
(defthm fn-cat-view-below-of-withdraw-pinned
  (implies (and (natp i) (<= i (fn-cat-count fn-cat))
                (natp v) (<= v (fn-cat-count fn-cat))
                (natp target) (< target (fn-cat-count fn-cat)))
           (equal (fn-cat-view-below i v fn-arena (fn-cat-withdraw target by fn-cat))
                  (fn-cat-view-below i v fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-cat-view-below i v fn-arena fn-cat)
           :in-theory (e/d (fn-cat-view-below fn-cat-visible-at-by-row)
                           (fn-cat-at-is-nth fn-cat-count-is-len fn-cat-withdraw-is-mark
                            fn-cat-p-is-rowsp fn-cat-visible-at-is-visiblep
                            fn-cat-visible-at fn-cat-row-article)))))

(defthm fn-cat-view-articles-of-withdraw-pinned
  (implies (and (natp v) (<= v (fn-cat-count fn-cat))
                (natp target) (< target (fn-cat-count fn-cat)))
           (equal (fn-cat-view-articles v fn-arena (fn-cat-withdraw target by fn-cat))
                  (fn-cat-view-articles v fn-arena fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-cat-view-articles)
                                  (fn-cat-at-is-nth fn-cat-count-is-len fn-cat-withdraw-is-mark
                                   fn-cat-p-is-rowsp fn-cat-view-below)))))

; The rows below I visible at V, newest first, except TARGET: what a
; :withdraw delta's consumer keeps.
(defun fn-cat-view-below-except (target i v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp i) (natp v) (<= i (fn-cat-count fn-cat))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :guard-hints (("Goal" :in-theory (disable fn-cat-p-is-rowsp fn-cat-count-is-len
                                                            fn-cat-at-is-nth)))))
  (if (zp i)
      nil
    (let ((seq (- i 1)))
      (if (and (not (equal seq target)) (fn-cat-visible-at seq v fn-cat))
          (cons (fn-cat-row-article seq fn-arena fn-cat)
                (fn-cat-view-below-except target seq v fn-arena fn-cat))
        (fn-cat-view-below-except target seq v fn-arena fn-cat)))))

; The :withdraw delta: every version past the withdrawal's sees the view
; without the target.
(defthm fn-cat-view-below-of-withdraw-advanced
  (implies (and (natp i) (<= i (fn-cat-count fn-cat))
                (natp v) (< (fn-cat-count fn-cat) v)
                (natp target) (< target (fn-cat-count fn-cat))
                (null (fn-held-withdrawn (fn-cat-at target fn-cat))))
           (equal (fn-cat-view-below i v fn-arena (fn-cat-withdraw target by fn-cat))
                  (fn-cat-view-below-except target i v fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-cat-view-below i v fn-arena fn-cat)
           :in-theory (e/d (fn-cat-view-below fn-cat-view-below-except fn-cat-visible-at-by-row)
                           (fn-cat-at-is-nth fn-cat-count-is-len fn-cat-withdraw-is-mark
                            fn-cat-p-is-rowsp fn-cat-visible-at-is-visiblep
                            fn-cat-visible-at fn-cat-row-article)))))

; The cancel's composed transaction, in the order that reproduces the
; refresh: withdraw the target (at version COUNT), then commit the cancel
; row.  The version that first sees the cancel (COUNT + 1) does not see the
; target; the version before it (COUNT) sees neither change.
(defthm fn-cat-withdraw-then-commit-view
  (implies (and (natp target) (< target (fn-cat-count fn-cat))
                (null (fn-held-withdrawn (fn-cat-at target fn-cat)))
                (null (fn-held-withdrawn h)))
           (let ((c2 (fn-cat-commit h (fn-cat-withdraw target by fn-cat))))
             (and (equal (fn-cat-view-articles (fn-cat-count fn-cat) fn-arena c2)
                         (fn-cat-view-articles (fn-cat-count fn-cat) fn-arena fn-cat))
                  (equal (fn-cat-view-articles (+ 1 (fn-cat-count fn-cat)) fn-arena c2)
                         (cons (fn-cat-row-article (fn-cat-count fn-cat) fn-arena c2)
                               (fn-cat-view-below-except target (fn-cat-count fn-cat)
                                                         (+ 1 (fn-cat-count fn-cat))
                                                         fn-arena fn-cat))))))
  :hints (("Goal" :in-theory (e/d ()
                                  (fn-cat-at-is-nth fn-cat-count-is-len fn-cat-withdraw-is-mark
                                   fn-cat-commit-is-append fn-cat-p-is-rowsp
                                   fn-cat-view-below fn-cat-row-article fn-cat-view-articles
                                   fn-cat-view-below-except))
           :use ((:instance fn-cat-view-articles-of-commit-pinned
                            (v (fn-cat-count fn-cat)) (fn-cat (fn-cat-withdraw target by fn-cat)))
                 (:instance fn-cat-view-articles-of-commit-advanced
                            (fn-cat (fn-cat-withdraw target by fn-cat)))
                 (:instance fn-cat-view-articles-of-withdraw-pinned (v (fn-cat-count fn-cat)))
                 (:instance fn-cat-view-below-of-withdraw-advanced
                            (i (fn-cat-count fn-cat)) (v (+ 1 (fn-cat-count fn-cat))))))))

; -----------------------------------------------------------------------------
; The owner: the incremental application of one committed article to the
; view, and its equation with the refresh.

; The owner O with its store replaced by S (the finish's result), nothing
; else touched: the owner fn-own-complete builds before it refreshes.
(defun fn-crf-with-store (o s)
  (declare (xargs :guard t))
  (fn-own-make s (fn-own-view o) (fn-own-conns o) (fn-own-next-id o)
               (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger o)
               (fn-own-clock o) (fn-own-facts o) (fn-own-config o) (fn-own-queue o)
               (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o)))

; applyViewDelta(view, (:article A VERDICT), S).  VIEW is the committed view
; before the completion, A the article the acceptance installed, VERDICT its
; statement verdict, S the store after the finish, read for its scalars
; only: the record count (the version), the frontier, the records and the
; configuration journal a cancel's authority is decided under, the
; acceptance the archive projects, the keyring snapshots.  The whole-archive
; comparisons of fn-own-refresh do not occur; the tests that remain are on
; the visible lists (whether A withdrew anything, whether A is visible).
(defun fn-crf-apply-article (view a verdict s)
  (declare (xargs :guard t))
  (let* ((old-raw (fn-own-view-raw view))
         (raw (cons a old-raw))
         (old-verdicts (fn-own-view-verdicts view))
         (verdicts (cons (cons (fn-article-msgid a) verdict) old-verdicts))
         (ws (fn-ctl-prepend (fn-ctl-article-withdrawals a verdicts
                                                         (fn-sf-records (fn-sn-files s))
                                                         (fn-sn-config-history s))
                             (fn-own-view-withdrawals view)))
         (old-visible (fn-state-articles (fn-own-view-archive view)))
         (visible (fn-ctl-visible-add a old-visible old-raw ws verdicts))
         (archive (fn-ctl-visible-state-of (fn-node-acceptance (fn-sn-node s)) visible))
         (plainp (and (consp visible) (equal (cdr visible) old-visible)
                      (equal (car visible) a)))
         (withdrawn (if plainp
                        (fn-own-view-withdrawn view)
                      (fn-ctl-subseq-diff raw visible)))
         (index (fn-midx-refresh (fn-own-view-index view) old-visible visible))
         (buckets (fn-gidx-refresh (fn-own-view-group-index view) old-visible visible)))
    (fn-own-view-make-visible (len (fn-sf-records (fn-sn-files s)))
                              (fn-sf-frontier (fn-sn-files s))
                              archive verdicts index buckets ws raw withdrawn
                              (fn-sn-keyring-snapshots s))))

(local (defthm fn-crf-cons-is-not-its-cdr
   (not (equal (cons a x) x))
   :hints (("Goal" :use ((:instance acl2-count (x (cons a x))))))))

; KEYSTONE (PRF-202).  The refresh over the store the finish produced is the
; delta's application to the old view: every projection.
(defthm fn-view-apply-is-refresh
  (implies (and (fn-own-store-idlep s)
                (consp a)
                (equal (fn-state-articles (fn-node-acceptance (fn-sn-node s)))
                       (cons a (fn-own-view-raw (fn-own-view o))))
                (equal (fn-sn-verdicts s)
                       (cons (cons (fn-article-msgid a) verdict)
                             (fn-own-view-verdicts (fn-own-view o)))))
           (equal (fn-own-view (fn-own-refresh (fn-crf-with-store o s)))
                  (fn-crf-apply-article (fn-own-view o) a verdict s)))
  :hints (("Goal" :in-theory (e/d (fn-own-refresh fn-crf-with-store fn-crf-apply-article
                                   fn-ctl-refresh-withdrawals fn-ctl-refresh-visible
                                   fn-ctl-verdicts-grow-by-p fn-ctl-refresh-withdrawn)
                                  (fn-ctl-article-withdrawals fn-ctl-visible-add fn-ctl-prepend
                                   fn-midx-refresh fn-gidx-refresh fn-ctl-subseq-diff
                                   fn-ctl-articles-withdrawals fn-ctl-visible-articles
                                   fn-ctl-visible-state-of fn-own-view-make-visible
                                   fn-own-store-idlep fn-state-articles fn-node-acceptance
                                   fn-sn-node fn-sn-verdicts fn-sf-records fn-sn-files
                                   fn-sf-frontier fn-sn-config-history fn-sn-keyring-snapshots
                                   fn-article-msgid
                                   ; The withdrawal walk is equal on both
                                   ; sides; opened it cost 29 s (8 million
                                   ; steps) once the cancel-lock merge grew
                                   ; fn-ctl-withdrawal-effect.
                                   fn-ctl-visible-filter-nil-means-all-withdrawn
                                   fn-ctl-visible-filter fn-ctl-withdrawn-by-p)))))

; The plain case: A is a visible article that withdraws nothing.  The apply
; is the cons, the extend and the put; nothing is rebuilt and nothing
; compared.
(defthm fn-crf-apply-article-plain
  (implies (and (consp a)
                (not (fn-ctl-causes-p (fn-ctl-prepend
                                       (fn-ctl-article-withdrawals
                                        a (cons (cons (fn-article-msgid a) verdict)
                                                (fn-own-view-verdicts view))
                                        (fn-sf-records (fn-sn-files s))
                                        (fn-sn-config-history s))
                                       (fn-own-view-withdrawals view))
                                      (fn-article-msgid a)))
                (not (fn-ctl-withdrawn-by-p a
                                            (fn-ctl-prepend
                                             (fn-ctl-article-withdrawals
                                              a (cons (cons (fn-article-msgid a) verdict)
                                                      (fn-own-view-verdicts view))
                                              (fn-sf-records (fn-sn-files s))
                                              (fn-sn-config-history s))
                                             (fn-own-view-withdrawals view))
                                            (cons a (fn-own-view-raw view))
                                            (cons (cons (fn-article-msgid a) verdict)
                                                  (fn-own-view-verdicts view))))
                (fn-own-view-group-index view))
           (let* ((view2 (fn-crf-apply-article view a verdict s))
                  (old-visible (fn-state-articles (fn-own-view-archive view))))
             (and (equal (fn-state-articles (fn-own-view-archive view2)) (cons a old-visible))
                  (equal (fn-own-view-index view2) (fn-midx-extend a (fn-own-view-index view)))
                  (equal (fn-own-view-group-index view2)
                         (fn-gidx-put-all (fn-index-article-entries a) (fn-own-view-group-index view)))
                  (equal (fn-own-view-withdrawn view2) (fn-own-view-withdrawn view))
                  (equal (fn-own-view-raw view2) (cons a (fn-own-view-raw view)))
                  (equal (fn-own-view-version view2) (len (fn-sf-records (fn-sn-files s)))))))
  :hints (("Goal" :in-theory (e/d (fn-crf-apply-article fn-ctl-visible-add fn-midx-refresh
                                   fn-gidx-refresh fn-own-view-fields-of-make-visible)
                                  (fn-ctl-article-withdrawals fn-ctl-prepend fn-ctl-causes-p
                                   fn-ctl-withdrawn-by-p fn-ctl-drop-via fn-ctl-subseq-diff
                                   fn-midx-build fn-gidx-build fn-midx-extend fn-gidx-put-all
                                   fn-index-article-entries fn-ctl-visible-articles
                                   fn-state-articles fn-node-acceptance fn-sn-node
                                   fn-sf-records fn-sn-files fn-sf-frontier fn-sn-config-history
                                   fn-sn-keyring-snapshots fn-article-msgid
                                   fn-own-view-group-index fn-own-view-withdrawals
                                   fn-own-view-raw fn-own-view-withdrawn fn-own-view-keyring
                                   fn-own-view-make-visible)))))
