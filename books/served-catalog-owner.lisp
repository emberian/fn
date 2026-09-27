; served-catalog-owner.lisp -- the catalog at the owner's entries (step 8 of
; the catalog slice, the R side; planning/evidence/catalog-slice-2026-09-26.md).
;
; The host maintains the catalog at three entries, each an ACL2 decision the
; host only plumbs (host/owner-host.lisp):
;   E  fn-sca-load-history      at recovery (fn-owner-install-extended): the
;                               catalog of the installed store's history,
;                               from empty;
;   T2 fn-sca-complete          at fn-owner-finish-submission: the pending
;                               PreparedCommit completed by the completing
;                               record's token -- HIDDEN when the owner's
;                               refreshed view no longer shows its
;                               Message-ID (R1: a cancel that arrived before
;                               its target; the row is committed withdrawn at
;                               its own index and no view shows it, as the
;                               owner's refresh shows it at no version);
;   T4 fn-sca-withdraw-targets  after T2: the completed article's withdrawal
;                               targets (books/control-visible.lisp puts the
;                               newest article's withdrawals first in the
;                               view's list) that the view no longer shows are
;                               withdrawn at the count, the cancel's row as
;                               BY.
; The host calls T4 and T2 as ONE step, fn-sca-finish, T4 first: the
; withdrawals are published at the count before the completing row commits,
; so the first version that shows the row (a fresh reader's pin) is the first
; that hides its targets (fn-sca-finish-hides-the-targets-from-fresh-views),
; a completed R1 row is visible at no version (fn-sca-finish-hides-the-
; hidden-row), and every version at or below the count is unchanged
; (fn-sca-finish-keeps-pinned-views).
; The prepare is books/catalog-commit.lisp fn-cat-prepare itself, called at
; fn-owner-prepare-buffer over the payload buffer.
;
; R (books/catalog-relation.lisp fn-cat-history-relation) is established by E
; (fn-cat-ocl-relation-at-recover) and preserved by T2 in both forms
; (fn-cat-ocl-relation-of-article-finish, fn-cat-relation-of-complete-hidden)
; and by T4 (fn-cat-ocl-relation-of-withdraw), all in books/catalog-entries
; and catalog-relation; the theorems below are this book's shapes of those
; keystones over the functions the host calls.
;
; The JOIN -- that the view a pin names in the catalog (books/served-catalog-
; chain.lisp fn-scr-view-of) holds the pinned archive's articles, the
; hypothesis fn-scr-catalogp carries -- is stated here as fn-sca-join and is
; an OPEN proof target (the boundary owner's R3): its teeth are in the test
; book; what continues without it is the served path under the hypothesis.

(in-package "ACL2")

(include-book "served-catalog-chain")
(include-book "catalog-entries")
(include-book "catalog-refresh")

; -----------------------------------------------------------------------------
; E: the catalog of a history, from empty.

; Each article record's row, visible when the recovered owner's view shows
; its Message-ID, hidden otherwise (a cancel the history made effective).
(defun fn-sca-load-rows (records view-index keyring generation fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (fn-prin-keyringp keyring) (natp generation))))
  (if (consp records)
      (if (fn-record-p (car records))
          (mv-let (fn-arena fn-cat)
            (if (fn-midx-lookup (fn-record-msgid (car records)) view-index)
                (fn-cat-load-row (car records) keyring generation fn-arena fn-cat)
              (fn-cat-load-row-hidden (car records) keyring generation fn-arena fn-cat))
            (fn-sca-load-rows (cdr records) view-index keyring generation fn-arena fn-cat))
        (fn-sca-load-rows (cdr records) view-index keyring generation fn-arena fn-cat))
    (mv fn-arena fn-cat)))

(defun fn-sca-load-history (records view-index keyring generation fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (fn-prin-keyringp keyring) (natp generation))))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-cat (fn-cat-clear fn-cat)))
    (fn-sca-load-rows records view-index keyring generation fn-arena fn-cat)))

; The fold's induction, carrying the history appended so far
; (books/catalog-relation.lisp fn-crl-load-ind).
(local (defun fn-sca-load-ind (records history view-index keyring generation fn-arena fn-cat)
   (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil)
            (irrelevant history))
   (if (consp records)
       (if (fn-record-p (car records))
           (mv-let (fn-arena fn-cat)
             (if (fn-midx-lookup (fn-record-msgid (car records)) view-index)
                 (fn-cat-load-row (car records) keyring generation fn-arena fn-cat)
               (fn-cat-load-row-hidden (car records) keyring generation fn-arena fn-cat))
             (fn-sca-load-ind (cdr records) (append history (list (car records)))
                              view-index keyring generation fn-arena fn-cat))
         (fn-sca-load-ind (cdr records) (append history (list (car records)))
                          view-index keyring generation fn-arena fn-cat))
     (mv fn-arena fn-cat))))

; The fold's base: an atom appended to the history adds no article.
(local (defthm fn-sca-relation-of-append-atom
   (implies (not (consp x))
            (equal (fn-cat-history-relation (append h x) fn-arena fn-cat)
                   (fn-cat-history-relation h fn-arena fn-cat)))))

; KEYSTONE (E): the fold establishes R over the history it loads, whatever
; the view hides (catalog-relation's two step theorems; catalog-entries'
; non-article step).
(defthm fn-sca-load-rows-establishes-relation
  (implies (and (fn-cat-history-relation history fn-arena fn-cat)
                (natp generation))
           (mv-let (fn-arena2 fn-cat2)
             (fn-sca-load-rows records view-index keyring generation fn-arena fn-cat)
             (fn-cat-history-relation (append history records) fn-arena2 fn-cat2)))
  :hints (("Goal" :induct (fn-sca-load-ind records history view-index keyring generation
                                           fn-arena fn-cat)
           :expand ((fn-sca-load-rows records view-index keyring generation fn-arena fn-cat))
           :in-theory (e/d (fn-sca-load-rows)
                           (fn-cat-history-relation fn-cat-load-row fn-cat-load-row-hidden
                            fn-cat-count-is-len fn-cat-at-is-nth fn-cat-p-is-held-listp)))
          ("Subgoal *1/1" :use ((:instance fn-cat-load-row-keeps-relation
                                          (w (car records)) (records history))
                                (:instance fn-cat-load-row-hidden-keeps-relation
                                          (w (car records)) (records history))))))

(defthm fn-sca-load-history-establishes-relation
  (implies (natp generation)
           (mv-let (fn-arena2 fn-cat2)
             (fn-sca-load-history records view-index keyring generation fn-arena fn-cat)
             (fn-cat-history-relation records fn-arena2 fn-cat2)))
  :hints (("Goal" :use ((:instance fn-sca-load-rows-establishes-relation
                                   (history nil) (fn-arena (fn-arena-clear fn-arena))
                                   (fn-cat (fn-cat-clear fn-cat)))
                        (:instance fn-cat-relation-at-init))
           :in-theory (e/d (fn-sca-load-history fn-arena-clear fn-cat-clear
                            create-fn-arena create-fn-cat)
                           (fn-cat-history-relation fn-sca-load-rows)))))

; -----------------------------------------------------------------------------
; T2 and R1: the completion, hidden when the view no longer shows the row.

(defun fn-sca-complete (token pending view-index fn-cat)
  (declare (xargs :stobjs fn-cat
                  :guard (fn-pc-optionp pending)
                  :guard-hints (("Goal" :in-theory (enable fn-pc-p)))))
  (if (and pending
           (not (fn-midx-lookup (fn-record-msgid (fn-pc-held pending)) view-index)))
      (fn-cat-complete-hidden token pending (fn-pc-expected pending) fn-cat)
    (fn-cat-complete token pending fn-cat)))

(defthm fn-sca-complete-keeps-the-relation
  (implies (and (fn-cat-history-relation records fn-arena fn-cat)
                (fn-pc-p pending)
                (equal token (fn-pc-token pending))
                (equal (fn-pc-expected pending) (fn-cat-count fn-cat))
                (< (fn-record-payload (fn-pc-held pending)) (fn-arena-count fn-arena))
                (equal (fn-held-wire-of (fn-pc-held pending) fn-arena) w)
                (fn-record-p w))
           (fn-cat-history-relation (append records (list w)) fn-arena
                                    (mv-nth 2 (fn-sca-complete token pending view-index fn-cat))))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-sca-complete fn-cat-relation-of-complete)
                              (theory 'minimal-theory))
           :use ((:instance fn-cat-relation-of-complete-hidden
                            (by (fn-pc-expected pending)))
                 (:instance fn-pc-p-fields (pc pending))))))

; -----------------------------------------------------------------------------
; T4: the completed article's withdrawal targets the view no longer shows.

; The targets of the withdrawals CAUSE contributed: the view's list holds the
; newest article's first (books/control-visible.lisp fn-ctl-refresh-
; withdrawals, fn-ctl-prepend), so the scan stops at the first other cause.
(defun fn-sca-targets-of (cause ws)
  (declare (xargs :guard t))
  (if (and (consp ws) (fn-ctl-withdrawalp (car ws))
           (equal (fn-ctl-w-cause (car ws)) cause))
      (cons (fn-ctl-w-target (car ws)) (fn-sca-targets-of cause (cdr ws)))
    nil))

(defun fn-sca-withdraw-targets (targets view-index by fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp by)))
  (if (consp targets)
      (let ((fn-cat
             (if (fn-midx-lookup (car targets) view-index)
                 fn-cat
               (let ((seq (fn-cat-view-last-visible
                           (fn-cat-msgid-seqs (car targets) fn-cat)
                           (fn-cat-count fn-cat) fn-cat)))
                 (if (and (natp seq) (< seq (fn-cat-count fn-cat)))
                     (fn-cat-withdraw seq by fn-cat)
                   fn-cat)))))
        (fn-sca-withdraw-targets (cdr targets) view-index by fn-cat))
    fn-cat))

(defthm fn-sca-withdraw-targets-keeps-the-relation
  (implies (and (fn-cat-history-relation records fn-arena fn-cat) (natp by))
           (fn-cat-history-relation records fn-arena
                                    (fn-sca-withdraw-targets targets view-index by fn-cat)))
  :hints (("Goal" :induct (fn-sca-withdraw-targets targets view-index by fn-cat)
           :in-theory (union-theories
                       '(fn-sca-withdraw-targets fn-cat-relation-of-withdraw)
                       (theory 'minimal-theory)))))

;; -----------------------------------------------------------------------------
; The finish the host calls (fn-owner-finish-submission): T4 BEFORE T2.
;
; The withdrawals are published at the count BEFORE the completing row
; commits, so the version that first shows the completing row (count + 1, a
; fresh reader's pin: fn-scr-view-of of the refreshed owner's version) is
; the first that hides the targets (books/catalog-refresh.lisp
; fn-cat-withdraw-then-commit-view); a reader pinned at or below the count
; sees neither.  The reverse order (complete, then withdraw at count + 1)
; would show a target at exactly the fresh reader's view.  R1 (a cancel that
; arrived before its target) is the completion's hidden form: the row is
; committed withdrawn at its own index.  A refused completion (a stale
; token, a count the pending row did not expect) changes nothing.

(defun fn-sca-finish (token pending view-index targets fn-cat)
  (declare (xargs :stobjs fn-cat
                  :guard (fn-pc-optionp pending)
                  :guard-hints (("Goal" :in-theory (enable fn-pc-p)))))
  (if (and pending
           (equal token (fn-pc-token pending))
           (equal (fn-pc-expected pending) (fn-cat-count fn-cat)))
      (let ((fn-cat (fn-sca-withdraw-targets targets view-index
                                             (fn-pc-expected pending) fn-cat)))
        (fn-sca-complete token pending view-index fn-cat))
    (fn-sca-complete token pending view-index fn-cat)))

(local (defthm fn-sca-withdrawn-of-assign
   (equal (fn-held-withdrawn (fn-cat-assign h c)) (fn-held-withdrawn h))
   :hints (("Goal" :in-theory (enable fn-cat-assign fn-held-with-numbers fn-record-internals
                                      fn-held-internals)))))

(local (defthm fn-sca-len-of-withdraw-targets
   (equal (len (fn-sca-withdraw-targets targets view-index by fn-cat)) (len fn-cat))
   :hints (("Goal" :in-theory (enable fn-sca-withdraw-targets fn-cat-mark-withdrawn)))))

(local (defthm fn-sca-len-of-withdraw
   (implies (and (natp target) (< target (len fn-cat)))
            (equal (len (fn-cat-withdraw target by fn-cat)) (len fn-cat)))
   :hints (("Goal" :in-theory (enable fn-cat-mark-withdrawn)))))

(local (defthm fn-sca-last-visible-type
   (or (null (fn-cat-view-last-visible seqs v fn-cat))
       (natp (fn-cat-view-last-visible seqs v fn-cat)))
   :rule-classes :type-prescription))

; Pinned readers: a version at or below the count sees no change.
(local (defthm fn-sca-view-articles-of-withdraw-targets-pinned
   (implies (and (natp v) (<= v (fn-cat-count fn-cat)))
            (equal (fn-cat-view-articles v fn-arena (fn-sca-withdraw-targets targets view-index by fn-cat))
                   (fn-cat-view-articles v fn-arena fn-cat)))
   :hints (("Goal" :induct (fn-sca-withdraw-targets targets view-index by fn-cat)
            :in-theory (e/d (fn-sca-withdraw-targets)
                            (fn-cat-withdraw-is-mark fn-cat-view-articles fn-cat-view-last-visible
                             fn-cat-msgid-seqs-is-seqs-for))))))

(defthm fn-sca-finish-keeps-the-relation
  (implies (and (fn-cat-history-relation records fn-arena fn-cat)
                (fn-pc-p pending)
                (equal token (fn-pc-token pending))
                (equal (fn-pc-expected pending) (fn-cat-count fn-cat))
                (< (fn-record-payload (fn-pc-held pending)) (fn-arena-count fn-arena))
                (equal (fn-held-wire-of (fn-pc-held pending) fn-arena) w)
                (fn-record-p w))
           (fn-cat-history-relation (append records (list w)) fn-arena
                                    (mv-nth 2 (fn-sca-finish token pending view-index targets fn-cat))))
  :hints (("Goal" :in-theory (e/d (fn-sca-finish) (fn-sca-complete fn-cat-history-relation
                                                   fn-sca-withdraw-targets))
           :use ((:instance fn-sca-withdraw-targets-keeps-the-relation
                            (by (fn-pc-expected pending)))
                 (:instance fn-sca-complete-keeps-the-relation
                            (fn-cat (fn-sca-withdraw-targets targets view-index
                                                             (fn-pc-expected pending) fn-cat)))))))

(local (defthm fn-sca-view-articles-of-complete-pinned
   (implies (and (natp v) (<= v (fn-cat-count fn-cat)))
            (equal (fn-cat-view-articles v fn-arena (mv-nth 2 (fn-sca-complete token pending view-index fn-cat)))
                   (fn-cat-view-articles v fn-arena fn-cat)))
   :hints (("Goal" :in-theory (e/d (fn-sca-complete fn-cat-complete fn-cat-complete-hidden)
                                   (fn-cat-commit-is-append fn-cat-view-articles))))))

; KEYSTONE (pinned readers): a version at or below the count before the
; finish sees no change.
(defthm fn-sca-finish-keeps-pinned-views
  (implies (and (natp v) (<= v (fn-cat-count fn-cat)))
           (equal (fn-cat-view-articles v fn-arena
                                        (mv-nth 2 (fn-sca-finish token pending view-index targets fn-cat)))
                  (fn-cat-view-articles v fn-arena fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-sca-finish) (fn-sca-complete fn-sca-withdraw-targets
                                                   fn-cat-view-articles)))))

; The row facts the two fresh-view keystones read (list model).

(local (defthm fn-sca-nth-of-append-at-len
   (equal (nth (len a) (append a b)) (car b))
   :hints (("Goal" :induct (len a) :in-theory (enable nth append len)))))

(local (defthm fn-sca-nth-of-append-at-n
   (implies (equal n (len a))
            (equal (nth n (append a b)) (car b)))))

(local (defthm fn-sca-withdrawn-of-with-withdrawn
   (equal (fn-held-withdrawn (fn-held-with-withdrawn h w)) w)
   :hints (("Goal" :in-theory (enable fn-held-with-withdrawn fn-record-internals
                                      fn-held-internals)))))

(local (defthm fn-sca-msgid-of-with-withdrawn
   (equal (fn-record-msgid (fn-held-with-withdrawn h w)) (fn-record-msgid h))
   :hints (("Goal" :in-theory (enable fn-held-with-withdrawn fn-record-internals
                                      fn-held-internals)))))

(local (defun fn-sca-seqs-ind (k c i)
   (if (consp c)
       (if (zp k) (list c i) (fn-sca-seqs-ind (- k 1) (cdr c) (+ 1 i)))
     (list k i))))

(local (defthm fn-sca-seqs-for-of-update-nth
   (implies (and (natp k) (< k (len c))
                 (equal (fn-record-msgid x) (fn-record-msgid (nth k c))))
            (equal (fn-cat-seqs-for m (update-nth k x c) i)
                   (fn-cat-seqs-for m c i)))
   :hints (("Goal" :induct (fn-sca-seqs-ind k c i)
            :in-theory (enable fn-cat-seqs-for update-nth nth)))))

(local (defthm fn-sca-visiblep-at-len-of-mark
   (equal (fn-cat-visiblep s (len c) (fn-cat-mark-withdrawn tg (len c) by c))
          (fn-cat-visiblep s (len c) c))
   :hints (("Goal" :in-theory (enable fn-cat-visiblep fn-cat-mark-withdrawn)))))

(local (defthm fn-sca-len-of-mark
   (implies (natp tg)
            (equal (len (fn-cat-mark-withdrawn tg v by c)) (len c)))
   :hints (("Goal" :in-theory (enable fn-cat-mark-withdrawn)))))

(local (defthm fn-sca-last-visible-at-len-of-mark
   (implies (and (natp tg) (< tg (len c)))
            (equal (fn-cat-view-last-visible seqs (len c) (fn-cat-mark-withdrawn tg (len c) by c))
                   (fn-cat-view-last-visible seqs (len c) c)))
   :hints (("Goal" :induct (fn-cat-view-last-visible seqs (len c) c)
            :in-theory (enable fn-cat-view-last-visible)))))

(local (defthm fn-sca-seqs-for-of-mark
   (implies (natp tg)
            (equal (fn-cat-seqs-for m (fn-cat-mark-withdrawn tg v by c) i)
                   (fn-cat-seqs-for m c i)))
   :hints (("Goal" :in-theory (enable fn-cat-mark-withdrawn)))))

(local (defthm fn-sca-withdrawn-cell-of-mark
   (implies (and (natp s) (fn-held-withdrawn (nth s c)))
            (equal (fn-held-withdrawn (nth s (fn-cat-mark-withdrawn tg v by c)))
                   (fn-held-withdrawn (nth s c))))
   :hints (("Goal" :in-theory (enable fn-cat-mark-withdrawn)))))

(local (defthm fn-sca-withdrawn-cell-of-withdraw-targets
   (implies (and (natp s) (fn-held-withdrawn (nth s fn-cat)))
            (equal (fn-held-withdrawn (nth s (fn-sca-withdraw-targets targets view-index by fn-cat)))
                   (fn-held-withdrawn (nth s fn-cat))))
   :hints (("Goal" :induct (fn-sca-withdraw-targets targets view-index by fn-cat)
            :in-theory (e/d (fn-sca-withdraw-targets)
                            (fn-cat-view-last-visible fn-cat-msgid-seqs-is-seqs-for))))))

(local (defthm fn-sca-last-visible-below-len
   (implies (fn-cat-view-last-visible seqs v fn-cat)
            (< (fn-cat-view-last-visible seqs v fn-cat) (len fn-cat)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-cat-view-last-visible)))))

(local (defthm fn-sca-withdrawn-cell-of-mark-split
   (implies (and (natp s) (natp tg))
            (equal (fn-held-withdrawn (nth s (fn-cat-mark-withdrawn tg v by c)))
                   (if (and (equal s tg) (< tg (len c)) (null (fn-held-withdrawn (nth tg c))))
                       (cons v by)
                     (fn-held-withdrawn (nth s c)))))
   :hints (("Goal" :in-theory (enable fn-cat-mark-withdrawn)))))

; KEYSTONE (R1): the completed row of a Message-ID the refreshed view no
; longer shows is visible at no version.
(defthm fn-sca-finish-hides-the-hidden-row
  (implies (and (fn-pc-p pending)
                (equal token (fn-pc-token pending))
                (equal (fn-pc-expected pending) (fn-cat-count fn-cat))
                (not (fn-midx-lookup (fn-record-msgid (fn-pc-held pending)) view-index)))
           (let ((c2 (mv-nth 2 (fn-sca-finish token pending view-index targets fn-cat))))
             (and (equal (fn-cat-count c2) (+ 1 (fn-cat-count fn-cat)))
                  (not (fn-cat-visible-at (fn-cat-count fn-cat) v c2)))))
  :hints (("Goal" :in-theory (enable fn-sca-finish fn-sca-complete fn-cat-complete-hidden
                                     fn-cat-visiblep))))

(local (defthm fn-sca-withdraw-targets-hides
   (implies (and (member-equal mid targets)
                 (not (fn-midx-lookup mid view-index))
                 (equal seq (fn-cat-view-last-visible (fn-cat-msgid-seqs mid fn-cat)
                                                      (fn-cat-count fn-cat) fn-cat))
                 seq
                 (null (fn-held-withdrawn (fn-cat-at seq fn-cat)))
                 (natp v) (< (fn-cat-count fn-cat) v))
            (not (fn-cat-visible-at seq v (fn-sca-withdraw-targets targets view-index by fn-cat))))
   :hints (("Goal" :induct (fn-sca-withdraw-targets targets view-index by fn-cat)
            :in-theory (e/d (fn-sca-withdraw-targets fn-cat-visiblep)
                            (fn-cat-view-last-visible))))))

(local (defthm fn-sca-nth-of-append-below
   (implies (and (natp s) (< s (len a)))
            (equal (nth s (append a b)) (nth s a)))
   :hints (("Goal" :in-theory (enable nth append)))))

(local (defthm fn-sca-visible-at-of-complete-below
   (implies (and (natp seq) (< seq (fn-cat-count fn-cat)))
            (equal (fn-cat-visible-at seq v (mv-nth 2 (fn-sca-complete token pending view-index fn-cat)))
                   (fn-cat-visible-at seq v fn-cat)))
   :hints (("Goal" :in-theory (enable fn-sca-complete fn-cat-complete fn-cat-complete-hidden
                                      fn-cat-visiblep)))))

; KEYSTONE (T4 before T2): a target the refreshed view no longer shows --
; its Message-ID's newest row visible at the count, not yet withdrawn -- is
; visible at no version past the count, the first a fresh reader can pin.
(defthm fn-sca-finish-hides-the-targets-from-fresh-views
  (implies (and (fn-pc-p pending)
                (equal token (fn-pc-token pending))
                (equal (fn-pc-expected pending) (fn-cat-count fn-cat))
                (member-equal mid targets)
                (not (fn-midx-lookup mid view-index))
                (equal seq (fn-cat-view-last-visible (fn-cat-msgid-seqs mid fn-cat)
                                                     (fn-cat-count fn-cat) fn-cat))
                seq
                (null (fn-held-withdrawn (fn-cat-at seq fn-cat)))
                (natp v) (< (fn-cat-count fn-cat) v))
           (not (fn-cat-visible-at seq v (mv-nth 2 (fn-sca-finish token pending view-index
                                                                  targets fn-cat)))))
  :hints (("Goal" :in-theory (e/d (fn-sca-finish)
                                  (fn-sca-complete fn-sca-withdraw-targets
                                   fn-cat-view-last-visible fn-cat-visible-at-is-visiblep))
           :use ((:instance fn-sca-withdraw-targets-hides (by (fn-pc-expected pending)))))))

; -----------------------------------------------------------------------------
; The join (OPEN): the view a pin names holds the pinned archive's articles.
; Stated over the owner's current view: its version and archive.  Proving it
; is the R-side completion of step 8; until then it is the hypothesis the
; served chain carries (fn-scr-catalogp), with teeth in the test book.

(defun-nx fn-sca-join (o fn-arena fn-cat)
  (equal (fn-state-articles (fn-own-view-archive (fn-own-view o)))
         (fn-cat-view-articles (fn-scr-view-of (fn-own-view-version (fn-own-view o)) fn-cat)
                               fn-arena fn-cat)))
