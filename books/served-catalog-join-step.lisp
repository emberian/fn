; served-catalog-join-step.lisp -- the one-article step of the join between
; the owner's view and the catalog, over lists (lane sca-join, 2026-09-27;
; split from books/served-catalog-join.lisp to keep each book under 10 s).
;
; KEYSTONE fn-scj-join-of-finish-lists: the catalog after the host's
; T4-then-T2 (fn-sca-finish, with the refreshed view's index and
; fn-sca-targets-of the completed Message-ID over the refreshed withdrawals)
; shows at the new count exactly the list the refresh's one-article step
; makes (fn-ctl-visible-add): the articles the cancel drops are the rows T4
; withdraws (fn-scj-view-below-after-withdraw-targets, fn-scj-drop-via-is-keep),
; and the completed row is visible exactly when the refresh keeps the article
; (fn-scj-visible-add-shows-a).  The hypotheses are named in
; books/served-catalog-join.lisp, which states the step over the owner's view.

(in-package "ACL2")

(include-book "served-catalog-join-refresh")

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

; The rules below never reason about a Message-ID's syntax.
(local (in-theory (disable fn-nntp-article-idp-is-consp fn-scat-article-idp-is-msgid-idp
                           fn-scat-msgid-idp fn-nntp-index-msgid-okp-stringp
                           fn-nntp-index-msgid-okp fn-cp-id-length-bound)))

; -----------------------------------------------------------------------------
; The catalog's side: T4 at the count, then T2.

; Every row's withdrawal, when present, was published below version B.
(defun fn-scj-marks-below (c b)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp c)
      (and (let ((w (fn-held-withdrawn (car c))))
             (or (null w) (< (car w) b)))
           (fn-scj-marks-below (cdr c) b))
    t))

(defthm fn-scj-marks-below-nth
  (implies (and (fn-scj-marks-below c b) (natp seq) (< seq (len c))
                (fn-held-withdrawn (nth seq c)))
           (< (car (fn-held-withdrawn (nth seq c))) b))
  :rule-classes (:rewrite :linear))

(defthm fn-scj-marks-below-of-update-nth
  (implies (and (fn-scj-marks-below c b) (natp seq) (< seq (len c))
                (or (null (fn-held-withdrawn h)) (< (car (fn-held-withdrawn h)) b)))
           (fn-scj-marks-below (update-nth seq h c) b))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm fn-scj-marks-below-of-append
  (equal (fn-scj-marks-below (append a b2) b)
         (and (fn-scj-marks-below a b) (fn-scj-marks-below b2 b))))

(defthm fn-scj-marks-below-monotone
  (implies (and (fn-scj-marks-below c b) (<= b b2) (rationalp b) (rationalp b2))
           (fn-scj-marks-below c b2)))

(defthm fn-scj-len-of-mark
  (implies (natp target) (equal (len (fn-cat-mark-withdrawn target v by c)) (len c)))
  :hints (("Goal" :in-theory (enable fn-cat-mark-withdrawn))))

(defthm fn-scj-nth-of-mark
  (implies (and (natp s) (natp target))
           (equal (nth s (fn-cat-mark-withdrawn target v by c))
                  (if (and (equal s target) (< s (len c)) (null (fn-held-withdrawn (nth s c))))
                      (fn-held-with-withdrawn (nth s c) (cons v by))
                    (nth s c))))
  :hints (("Goal" :in-theory (enable fn-cat-mark-withdrawn))))

(defthm fn-scj-marks-below-of-mark
  (implies (and (fn-scj-marks-below c b) (natp target) (< v b))
           (fn-scj-marks-below (fn-cat-mark-withdrawn target v by c) b))
  :hints (("Goal" :in-theory (enable fn-cat-mark-withdrawn))))

(in-theory (disable fn-scj-marks-below))


(defthm fn-scj-marks-below-of-withdraw-targets
  (implies (and (fn-scj-marks-below c b) (< (len c) b))
           (fn-scj-marks-below (fn-sca-withdraw-targets targets view-index by c) b))
  :hints (("Goal" :induct (fn-sca-withdraw-targets targets view-index by c)
           :in-theory (enable fn-sca-withdraw-targets))))

(defthm fn-scj-len-of-withdraw-targets
  (equal (len (fn-sca-withdraw-targets targets view-index by fn-cat)) (len fn-cat))
  :hints (("Goal" :in-theory (enable fn-sca-withdraw-targets))))


(defthm fn-scj-seqs-for-of-mark
  (implies (and (natp target) (natp i))
           (equal (fn-cat-seqs-for m (fn-cat-mark-withdrawn target v by c) i)
                  (fn-cat-seqs-for m c i)))
  :hints (("Goal" :in-theory (enable fn-cat-mark-withdrawn))))

(defthm fn-scj-visiblep-at-count-of-mark
  (implies (and (natp target) (natp s) (equal n (len c)))
           (equal (fn-cat-visiblep s n (fn-cat-mark-withdrawn target n by c))
                  (fn-cat-visiblep s n c)))
  :hints (("Goal" :in-theory (enable fn-cat-visiblep))))

(defthm fn-scj-last-visible-at-count-of-mark
  (implies (and (natp target) (equal n (len c)))
           (equal (fn-cat-view-last-visible seqs n (fn-cat-mark-withdrawn target n by c))
                  (fn-cat-view-last-visible seqs n c)))
  :hints (("Goal" :induct (fn-cat-view-last-visible seqs n c)
           :in-theory (enable fn-cat-view-last-visible))))


(defun-nx fn-scj-hitp (seq targets index n c)
  (if (consp targets)
      (or (and (not (fn-midx-lookup (car targets) index))
               (equal seq (fn-cat-view-last-visible (fn-cat-seqs-for (car targets) c 0) n c)))
          (fn-scj-hitp seq (cdr targets) index n c))
    nil))

(defthm fn-scj-hitp-of-mark
  (implies (and (natp target) (equal n (len c)))
           (equal (fn-scj-hitp seq targets index n (fn-cat-mark-withdrawn target n by c))
                  (fn-scj-hitp seq targets index n c)))
  :hints (("Goal" :in-theory (disable fn-cat-view-last-visible))))


(defthm fn-scj-withdrawn-of-withdraw-targets
  (implies (natp seq)
           (equal (fn-held-withdrawn (nth seq (fn-sca-withdraw-targets targets index by c)))
                  (if (and (< seq (len c))
                           (fn-scj-hitp seq targets index (len c) c)
                           (null (fn-held-withdrawn (nth seq c))))
                      (cons (len c) by)
                    (fn-held-withdrawn (nth seq c)))))
  :hints (("Goal" :induct (fn-sca-withdraw-targets targets index by c)
           :in-theory (e/d (fn-sca-withdraw-targets) (fn-cat-view-last-visible)))))

(defthm fn-scj-row-article-of-mark
  (implies (and (natp target) (natp k))
           (equal (fn-cat-row-article k fn-arena (fn-cat-mark-withdrawn target v by fn-cat))
                  (fn-cat-row-article k fn-arena fn-cat)))
  :hints (("Goal" :in-theory (enable fn-cat-row-article))))

(defthm fn-scj-row-article-of-withdraw-targets
  (implies (natp k)
           (equal (fn-cat-row-article k fn-arena (fn-sca-withdraw-targets targets index by fn-cat))
                  (fn-cat-row-article k fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-sca-withdraw-targets targets index by fn-cat)
           :in-theory (e/d (fn-sca-withdraw-targets) (fn-cat-view-last-visible fn-cat-row-article)))))

(defthm fn-scj-view-find-names-its-msgid
  (implies (fn-cat-view-find m i v fn-cat)
           (and (equal (fn-record-msgid (nth (fn-cat-view-find m i v fn-cat) fn-cat)) m)
                (fn-cat-visible-at (fn-cat-view-find m i v fn-cat) v fn-cat)
                (natp (fn-cat-view-find m i v fn-cat))
                (< (fn-cat-view-find m i v fn-cat) (nfix i))))
  :hints (("Goal" :in-theory (disable fn-cat-visible-at-is-visiblep))))


(defthm fn-scj-visible-row-msgid-in-view
  (implies (and (natp seq) (< seq (nfix i)) (fn-cat-visible-at seq v fn-cat))
           (member-equal (fn-record-msgid (nth seq fn-cat))
                         (fn-article-msgids (fn-cat-view-below i v fn-arena fn-cat))))
  :hints (("Goal" :induct (fn-cat-view-below i v fn-arena fn-cat)
           :in-theory (disable fn-cat-visible-at-is-visiblep fn-cat-row-article))))

(defthm fn-scj-view-find-of-visible-unique
  (implies (and (no-duplicatesp-equal (fn-article-msgids (fn-cat-view-below i v fn-arena fn-cat)))
                (natp seq) (< seq (nfix i))
                (fn-cat-visible-at seq v fn-cat))
           (equal (fn-cat-view-find (fn-record-msgid (nth seq fn-cat)) i v fn-cat) seq))
  :hints (("Goal" :induct (fn-cat-view-below i v fn-arena fn-cat)
           :in-theory (disable fn-cat-visible-at-is-visiblep fn-cat-row-article
                               fn-accepted-iff-id-member))
          ("Subgoal *1/2" :use ((:instance fn-scj-visible-row-msgid-in-view (i (+ -1 i))))
           :in-theory (e/d (fn-accepted-iff-id-member) (fn-cat-visible-at-is-visiblep fn-cat-row-article)))))

(defthm fn-scj-last-visible-is-view-find
  (equal (fn-cat-view-last-visible (fn-cat-seqs-for m fn-cat 0) v fn-cat)
         (fn-cat-view-find m (len fn-cat) v fn-cat))
  :hints (("Goal" :use ((:instance fn-cat-view-find-is-msgid-column (msgid m)))
           :in-theory (disable fn-cat-view-find fn-cat-view-last-visible))))

(defthm fn-scj-hitp-iff
  (implies (and (no-duplicatesp-equal (fn-article-msgids (fn-cat-view-below (len fn-cat) n fn-arena fn-cat)))
                (natp seq) (< seq (len fn-cat))
                (fn-cat-visible-at seq n fn-cat))
           (iff (fn-scj-hitp seq targets index n fn-cat)
                (and (member-equal (fn-record-msgid (nth seq fn-cat)) targets)
                     (not (fn-midx-lookup (fn-record-msgid (nth seq fn-cat)) index)))))
  :hints (("Goal" :induct (len targets)
           :in-theory (disable fn-cat-visible-at-is-visiblep fn-cat-view-find fn-midx-lookup))
          ("Subgoal *1/1" :use ((:instance fn-scj-view-find-of-visible-unique (i (len fn-cat)) (v n))
                                (:instance fn-scj-view-find-names-its-msgid (m (car targets)) (i (len fn-cat)) (v n))))))

(defthm fn-scj-visible-at-count-when-marks-below
  (implies (and (fn-scj-marks-below fn-cat (len fn-cat)) (natp seq) (< seq (len fn-cat)))
           (iff (fn-cat-visible-at seq (len fn-cat) fn-cat)
                (null (fn-held-withdrawn (nth seq fn-cat)))))
  :hints (("Goal" :do-not-induct t :in-theory (enable fn-cat-visiblep)
           :use ((:instance fn-scj-marks-below-nth (c fn-cat) (b (len fn-cat)))))))

(defthm fn-scj-visible-after-withdraw-targets
  (implies (and (fn-scj-marks-below fn-cat (len fn-cat))
                (no-duplicatesp-equal (fn-article-msgids (fn-cat-view-below (len fn-cat) (len fn-cat) fn-arena fn-cat)))
                (natp seq) (< seq (len fn-cat)))
           (iff (fn-cat-visible-at seq (+ 1 (len fn-cat))
                                   (fn-sca-withdraw-targets targets index by fn-cat))
                (and (null (fn-held-withdrawn (nth seq fn-cat)))
                     (not (and (member-equal (fn-record-msgid (nth seq fn-cat)) targets)
                               (not (fn-midx-lookup (fn-record-msgid (nth seq fn-cat)) index)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cat-visiblep) (fn-scj-hitp-iff fn-scj-visible-at-count-when-marks-below
                                                              fn-midx-lookup fn-sca-withdraw-targets))
           :use ((:instance fn-scj-hitp-iff (n (len fn-cat)))
                 (:instance fn-scj-visible-at-count-when-marks-below)))))

(defthm fn-scj-view-below-after-withdraw-targets
  (implies (and (fn-scj-marks-below fn-cat (len fn-cat))
                (no-duplicatesp-equal (fn-article-msgids (fn-cat-view-below (len fn-cat) (len fn-cat) fn-arena fn-cat)))
                (natp i) (<= i (len fn-cat)))
           (equal (fn-cat-view-below i (+ 1 (len fn-cat)) fn-arena
                                     (fn-sca-withdraw-targets targets index by fn-cat))
                  (fn-scj-keep (fn-cat-view-below i (len fn-cat) fn-arena fn-cat) targets index)))
  :hints (("Goal" :induct (fn-cat-view-below i (len fn-cat) fn-arena fn-cat)
           :in-theory (disable fn-cat-visible-at-is-visiblep fn-sca-withdraw-targets fn-midx-lookup
                               fn-cat-row-article))
          ("Subgoal *1/2" :use ((:instance fn-scj-visible-after-withdraw-targets (seq (+ -1 i)))
                                (:instance fn-scj-visible-at-count-when-marks-below (seq (+ -1 i)))))))

(defthm fn-scj-withdrawn-of-assign
  (equal (fn-held-withdrawn (fn-cat-assign h c)) (fn-held-withdrawn h))
  :hints (("Goal" :in-theory (enable fn-cat-assign fn-held-with-numbers fn-record-internals
                                     fn-held-internals))))

(defthm fn-scj-len-of-commit
  (equal (len (fn-cat-commit h c)) (+ 1 (len c)))
  :hints (("Goal" :in-theory (enable fn-cat-commit-is-append))))

(defthm fn-scj-marks-below-of-commit
  (implies (and (fn-scj-marks-below c b)
                (or (null (fn-held-withdrawn h)) (< (car (fn-held-withdrawn h)) b)))
           (fn-scj-marks-below (fn-cat-commit h c) b))
  :hints (("Goal" :in-theory (enable fn-cat-commit-is-append fn-scj-marks-below))))

(defthm fn-scj-nth-len-of-commit
  (equal (nth (len c) (fn-cat-commit h c)) (fn-cat-assign h c))
  :hints (("Goal" :use ((:instance fn-cat-commit-new-row (fn-cat c)))
           :in-theory (disable fn-cat-commit-new-row fn-cat-commit-is-append))))

(defthm fn-scj-withdrawn-of-commit-at-len
  (implies (equal n (len c))
           (equal (fn-held-withdrawn (nth n (fn-cat-commit h c))) (fn-held-withdrawn h)))
  :hints (("Goal" :in-theory (disable fn-cat-commit-is-append))))

; The catalog after the host's finish (T4 then T2): the view at the new
; count is the kept rows, with the completed row on top when the refreshed
; index shows its Message-ID.
(defthm fn-scj-view-after-finish
  (let ((c2 (mv-nth 2 (fn-sca-finish token pending index targets fn-cat)))
        (c4 (fn-sca-withdraw-targets targets index (len fn-cat) fn-cat))
        (x (fn-scj-keep (fn-cat-view-below (len fn-cat) (len fn-cat) fn-arena fn-cat)
                        targets index)))
    (implies (and (fn-scj-marks-below fn-cat (len fn-cat))
                  (no-duplicatesp-equal
                   (fn-article-msgids (fn-cat-view-below (len fn-cat) (len fn-cat) fn-arena fn-cat)))
                  (fn-pc-p pending)
                  (equal token (fn-pc-token pending))
                  (equal (fn-pc-expected pending) (len fn-cat))
                  (null (fn-held-withdrawn (fn-pc-held pending))))
             (and (equal (len c2) (+ 1 (len fn-cat)))
                  (fn-scj-marks-below c2 (+ 1 (len fn-cat)))
                  (equal (fn-cat-view-articles (+ 1 (len fn-cat)) fn-arena c2)
                         (if (fn-midx-lookup (fn-record-msgid (fn-pc-held pending)) index)
                             (cons (fn-cat-row-article (len fn-cat) fn-arena
                                                       (fn-cat-commit (fn-pc-held pending) c4))
                                   x)
                           x)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-sca-finish fn-sca-complete fn-cat-complete fn-cat-complete-hidden
                            fn-cat-view-articles fn-cat-visible-at-by-row)
                           (fn-cat-visible-at-is-visiblep fn-sca-withdraw-targets fn-midx-lookup
                            fn-cat-row-article fn-cat-view-below fn-cat-commit-is-append
                            fn-scj-keep))
           :expand ((fn-cat-view-below (+ 1 (len fn-cat)) (+ 1 (len fn-cat)) fn-arena
                                       (fn-cat-commit (fn-pc-held pending)
                                                      (fn-sca-withdraw-targets targets index (len fn-cat) fn-cat)))
                    (fn-cat-view-below (+ 1 (len fn-cat)) (+ 1 (len fn-cat)) fn-arena
                                       (fn-cat-commit (fn-held-with-withdrawn (fn-pc-held pending)
                                                                              (cons (len fn-cat) (len fn-cat)))
                                                      (fn-sca-withdraw-targets targets index (len fn-cat) fn-cat))))
           :use ((:instance fn-scj-view-below-after-withdraw-targets (i (len fn-cat)) (by (len fn-cat)))
                 (:instance fn-pc-p-fields (pc pending))))))

(defthm fn-scj-true-listp-of-view-below
  (true-listp (fn-cat-view-below i v fn-arena fn-cat))
  :rule-classes :type-prescription)

(defthm fn-scj-join-of-finish-lists
  (let* ((n (len fn-cat))
         (v (fn-cat-view-below n n fn-arena fn-cat))
         (v2 (fn-ctl-visible-add a v old ws verdicts))
         (index (fn-midx-build v2))
         (targets (fn-sca-targets-of (fn-article-msgid a) ws))
         (c2 (mv-nth 2 (fn-sca-finish token pending index targets fn-cat))))
    (implies (and (fn-scj-marks-below fn-cat n)
                  (consp a)
                  (stringp (fn-article-msgid a))
                  (no-duplicatesp-equal (fn-article-msgids (cons a v)))
                  (fn-midx-string-article-listp v)
                  (fn-midx-string-article-listp v2)
                  (fn-pc-p pending)
                  (equal token (fn-pc-token pending))
                  (equal (fn-pc-expected pending) n)
                  (null (fn-held-withdrawn (fn-pc-held pending)))
                  (equal (fn-record-msgid (fn-pc-held pending)) (fn-article-msgid a))
                  (equal (fn-cat-row-article n fn-arena
                                             (fn-cat-commit (fn-pc-held pending)
                                                            (fn-sca-withdraw-targets targets index n fn-cat)))
                         a))
             (and (equal (fn-cat-view-articles (+ 1 n) fn-arena c2) v2)
                  (equal (len c2) (+ 1 n))
                  (fn-scj-marks-below c2 (+ 1 n)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ctl-visible-add)
                           (fn-scj-view-after-finish fn-scj-visible-add-kept-is-keep fn-scj-visible-add-shows-a
                            fn-sca-finish fn-midx-build fn-midx-lookup fn-ctl-drop-via fn-ctl-causes-p
                            fn-ctl-withdrawn-by-p fn-scj-keep fn-cat-view-below fn-cat-row-article
                            fn-sca-targets-of fn-sca-withdraw-targets fn-cat-commit-is-append))
           :use ((:instance fn-scj-view-after-finish
                            (index (fn-midx-build (fn-ctl-visible-add a (fn-cat-view-below (len fn-cat) (len fn-cat) fn-arena fn-cat) old ws verdicts)))
                            (targets (fn-sca-targets-of (fn-article-msgid a) ws)))
                 (:instance fn-scj-visible-add-kept-is-keep (v (fn-cat-view-below (len fn-cat) (len fn-cat) fn-arena fn-cat)))
                 (:instance fn-scj-visible-add-shows-a (v (fn-cat-view-below (len fn-cat) (len fn-cat) fn-arena fn-cat)))))))
