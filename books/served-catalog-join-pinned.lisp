; served-catalog-join-pinned.lisp -- pinned readers survive the host's
; catalog finish (lane sca-join-4, sub-lane P, 2026-09-27; PRF-302, step 3
; of the join's discharge).
;
; A connection (and the live view, and a captured reader view) reads the
; catalog at fn-scr-view-of of the version it pinned: a BISECTION over the
; rows' sequences, which counts the rows below the version only when the
; rows are sorted by sequence.  This book carries that sortedness and shows
; the pinned view does not move when the host finishes a completion:
;
;   P1  fn-scj-seqs-sortedp: the rows' sequences are nondecreasing.  Every
;       open establishes it (fn-scj-seqs-sortedp-at-open: the replay checks
;       each event's sequence is its position, fn-scj-seqs-from-of-cpr-
;       replay; a loaded row's sequence is its event's, fn-scj-load-h-
;       sequence), and fn-sca-finish keeps it when every row's sequence is
;       below the completed row's (fn-scj-seqs-sortedp-of-finish).
;   P2  fn-scj-view-of-of-finish: fn-scr-view-of V is unchanged by the
;       finish for V at most the completed row's sequence (the bisection is
;       the first row at or above V, fn-scj-view-of-is-split).
;   P3  fn-scj-freshp-of-finish: the number table stays fresh.
;   P4  fn-scj-catalogp-of-finish (KEYSTONE): the -cat keystone's
;       hypothesis at fn-scr-view-of V survives the finish; hence every
;       pinned connection (fn-scj-conns-pinp-of-finish) and, at the host's
;       call, fn-scj-conns-pinp-at-host-finish.
;   P5  a connection pinned to the current view is pinned exactly when the
;       live view is (fn-scj-conn-pinp-when-on-view), and the live view is
;       from the join, freshness and the view's own index facts
;       (fn-scj-live-okp-of-joinp).
;
; Teeth: tests/acl2/served-catalog-join-pinned-tests.lisp.

(in-package "ACL2")

(include-book "served-catalog-join-conns")

; -----------------------------------------------------------------------------
; The rows' sequences, as naturals.

(defun fn-scj-seqs (c)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp c)
      (cons (nfix (fn-record-sequence (car c))) (fn-scj-seqs (cdr c)))
    nil))

(defun fn-scj-nats-sortedp (xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp xs) (consp (cdr xs)))
      (and (<= (nfix (car xs)) (nfix (cadr xs)))
           (fn-scj-nats-sortedp (cdr xs)))
    t))

; P1: the catalog's rows are sorted by sequence.
(defun fn-scj-seqs-sortedp (c)
  (declare (xargs :guard t :verify-guards nil))
  (fn-scj-nats-sortedp (fn-scj-seqs c)))

(defun fn-scj-nats-below (xs v)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs)
      (and (< (nfix (car xs)) (nfix v))
           (fn-scj-nats-below (cdr xs) v))
    t))

; The index of the first sequence at or above V (the count below V when
; sorted).
(defun fn-scj-split (v xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs)
      (if (< (nfix (car xs)) (nfix v))
          (+ 1 (fn-scj-split v (cdr xs)))
        0)
    0))

(defthm fn-scj-len-of-seqs
  (equal (len (fn-scj-seqs c)) (len c)))

(defthm fn-scj-nth-of-seqs
  (implies (< (nfix i) (len c))
           (equal (nth i (fn-scj-seqs c)) (nfix (fn-record-sequence (nth i c))))))

(defthm fn-scj-seqs-below-is-nats-below
  (equal (fn-scj-seqs-below c v) (fn-scj-nats-below (fn-scj-seqs c) v))
  :hints (("Goal" :in-theory (enable fn-scj-seqs-below))))

(defthm fn-scj-seqs-of-append
  (equal (fn-scj-seqs (append a b)) (append (fn-scj-seqs a) (fn-scj-seqs b))))

(defthm fn-scj-seqs-of-commit
  (equal (fn-scj-seqs (fn-cat-commit h c))
         (append (fn-scj-seqs c) (list (nfix (fn-record-sequence h)))))
  :hints (("Goal" :in-theory (disable fn-cat-assign))))

(defthm fn-scj-seqs-of-update-nth
  (implies (and (< (nfix i) (len c))
                (equal (nfix (fn-record-sequence x)) (nfix (fn-record-sequence (nth i c)))))
           (equal (fn-scj-seqs (update-nth i x c)) (fn-scj-seqs c)))
  :hints (("Goal" :induct (update-nth i x c) :in-theory (enable update-nth))))

(defthm fn-scj-seqs-of-mark
  (implies (natp target)
           (equal (fn-scj-seqs (fn-cat-mark-withdrawn target v by c)) (fn-scj-seqs c)))
  :hints (("Goal" :in-theory (enable fn-cat-mark-withdrawn))))

(defthm fn-scj-seqs-of-withdraw-targets
  (equal (fn-scj-seqs (fn-sca-withdraw-targets targets index by c)) (fn-scj-seqs c))
  :hints (("Goal" :induct (fn-sca-withdraw-targets targets index by c)
           :in-theory (e/d (fn-sca-withdraw-targets) (fn-scj-seqs fn-cat-view-last-visible)))))

; -----------------------------------------------------------------------------
; The bisection over sorted rows is the split.

(defthm fn-scj-split-bound
  (<= (fn-scj-split v xs) (len xs))
  :rule-classes :linear)

(defthm fn-scj-below-split
  (implies (and (natp i) (< i (fn-scj-split v xs)))
           (< (nfix (nth i xs)) (nfix v)))
  :hints (("Goal" :induct (nth i xs) :in-theory (enable nth))))

(defthm fn-scj-sorted-car-le-nth
  (implies (and (fn-scj-nats-sortedp xs) (natp i) (< i (len xs)))
           (<= (nfix (car xs)) (nfix (nth i xs))))
  :hints (("Goal" :induct (nth i xs) :in-theory (enable nth)))
  :rule-classes nil)

(defthm fn-scj-at-or-above-split
  (implies (and (fn-scj-nats-sortedp xs) (natp i)
                (<= (fn-scj-split v xs) i) (< i (len xs)))
           (<= (nfix v) (nfix (nth i xs))))
  :hints (("Goal" :induct (nth i xs) :in-theory (enable nth))
          ("Subgoal *1/2" :use ((:instance fn-scj-sorted-car-le-nth)))
          ("Subgoal *1/1" :use ((:instance fn-scj-sorted-car-le-nth)))))

(defthm fn-scj-natp-split
  (natp (fn-scj-split v xs))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-scj-integerp-of-mid
  (implies (integerp lo) (integerp (fn-scr-mid lo hi)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-scr-mid))))

(defthm fn-scj-seq-bound-is-split
  (implies (and (fn-scj-seqs-sortedp c) (natp v)
                (natp lo) (natp hi) (<= hi (len c))
                (<= lo (fn-scj-split v (fn-scj-seqs c)))
                (<= (fn-scj-split v (fn-scj-seqs c)) hi))
           (equal (fn-scr-seq-bound lo hi v c) (fn-scj-split v (fn-scj-seqs c))))
  :hints (("Goal" :induct (fn-scr-seq-bound lo hi v c)
           :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (e/d (fn-scr-seq-bound)
                           (fn-scj-split fn-scj-seqs fn-scj-nats-sortedp nth len
                            nonnegative-integer-quotient floor mod)))
          ("Subgoal *1/3" :use ((:instance fn-scj-below-split (i (fn-scr-mid lo hi)) (xs (fn-scj-seqs c)))
                                (:instance fn-scj-at-or-above-split (i (fn-scr-mid lo hi)) (xs (fn-scj-seqs c)))
                                (:instance fn-scj-nth-of-seqs (i (fn-scr-mid lo hi)))
                                (:instance fn-scr-mid-bounds) (:instance natp-of-fn-scr-mid)
                                (:instance fn-scj-natp-split (xs (fn-scj-seqs c)))))
          ("Subgoal *1/2" :use ((:instance fn-scj-below-split (i (fn-scr-mid lo hi)) (xs (fn-scj-seqs c)))
                                (:instance fn-scj-at-or-above-split (i (fn-scr-mid lo hi)) (xs (fn-scj-seqs c)))
                                (:instance fn-scj-nth-of-seqs (i (fn-scr-mid lo hi)))
                                (:instance fn-scr-mid-bounds) (:instance natp-of-fn-scr-mid)
                                (:instance fn-scj-natp-split (xs (fn-scj-seqs c)))))))

(defthm fn-scj-split-of-nfix
  (equal (fn-scj-split (nfix v) xs) (fn-scj-split v xs)))

(defthm fn-scj-view-of-is-split
  (implies (fn-scj-seqs-sortedp c)
           (equal (fn-scr-view-of v c) (fn-scj-split v (fn-scj-seqs c))))
  :hints (("Goal" :in-theory (e/d (fn-scr-view-of) (fn-scj-split fn-scj-seqs fn-scj-seqs-sortedp))
           :use ((:instance fn-scj-seq-bound-is-split (v (nfix v)) (lo 0) (hi (len c)))
                 (:instance fn-scj-split-of-nfix (xs (fn-scj-seqs c)))
                 (:instance fn-scj-split-bound (xs (fn-scj-seqs c)))))))

; -----------------------------------------------------------------------------
; The finish, over sequences: T4's marks change none; T2 appends the
; completed row's.  A refused finish changes nothing.

(defthm fn-scj-seqs-of-finish
  (equal (fn-scj-seqs (mv-nth 2 (fn-sca-finish token pending idx targets c)))
         (if (and pending
                  (equal token (fn-pc-token pending))
                  (equal (fn-pc-expected pending) (len c)))
             (append (fn-scj-seqs c) (list (nfix (fn-record-sequence (fn-pc-held pending)))))
           (fn-scj-seqs c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-sca-finish fn-sca-complete fn-cat-complete fn-cat-complete-hidden)
                           (fn-scj-seqs fn-sca-withdraw-targets fn-cat-commit-is-append fn-midx-lookup)))))

(defthm fn-scj-split-of-snoc
  (implies (<= (nfix v) (nfix s))
           (equal (fn-scj-split v (append xs (list s))) (fn-scj-split v xs))))

(defthm fn-scj-nats-sortedp-of-snoc
  (implies (and (fn-scj-nats-sortedp xs) (fn-scj-nats-below xs s))
           (fn-scj-nats-sortedp (append xs (list (nfix s))))))

; P1 kept by the finish.
(defthm fn-scj-seqs-sortedp-of-finish
  (implies (and (fn-scj-seqs-sortedp c)
                (fn-scj-seqs-below c (fn-record-sequence (fn-pc-held pending))))
           (fn-scj-seqs-sortedp (mv-nth 2 (fn-sca-finish token pending idx targets c))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d () (fn-sca-finish fn-scj-seqs fn-scj-nats-sortedp fn-scj-nats-below))
           :use ((:instance fn-scj-nats-sortedp-of-snoc (xs (fn-scj-seqs c))
                            (s (fn-record-sequence (fn-pc-held pending))))))))

; P2: the view a pinned version names does not move.
(defthm fn-scj-view-of-of-finish
  (implies (and (fn-scj-seqs-sortedp c)
                (fn-scj-seqs-below c (fn-record-sequence (fn-pc-held pending)))
                (<= (nfix v) (nfix (fn-record-sequence (fn-pc-held pending)))))
           (equal (fn-scr-view-of v (mv-nth 2 (fn-sca-finish token pending idx targets c)))
                  (fn-scr-view-of v c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d () (fn-sca-finish fn-scj-seqs fn-scj-nats-sortedp fn-scj-nats-below
                               fn-scj-split fn-scj-seqs-sortedp fn-scj-split-of-snoc))
           :use ((:instance fn-scj-seqs-sortedp-of-finish)
                 (:instance fn-scj-view-of-is-split)
                 (:instance fn-scj-split-of-snoc (xs (fn-scj-seqs c))
                            (s (nfix (fn-record-sequence (fn-pc-held pending)))))
                 (:instance fn-scj-view-of-is-split (c (mv-nth 2 (fn-sca-finish token pending idx targets c))))))))

; P3: the number table stays fresh.
(defthm fn-scj-freshp-of-withdraw-targets
  (implies (fn-cnx-freshp c)
           (fn-cnx-freshp (fn-sca-withdraw-targets targets index by c)))
  :hints (("Goal" :induct (fn-sca-withdraw-targets targets index by c)
           :in-theory (e/d (fn-sca-withdraw-targets) (fn-cnx-freshp fn-cat-view-last-visible fn-cat-withdraw-is-mark)))))

(defthm fn-scj-freshp-of-finish
  (implies (fn-cnx-freshp c)
           (fn-cnx-freshp (mv-nth 2 (fn-sca-finish token pending idx targets c))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-sca-finish fn-sca-complete fn-cat-complete fn-cat-complete-hidden)
                           (fn-cnx-freshp fn-sca-withdraw-targets fn-cat-commit-is-append fn-midx-lookup)))))

(in-theory (disable fn-scj-view-of-is-split fn-scj-seqs-of-finish))

; -----------------------------------------------------------------------------
; P4: a pinned reader's catalog fact survives the finish.

(defthm fn-scj-view-of-bound
  (<= (fn-scr-view-of v c) (len c))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-scr-view-of))))

(defthm fn-scj-view-articles-of-finish-at-view-of
  (implies (and (fn-scj-seqs-sortedp fn-cat)
                (fn-scj-seqs-below fn-cat (fn-record-sequence (fn-pc-held pending)))
                (<= (nfix v) (nfix (fn-record-sequence (fn-pc-held pending)))))
           (equal (fn-cat-view-articles (fn-scr-view-of v (mv-nth 2 (fn-sca-finish token pending idx targets fn-cat)))
                                        fn-arena (mv-nth 2 (fn-sca-finish token pending idx targets fn-cat)))
                  (fn-cat-view-articles (fn-scr-view-of v fn-cat) fn-arena fn-cat)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-scj-view-of-of-finish fn-scj-view-of-bound natp-of-fn-scr-view-of
                                        fn-cat-count-is-len)
                                      (theory 'minimal-theory))
           :use ((:instance fn-sca-finish-keeps-pinned-views
                            (v (fn-scr-view-of v fn-cat)) (view-index idx))))))

; KEYSTONE (a pinned catalog view survives the host's finish).  Any reader
; pinned at a version V -- a connection, the live view, a captured reader
; view -- whose archive and index satisfy the -cat keystone's hypothesis at
; fn-scr-view-of V keeps it over the catalog fn-sca-finish leaves, when the
; catalog's rows are sorted by sequence, every row's sequence is below the
; completed row's, and V is at most the completed row's sequence.  A refused
; finish leaves the catalog as it was.
(defthm fn-scj-catalogp-of-finish
  (let ((c2 (mv-nth 2 (fn-sca-finish token pending idx targets fn-cat))))
    (implies (and (fn-scr-catalogp archive index (fn-scr-view-of v fn-cat) fn-arena fn-cat)
                  (fn-scj-seqs-sortedp fn-cat)
                  (fn-scj-seqs-below fn-cat (fn-record-sequence (fn-pc-held pending)))
                  (<= (nfix v) (nfix (fn-record-sequence (fn-pc-held pending)))))
             (fn-scr-catalogp archive index (fn-scr-view-of v c2) fn-arena c2)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-scr-catalogp) (theory 'minimal-theory))
           :use ((:instance fn-scj-view-articles-of-finish-at-view-of)
                 (:instance fn-scj-freshp-of-finish (c fn-cat))))))

(defthm fn-scj-conn-pinp-of-finish
  (let ((c2 (mv-nth 2 (fn-sca-finish token pending idx targets fn-cat))))
    (implies (and (fn-scj-conn-pinp conn fn-arena fn-cat)
                  (fn-scj-seqs-sortedp fn-cat)
                  (fn-scj-seqs-below fn-cat (fn-record-sequence (fn-pc-held pending)))
                  (<= (nfix (fn-own-conn-version conn)) (nfix (fn-record-sequence (fn-pc-held pending)))))
             (fn-scj-conn-pinp conn fn-arena c2)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-scj-conn-pinp) (theory 'minimal-theory))
           :use ((:instance fn-scj-catalogp-of-finish
                            (archive (fn-own-conn-archive conn))
                            (index (fn-scj-conn-pinned-index conn))
                            (v (fn-own-conn-version conn)))))))

; Every connection pinned at or below N.
(defun fn-scj-conns-versions-atmostp (conns n)
  (declare (xargs :guard t))
  (if (consp conns)
      (and (<= (nfix (fn-own-conn-version (car conns))) (nfix n))
           (fn-scj-conns-versions-atmostp (cdr conns) n))
    t))

(defthm fn-scj-conns-pinp-of-finish
  (let ((c2 (mv-nth 2 (fn-sca-finish token pending idx targets fn-cat))))
    (implies (and (fn-scj-conns-pinp conns fn-arena fn-cat)
                  (fn-scj-seqs-sortedp fn-cat)
                  (fn-scj-seqs-below fn-cat (fn-record-sequence (fn-pc-held pending)))
                  (fn-scj-conns-versions-atmostp conns (fn-record-sequence (fn-pc-held pending))))
             (fn-scj-conns-pinp conns fn-arena c2)))
  :hints (("Goal" :induct (fn-scj-conns-versions-atmostp conns (fn-record-sequence (fn-pc-held pending)))
           :in-theory (union-theories '(fn-scj-conns-pinp fn-scj-conns-versions-atmostp
                                        fn-scj-conn-pinp-of-finish
                                        (:induction fn-scj-conns-versions-atmostp))
                                      (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; P1 at every open.

(defthm fn-scj-nats-below-monotone
  (implies (and (fn-scj-nats-below xs v) (<= (nfix v) (nfix w)))
           (fn-scj-nats-below xs w)))

(defthm fn-scj-nats-below-of-append
  (equal (fn-scj-nats-below (append a b) v)
         (and (fn-scj-nats-below a v) (fn-scj-nats-below b v))))

(defthm fn-scj-seqs-of-with-withdrawn
  (equal (fn-record-sequence (fn-held-with-withdrawn h w)) (fn-record-sequence h)))

(local (defun-nx fn-scj-load-seq-ind (rows idx c k)
  (declare (xargs :verify-guards nil))
  (if (consp rows)
      (fn-scj-load-seq-ind (cdr rows) idx (fn-sca-load-held-row (car rows) idx c) (+ 1 (nfix k)))
    (list idx c k))))

(defthm fn-scj-seqs-sorted-of-load-held-row
  (implies (and (fn-scj-seqs-sortedp c) (fn-scj-seqs-below c k) (natp k)
                (fn-store-event-p r) (equal (fn-store-event-sequence r) k)
                (fn-row-composite-okp r fn-arena))
           (and (fn-scj-seqs-sortedp (fn-sca-load-held-row r idx c))
                (fn-scj-seqs-below (fn-sca-load-held-row r idx c) (+ 1 k))))
  :hints (("Goal" :do-not-induct t
           :cases ((fn-scj-load-h r))
           :expand ((:free (x v) (fn-scj-nats-below (list x) v)) (:free (v) (fn-scj-nats-below nil v)))
           :in-theory (e/d (fn-scj-load-held-row-is)
                           (fn-sca-load-held-row fn-scj-load-h fn-cat-commit-is-append fn-midx-lookup
                            fn-store-event-p fn-store-event-sequence fn-row-composite-okp
                            fn-scj-seqs fn-scj-nats-sortedp fn-scj-nats-below))
           :use ((:instance fn-scj-load-h-sequence)
                 (:instance fn-scj-nats-sortedp-of-snoc (xs (fn-scj-seqs c)) (s k))))))

(defthm fn-scj-seqs-sorted-of-load-from
  (implies (and (fn-scj-seqs-sortedp c) (fn-scj-seqs-below c k) (natp k)
                (fn-scj-seqs-from rows k) (fn-rows-composites-okp rows fn-arena))
           (and (fn-scj-seqs-sortedp (fn-sca-load-held-rows-from rows idx c))
                (fn-scj-seqs-below (fn-sca-load-held-rows-from rows idx c) (+ k (len rows)))))
  :hints (("Goal" :induct (fn-scj-load-seq-ind rows idx c k)
           :expand ((fn-scj-seqs-from rows k) (fn-sca-load-held-rows-from rows idx c)
                    (fn-rows-composites-okp rows fn-arena))
           :in-theory (disable fn-sca-load-held-row fn-scj-load-h fn-scj-load-held-row-is
                               fn-store-event-p fn-store-event-sequence fn-row-composite-okp
                               fn-scj-seqs-sortedp fn-scj-seqs-below-is-nats-below
                               fn-scj-seqs-from fn-sca-load-held-rows-from fn-rows-composites-okp))))

(defthm fn-scj-seqs-sortedp-of-nil
  (fn-scj-seqs-sortedp nil))

(defthm fn-scj-seqs-from-at-related-store
  (implies (fn-cst-relation st)
           (fn-scj-seqs-from (fn-sf-records (fn-sn-files st)) 0))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cst-relation fn-cst-recoverablep fn-cst-replay-node)
                           (fn-cpr-replay fn-sn-statep fn-sn-observed-historyp fn-cst-final-configurationp
                            fn-node-statep fn-replay-advance-txid fn-replay-advance-okp fn-cnode-statep
                            fn-scj-seqs-from fn-cst-pending-linkp fn-cst-deferred-linkp))
           :use ((:instance fn-scj-seqs-from-of-cpr-replay
                            (configs (fn-sn-config-history st))
                            (events (fn-sf-records (fn-sn-files st))))))))

(defthm fn-scj-seqs-sortedp-of-load
  (implies (and (fn-scj-seqs-from rows 0) (fn-rows-composites-okp rows fn-arena))
           (fn-scj-seqs-sortedp (fn-sca-load-held-rows rows idx fn-arena fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-sca-load-held-rows) (fn-sca-load-held-rows-from fn-scj-seqs-sortedp))
           :use ((:instance fn-scj-seqs-sorted-of-load-from (c nil) (k 0))))))

; P1 at every open: the catalog the host loads from a related store's rows
; (fn-sca-load-held-rows, as the full open and the recover install it) is
; sorted by sequence.
(defthm fn-scj-seqs-sortedp-at-open
  (let ((rows (fn-sf-records (fn-sn-files st))))
    (implies (and (fn-cst-relation st) (fn-rows-composites-okp rows fn-arena))
             (fn-scj-seqs-sortedp (fn-sca-load-held-rows rows idx fn-arena fn-cat))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance fn-scj-seqs-from-at-related-store)
                 (:instance fn-scj-seqs-sortedp-of-load (rows (fn-sf-records (fn-sn-files st))))))))

; -----------------------------------------------------------------------------
; At the host's finish: the completed row's sequence is the length of the
; history before it, and the connections are the owner's before.

(defthm fn-scj-seqs-from-snoc-last
  (implies (and (fn-scj-seqs-from (append a (list e)) k) (natp k))
           (and (fn-store-event-p e)
                (equal (fn-store-event-sequence e) (+ k (len a)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-scj-seqs-from a k)
           :in-theory (disable fn-store-event-p fn-store-event-sequence))))

(defthm fn-scj-composites-okp-snoc-last
  (implies (fn-rows-composites-okp (append a (list e)) fn-arena)
           (fn-row-composite-okp e fn-arena))
  :rule-classes nil
  :hints (("Goal" :induct (len a) :in-theory (e/d (fn-rows-composites-okp) (fn-row-composite-okp)))))

; The completed row's sequence is its event's position: the length of the
; history before it.
(defthm fn-scj-held-sequence-at-host-finish
  (implies (and (fn-cst-relation s2)
                (equal (fn-sf-records (fn-sn-files s2)) (append events0 (list event)))
                (fn-rows-composites-okp (append events0 (list event)) fn-arena)
                (fn-scj-load-h event))
           (equal (fn-record-sequence (fn-scj-load-h event)) (len events0)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fix natp (:type-prescription len) unicity-of-0 commutativity-of-+)
                                      (theory 'minimal-theory))
           :use ((:instance fn-scj-seqs-from-at-related-store (st s2))
                 (:instance fn-scj-seqs-from-snoc-last (a events0) (e event) (k 0))
                 (:instance fn-scj-composites-okp-snoc-last (a events0) (e event))
                 (:instance fn-scj-load-h-sequence (r event))))))

(defthm fn-scj-own-refresh-conns
  (equal (fn-own-conns (fn-own-refresh x)) (fn-own-conns x))
  :hints (("Goal" :in-theory (e/d (fn-own-refresh)
                                  (fn-own-store-idlep fn-ctl-refresh-visible fn-ctl-refresh-withdrawals
                                   fn-ctl-refresh-withdrawn fn-midx-refresh fn-gidx-refresh
                                   fn-ctl-visible-state-of fn-own-view-make-visible)))))

(defthm fn-scj-conns-of-host-finish
  (equal (fn-own-conns (cdr (fn-ccar-own-finish o cfg fn-arena))) (fn-own-conns o))
  :hints (("Goal" :in-theory (union-theories '(fn-ccar-own-finish fn-ccar-own-complete-enabled
                                               fn-scj-own-refresh-conns fn-own-conns-of-fn-own-make
                                               cdr-cons)
                                             (theory 'minimal-theory)))))

(defthm fn-scj-conns-versions-atmostp-monotone
  (implies (and (fn-scj-conns-versions-atmostp conns m) (<= (nfix m) (nfix n)))
           (fn-scj-conns-versions-atmostp conns n)))

(defthm fn-scj-held-p-non-nil
  (implies (fn-held-p h) h)
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-held-p-forward-natural-head (x h))))))

; KEYSTONE (P4 at the host's call).  Over the owner host/owner-host.lisp
; fn-owner-finish-submission installs (fn-ccar-own-finish) and the catalog
; it computes over that owner's view: every connection pinned over the
; catalog at or below the old view's version stays pinned, and the rows stay
; sorted.  The completed row's sequence is len EVENTS0 (the replay's
; positions), which bounds the view's version and every pin.
(defthm fn-scj-conns-pinp-at-host-finish
  (let* ((view (fn-own-view o))
         (o2 (cdr (fn-ccar-own-finish o cfg fn-arena)))
         (s2 (fn-own-store o2))
         (view2 (fn-own-view o2))
         (held (fn-pc-held pending))
         (c2 (mv-nth 2 (fn-sca-finish token pending (fn-own-view-index view2)
                                      (fn-sca-targets-of (fn-record-msgid held)
                                                         (fn-own-view-withdrawals view2))
                                      fn-cat))))
    (implies (and (fn-scj-conns-pinp (fn-own-conns o) fn-arena fn-cat)
                  (fn-scj-conns-versions-atmostp (fn-own-conns o) (fn-own-view-version view))
                  (fn-scj-seqs-sortedp fn-cat)
                  (fn-scj-joinp view fn-arena fn-cat)
                  (<= (nfix (fn-own-view-version view)) (len events0))
                  (fn-cst-relation s2)
                  (equal (fn-sf-records (fn-sn-files s2)) (append events0 (list event)))
                  (fn-rows-composites-okp (append events0 (list event)) fn-arena)
                  (equal (fn-scj-load-h event) held)
                  (fn-pc-p pending))
             (and (fn-scj-conns-pinp (fn-own-conns o2) fn-arena c2)
                  (fn-scj-seqs-sortedp c2))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-scj-joinp fn-scj-conns-of-host-finish nfix fix
                                        (:type-prescription len))
                                      (theory 'minimal-theory))
           :use ((:instance fn-pc-p-fields (pc pending))
                 (:instance fn-scj-held-p-non-nil (h (fn-pc-held pending)))
                 (:instance fn-scj-held-sequence-at-host-finish
                            (s2 (fn-own-store (cdr (fn-ccar-own-finish o cfg fn-arena)))))
                 (:instance fn-scj-seqs-below-monotone (c fn-cat)
                            (v1 (fn-own-view-version (fn-own-view o))) (v2 (len events0)))
                 (:instance fn-scj-conns-versions-atmostp-monotone (conns (fn-own-conns o))
                            (m (fn-own-view-version (fn-own-view o))) (n (len events0)))
                 (:instance fn-scj-conns-pinp-of-finish (conns (fn-own-conns o))
                            (idx (fn-own-view-index (fn-own-view (cdr (fn-ccar-own-finish o cfg fn-arena)))))
                            (targets (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                        (fn-own-view-withdrawals
                                                         (fn-own-view (cdr (fn-ccar-own-finish o cfg fn-arena)))))))
                 (:instance fn-scj-seqs-sortedp-of-finish (c fn-cat)
                            (idx (fn-own-view-index (fn-own-view (cdr (fn-ccar-own-finish o cfg fn-arena)))))
                            (targets (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                        (fn-own-view-withdrawals
                                                         (fn-own-view (cdr (fn-ccar-own-finish o cfg fn-arena)))))))))))

; -----------------------------------------------------------------------------
; P5: connections pinned to the current view (open, advance), and the live
; view from the join.

(defun-nx fn-scj-conn-on-viewp (conn view)
  (and (equal (fn-own-conn-archive conn) (fn-own-view-archive view))
       (equal (fn-own-conn-index conn) (fn-own-view-index view))
       (equal (fn-own-conn-group-index conn) (fn-own-view-group-index view))
       (equal (fn-own-conn-control conn) (fn-own-view-control view))
       (equal (fn-own-conn-version conn) (fn-own-view-version view))))

(defthm fn-scj-conn-pinp-when-on-view
  (implies (fn-scj-conn-on-viewp conn view)
           (equal (fn-scj-conn-pinp conn fn-arena fn-cat)
                  (fn-scj-live-okp view fn-arena fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-scj-conn-on-viewp fn-scj-conn-pinp fn-scj-conn-pinned-index
                                   fn-scj-live-okp fn-scr-live-catalogp fn-scr-fields-catalogp
                                   fn-served-pinned-version fn-served-pinned-make)
                                  (fn-scr-catalogp fn-scr-view-of fn-own-view-live
                                   fn-own-conn-archive fn-own-conn-index fn-own-conn-group-index
                                   fn-own-conn-control fn-own-conn-version)))))

(defthm fn-scj-open-conn-on-view
  (implies (< (len (fn-own-conns o)) (nfix (fn-own-max-conns o)))
           (fn-scj-conn-on-viewp (car (fn-own-conns (cdr (fn-own-open o acfg)))) (fn-own-view o)))
  :hints (("Goal" :in-theory (e/d (fn-own-open fn-scj-conn-on-viewp)
                                  (fn-served-open-group-indexed fn-own-view-control
                                   fn-own-conn-make-group-indexed)))))

(defthm fn-scj-conns-pinp-of-open
  (implies (and (fn-scj-conns-pinp (fn-own-conns o) fn-arena fn-cat)
                (fn-scj-live-okp (fn-own-view o) fn-arena fn-cat))
           (fn-scj-conns-pinp (fn-own-conns (cdr (fn-own-open o acfg))) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-own-open fn-scj-conns-pinp)
                                  (fn-served-open-group-indexed fn-own-view-control fn-scj-conn-pinp
                                   fn-scj-live-okp fn-own-conn-make-group-indexed fn-scj-conn-pinp-when-on-view))
           :use ((:instance fn-scj-open-conn-on-view)
                 (:instance fn-scj-conn-pinp-when-on-view
                            (conn (car (fn-own-conns (cdr (fn-own-open o acfg)))))
                            (view (fn-own-view o)))))))

(defthm fn-scj-conns-pinp-of-replace
  (implies (and (fn-scj-conns-pinp conns fn-arena fn-cat)
                (fn-scj-conn-pinp conn fn-arena fn-cat))
           (fn-scj-conns-pinp (fn-own-replace-conn conn conns) fn-arena fn-cat))
  :hints (("Goal" :induct (fn-own-replace-conn conn conns)
           :in-theory (e/d (fn-scj-conns-pinp) (fn-scj-conn-pinp)))))


(defthm fn-scj-conn-pinp-of-make-on-view
  (equal (fn-scj-conn-pinp (fn-own-conn-make-group-indexed id (fn-own-view-version view) frontier wire session
                                                           (fn-own-view-archive view) config observation verdicts
                                                           (fn-own-view-index view) (fn-own-view-group-index view)
                                                           (fn-own-view-control view))
                           fn-arena fn-cat)
         (fn-scj-live-okp view fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-scj-conn-on-viewp) (fn-own-conn-make-group-indexed fn-scj-conn-pinp
                                                          fn-scj-live-okp fn-own-view-control))
           :use ((:instance fn-scj-conn-pinp-when-on-view
                            (conn (fn-own-conn-make-group-indexed id (fn-own-view-version view) frontier wire session
                                                                  (fn-own-view-archive view) config observation verdicts
                                                                  (fn-own-view-index view) (fn-own-view-group-index view)
                                                                  (fn-own-view-control view))))))))

(defthm fn-scj-conns-pinp-of-advance
  (implies (and (fn-scj-conns-pinp (fn-own-conns o) fn-arena fn-cat)
                (fn-scj-live-okp (fn-own-view o) fn-arena fn-cat))
           (fn-scj-conns-pinp (fn-own-conns (fn-own-advance o id)) fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-own-advance fn-own-advance-result fn-own-set-conns)
                                  (fn-own-conn-boundedp fn-own-view-control fn-scj-conn-pinp fn-scj-live-okp
                                   fn-own-conn-make-group-indexed fn-scj-conns-pinp
                                   fn-own-replace-conn fn-own-find-conn fn-own-view-group-index)))))

; The live view from the join: the view at the view's version is the whole
; catalog (every row's sequence below it), which the join says is the
; visible archive; the index facts are the view's own.
(defthm fn-scj-live-okp-of-joinp
  (let ((view (fn-own-view o)))
    (implies (and (fn-scj-joinp view fn-arena fn-cat)
                  (fn-cnx-freshp fn-cat)
                  (fn-nntp-projectionp (fn-own-view-archive view))
                  (fn-own-view-okp view groups capacity records))
             (fn-scj-live-okp view fn-arena fn-cat)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-scj-joinp fn-scj-live-okp fn-scr-live-catalogp fn-scr-fields-catalogp
                            fn-served-pinned-version fn-served-pinned-make fn-scr-catalogp
                            fn-gidx-pin-correspondencep fn-own-view-okp)
                           (fn-scr-view-of fn-own-view-live fn-cat-view-articles fn-cnx-freshp
                            fn-nntp-projectionp fn-midx-build fn-gidx-build fn-gidx-pinp
                            fn-scj-seqs-below-is-nats-below fn-own-prefix-archive
                            fn-ctl-visible-state fn-ctl-subseq-diff fn-own-view-control))
           :use ((:instance fn-scj-view-of-when-seqs-below
                            (version (fn-own-view-version (fn-own-view o))))))))

; KEYSTONE (the chain premise at the host's finish).  Under step 2's
; hypotheses (fn-scj-joinp-at-host-finish), with the catalog sorted and
; fresh before, every connection pinned over it at or below the view's
; version, the finished owner's view in fn-own-view-okp (fn-own-relation's
; view conjunct: its index and group index are the visible archive's) and its
; archive a projection (NAMED: no owner predicate found that carries
; fn-nntp-projectionp of the view's archive), the catalog the host's finish leaves carries the live view,
; every pinned connection and sortedness: fn-scr-owner-catalogp at every
; connection identifier.
(defthm fn-scj-owner-catalogp-at-host-finish
  (let* ((view (fn-own-view o))
         (o2 (cdr (fn-ccar-own-finish o cfg fn-arena)))
         (s2 (fn-own-store o2))
         (view2 (fn-own-view o2))
         (acc2 (fn-node-acceptance (fn-sn-node s2)))
         (a (car (fn-state-articles acc2)))
         (events2 (append events0 (list event)))
         (held (fn-pc-held pending))
         (c2 (mv-nth 2 (fn-sca-finish token pending (fn-own-view-index view2)
                                      (fn-sca-targets-of (fn-record-msgid held)
                                                         (fn-own-view-withdrawals view2))
                                      fn-cat))))
    (implies (and (fn-ccar-completion-enabledp (fn-own-store o))
                  (fn-scj-joinp view fn-arena fn-cat)
                  (fn-scar-view-indexedp o)
                  (fn-scj-rows-invp fn-cat events0)
                  (fn-cst-relation s2)
                  (fn-own-store-idlep s2)
                  (equal (fn-sf-records (fn-sn-files s2)) events2)
                  (fn-rows-composites-okp events2 fn-arena)
                  (fn-scj-rows-clearp events2)
                  (equal (fn-scj-load-h event) held)
                  (fn-pc-p pending)
                  (equal token (fn-pc-token pending))
                  (equal (fn-pc-expected pending) (len fn-cat))
                  (equal (fn-state-articles acc2) (cons a (fn-own-view-raw view)))
                  (equal (fn-sn-verdicts s2)
                         (cons (cons (fn-article-msgid a) verdict) (fn-own-view-verdicts view)))
                  (equal (fn-state-articles (fn-own-view-archive view))
                         (fn-ctl-visible-articles (fn-own-view-raw view)
                                                  (fn-own-view-withdrawals view)
                                                  (fn-own-view-verdicts view)))
                  (equal (fn-state-articles (fn-own-view-archive view2))
                         (fn-ctl-visible-articles (fn-state-articles acc2)
                                                  (fn-own-view-withdrawals view2)
                                                  (fn-own-view-verdicts view2)))
                  (<= (nfix (fn-own-view-version view)) (len events0))
                  ;; step 3
                  (fn-scj-seqs-sortedp fn-cat)
                  (fn-cnx-freshp fn-cat)
                  (fn-scj-conns-pinp (fn-own-conns o) fn-arena fn-cat)
                  (fn-scj-conns-versions-atmostp (fn-own-conns o) (fn-own-view-version view))
                  (fn-own-view-okp view2 (fn-sn-groups s2) (fn-sn-capacity s2)
                                   (fn-sf-records (fn-sn-files s2)))
                  (fn-nntp-projectionp (fn-own-view-archive view2)))
             (and (fn-scr-owner-catalogp o2 id fn-arena c2)
                  (fn-scj-conns-pinp (fn-own-conns o2) fn-arena c2)
                  (fn-scj-live-okp view2 fn-arena c2)
                  (fn-scj-seqs-sortedp c2)
                  (fn-cnx-freshp c2))))
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance fn-scj-joinp-at-host-finish)
                 (:instance fn-scj-conns-pinp-at-host-finish)
                 (:instance fn-scj-freshp-of-finish (c fn-cat)
                            (idx (fn-own-view-index (fn-own-view (cdr (fn-ccar-own-finish o cfg fn-arena)))))
                            (targets (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                        (fn-own-view-withdrawals
                                                         (fn-own-view (cdr (fn-ccar-own-finish o cfg fn-arena)))))))
                 (:instance fn-scj-live-okp-of-joinp
                            (o (cdr (fn-ccar-own-finish o cfg fn-arena)))
                            (fn-cat (mv-nth 2 (fn-sca-finish token pending
                                                             (fn-own-view-index (fn-own-view (cdr (fn-ccar-own-finish o cfg fn-arena))))
                                                             (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                                                (fn-own-view-withdrawals
                                                                                 (fn-own-view (cdr (fn-ccar-own-finish o cfg fn-arena)))))
                                                             fn-cat)))
                            (groups (fn-sn-groups (fn-own-store (cdr (fn-ccar-own-finish o cfg fn-arena)))))
                            (capacity (fn-sn-capacity (fn-own-store (cdr (fn-ccar-own-finish o cfg fn-arena)))))
                            (records (fn-sf-records (fn-sn-files (fn-own-store (cdr (fn-ccar-own-finish o cfg fn-arena)))))))
                 (:instance fn-scj-owner-catalogp-of-conns-and-live
                            (o (cdr (fn-ccar-own-finish o cfg fn-arena)))
                            (fn-cat (mv-nth 2 (fn-sca-finish token pending
                                                             (fn-own-view-index (fn-own-view (cdr (fn-ccar-own-finish o cfg fn-arena))))
                                                             (fn-sca-targets-of (fn-record-msgid (fn-pc-held pending))
                                                                                (fn-own-view-withdrawals
                                                                                 (fn-own-view (cdr (fn-ccar-own-finish o cfg fn-arena)))))
                                                             fn-cat))))))))
