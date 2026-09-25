; fn: the visible article list, maintained incrementally (packet C3, D27).
;
; `fn-ctl-visible-articles' (books/control-authority.lisp) is the article
; list a newly published reader view serves: every article but a target some
; withdrawal record, whose cause is in the same list, withdraws.  Computing
; it afresh walks every article against every record, per refresh; the
; served path may not do that ("no whole-state revalidation on a served
; path", AGENTS.md; D27).  This book is the incremental form the committed
; view's refresh is to carry: the visible list of (A . OLD) from the visible
; list of OLD, and a batch of new articles folded one at a time, with the
; correspondence theorem that makes the carried list equal the definition.
;
; Work per new article A (WS the records, N the visible list):
;   - one pass over WS for records whose cause is A (`fn-ctl-causes-p');
;   - one pass over WS for records whose target is A, each probing the
;     article list for its cause (`fn-ctl-withdrawn-by-p' on A only);
;   - a pass over N only when A is the cause of some record (A is a cancel
;     with a decided withdrawal), dropping what A's records withdraw.
; So an ordinary article costs O(|WS|) and no walk of the archive; a cancel
; costs O(N x |WS|) once.  The cause probe is a list walk here; the owner
; wiring answers it from the Message-ID trie (fn-midx-lookup-of-build-is-
; find-article).  Pessimistic figure: an archive of N articles and R
; records costs N x R per executed cancel and R per other article.
;
; Prefix `fn-ctl-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "control-authority")

; Some record in WS whose cause is CAUSE withdraws X.
(defun fn-ctl-withdrawn-via-p (x ws cause verdicts)
  (declare (xargs :guard t))
  (if (consp ws)
      (let ((w (car ws)))
        (or (and (fn-ctl-withdrawalp w)
                 (consp x)
                 (equal (fn-ctl-w-target w) (fn-article-msgid x))
                 (equal (fn-ctl-w-cause w) cause)
                 (fn-ctl-effect-withdrawsp
                  (fn-ctl-withdrawal-effect
                   w (fn-article-groups x)
                   (fn-ctl-lookup-verdict (fn-article-msgid x) verdicts))))
            (fn-ctl-withdrawn-via-p x (cdr ws) cause verdicts)))
    nil))

; Does any record name CAUSE as its cause?
(defun fn-ctl-causes-p (ws cause)
  (declare (xargs :guard t))
  (if (consp ws)
      (or (and (fn-ctl-withdrawalp (car ws))
               (equal (fn-ctl-w-cause (car ws)) cause))
          (fn-ctl-causes-p (cdr ws) cause))
    nil))

; XS without what the records caused by CAUSE withdraw.
(defun fn-ctl-drop-via (xs ws cause verdicts)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (fn-ctl-withdrawn-via-p (car xs) ws cause verdicts)
          (fn-ctl-drop-via (cdr xs) ws cause verdicts)
        (cons (car xs) (fn-ctl-drop-via (cdr xs) ws cause verdicts)))
    nil))

; One new article A over OLD, whose visible list is OLD-VISIBLE.
(defun fn-ctl-visible-add (a old-visible old ws verdicts)
  (declare (xargs :guard t))
  (if (consp a)
      (let ((kept (if (fn-ctl-causes-p ws (fn-article-msgid a))
                      (fn-ctl-drop-via old-visible ws (fn-article-msgid a)
                                       verdicts)
                    old-visible)))
        (if (fn-ctl-withdrawn-by-p a ws (cons a old) verdicts)
            kept
          (cons a kept)))
    (cons a old-visible)))

; `append' with guard t (the same logical definition).
(defun fn-ctl-prepend (xs ys)
  (declare (xargs :guard t))
  (if (consp xs) (cons (car xs) (fn-ctl-prepend (cdr xs) ys)) ys))

(defthm fn-ctl-prepend-is-append
  (equal (fn-ctl-prepend xs ys) (append xs ys)))

; A batch DELTA (newest first, as the acceptance archive conses) over OLD.
(defun fn-ctl-visible-extend (delta old-visible old ws verdicts)
  (declare (xargs :guard t))
  (if (consp delta)
      (fn-ctl-visible-add (car delta)
                          (fn-ctl-visible-extend (cdr delta) old-visible old
                                                 ws verdicts)
                          (fn-ctl-prepend (cdr delta) old) ws verdicts)
    old-visible))

; -----------------------------------------------------------------------------
; The correspondence.

(defthm fn-ctl-has-msgid-p-of-cons
  (equal (fn-ctl-has-msgid-p m (cons a arts))
         (or (and (consp a) (equal (fn-article-msgid a) m))
             (fn-ctl-has-msgid-p m arts))))

(defthm fn-ctl-withdrawn-by-p-of-cons-article
  (iff (fn-ctl-withdrawn-by-p x ws (cons a arts) verdicts)
       (or (fn-ctl-withdrawn-by-p x ws arts verdicts)
           (and (consp a)
                (fn-ctl-withdrawn-via-p x ws (fn-article-msgid a) verdicts))))
  :hints (("Goal" :induct (fn-ctl-withdrawn-by-p x ws arts verdicts)
           :in-theory (disable fn-ctl-withdrawal-effect
                               fn-ctl-effect-withdrawsp
                               fn-ctl-withdrawalp
                               fn-ctl-has-msgid-p))))

(defthm fn-ctl-drop-via-of-cons
  (equal (fn-ctl-drop-via (cons x xs) ws cause verdicts)
         (if (fn-ctl-withdrawn-via-p x ws cause verdicts)
             (fn-ctl-drop-via xs ws cause verdicts)
           (cons x (fn-ctl-drop-via xs ws cause verdicts)))))

(defthm fn-ctl-drop-via-of-atom
  (implies (not (consp xs))
           (equal (fn-ctl-drop-via xs ws cause verdicts) nil)))

(defthm fn-ctl-visible-filter-of-cons-article
  (implies (consp a)
           (equal (fn-ctl-visible-filter xs ws (cons a arts) verdicts)
                  (fn-ctl-drop-via (fn-ctl-visible-filter xs ws arts verdicts)
                                   ws (fn-article-msgid a) verdicts)))
  :hints (("Goal" :induct (fn-ctl-visible-filter xs ws arts verdicts)
           :in-theory (disable fn-ctl-withdrawn-by-p fn-ctl-withdrawn-via-p
                               fn-ctl-drop-via))))

(defthm fn-ctl-visible-filter-of-cons-atom
  (implies (not (consp a))
           (equal (fn-ctl-visible-filter xs ws (cons a arts) verdicts)
                  (fn-ctl-visible-filter xs ws arts verdicts)))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-by-p))))

(defthm fn-ctl-withdrawn-via-p-needs-a-cause
  (implies (not (fn-ctl-causes-p ws cause))
           (not (fn-ctl-withdrawn-via-p x ws cause verdicts)))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawal-effect
                                      fn-ctl-effect-withdrawsp))))

(defthm fn-ctl-drop-via-without-a-cause
  (implies (and (not (fn-ctl-causes-p ws cause))
                (true-listp xs))
           (equal (fn-ctl-drop-via xs ws cause verdicts) xs)))

(defthm fn-ctl-true-listp-of-visible-filter
  (true-listp (fn-ctl-visible-filter xs ws arts verdicts))
  :rule-classes (:rewrite :type-prescription))

(defthm fn-ctl-withdrawn-by-p-of-an-atom
  (implies (not (consp a))
           (not (fn-ctl-withdrawn-by-p a ws arts verdicts))))

; KEYSTONE (C3, D27).  The carried visible list after one new article is the
; definition's visible list of the grown archive, whenever the carried list
; before it was the definition's: the refresh never needs the whole-archive
; filter to stay correct.
(defthm fn-ctl-visible-add-is-visible
  (implies (equal old-visible (fn-ctl-visible-articles old ws verdicts))
           (equal (fn-ctl-visible-add a old-visible old ws verdicts)
                  (fn-ctl-visible-articles (cons a old) ws verdicts)))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-by-p
                                      fn-ctl-withdrawn-via-p
                                      fn-ctl-drop-via fn-ctl-causes-p))))

; KEYSTONE (C3, D27).  The same for a batch, the shape the owner's refresh
; sees between two idle phases: the new archive is DELTA consed onto OLD.
(defthm fn-ctl-visible-extend-is-visible
  (implies (equal old-visible (fn-ctl-visible-articles old ws verdicts))
           (equal (fn-ctl-visible-extend delta old-visible old ws verdicts)
                  (fn-ctl-visible-articles (append delta old) ws verdicts)))
  :hints (("Goal" :induct (fn-ctl-visible-extend delta old-visible old ws
                                                 verdicts)
           :in-theory (disable fn-ctl-visible-add fn-ctl-visible-articles))))

; -----------------------------------------------------------------------------
; The state a view serves (C3 owner wiring).  `fn-ctl-visible-state' is the
; acceptance state A with its article list replaced by the visible list:
; groups, watermarks, next txid, pending and fence unchanged, so no local
; number is reused and nothing is added or reordered.

(defun fn-ctl-visible-state-of (a visible)
  (declare (xargs :guard t))
  (fn-make-state (fn-state-groups a) (fn-state-nexts a) visible
                 (fn-state-next-txid a) (fn-state-pending a)
                 (fn-state-fenced a)))
(defun fn-ctl-visible-state (a ws verdicts)
  (declare (xargs :guard t))
  (fn-ctl-visible-state-of
   a (fn-ctl-visible-articles (fn-state-articles a) ws verdicts)))

(defthm fn-ctl-visible-state-of-fields
  (and (equal (fn-state-groups (fn-ctl-visible-state-of a vis)) (fn-state-groups a))
       (equal (fn-state-nexts (fn-ctl-visible-state-of a vis)) (fn-state-nexts a))
       (equal (fn-state-articles (fn-ctl-visible-state-of a vis)) vis)
       (equal (fn-state-next-txid (fn-ctl-visible-state-of a vis)) (fn-state-next-txid a))
       (equal (fn-state-pending (fn-ctl-visible-state-of a vis)) (fn-state-pending a))
       (equal (fn-state-fenced (fn-ctl-visible-state-of a vis)) (fn-state-fenced a))))

(defthm fn-ctl-pair-memberp-of-append
  (iff (fn-pair-memberp p (append a b))
       (or (fn-pair-memberp p a) (fn-pair-memberp p b))))

; A withdrawal projection of P: P's state with a subsequence of its articles.
; Proof vocabulary for the owner relation (a connection's archive is a
; projection of its pinned prefix); never run on a served path.
(defun fn-ctl-subseqp (xs ys)
  (declare (xargs :guard t))
  (cond ((atom xs) (null xs))
        ((atom ys) nil)
        (t (or (and (equal (car xs) (car ys))
                    (fn-ctl-subseqp (cdr xs) (cdr ys)))
               (fn-ctl-subseqp xs (cdr ys))))))
(defthm fn-ctl-subseqp-msgids
  (implies (and (fn-ctl-subseqp xs ys)
                (not (member-equal m (fn-article-msgids ys))))
           (not (member-equal m (fn-article-msgids xs)))))
(defthm fn-ctl-subseqp-article-listp
  (implies (and (fn-ctl-subseqp xs ys) (fn-article-listp configured ys))
           (fn-article-listp configured xs))
  :hints (("Goal" :in-theory (disable fn-articlep))))
(defthm fn-ctl-subseqp-all-memberships
  (implies (and (fn-ctl-subseqp xs ys)
                (not (fn-pair-memberp p (fn-all-article-memberships ys))))
           (not (fn-pair-memberp p (fn-all-article-memberships xs)))))
(defthm fn-ctl-subseqp-conflictsp
  (implies (and (fn-ctl-subseqp xs ys)
                (not (fn-memberships-conflictsp m ys)))
           (not (fn-memberships-conflictsp m xs)))
  :hints (("Goal" :induct (fn-memberships-conflictsp m ys))))
(defthm fn-ctl-subseqp-freshp
  (implies (and (fn-ctl-subseqp xs ys) (fn-articles-freshp ys))
           (fn-articles-freshp xs)))
(defthm fn-ctl-subseqp-below-nextsp
  (implies (and (fn-ctl-subseqp xs ys) (fn-articles-below-nextsp ys nexts))
           (fn-articles-below-nextsp xs nexts)))
(defthm fn-ctl-subseqp-acceptedp
  (implies (and (fn-ctl-subseqp xs ys) (not (fn-acceptedp m ys)))
           (not (fn-acceptedp m xs))))
(defthm fn-ctl-subseqp-of-cons-right
  (implies (fn-ctl-subseqp xs ys)
           (fn-ctl-subseqp xs (cons y ys))))
(defun fn-ctl-projectionp (a p)
  (declare (xargs :guard t))
  (and (equal a (fn-ctl-visible-state-of p (fn-state-articles a)))
       (fn-ctl-subseqp (fn-state-articles a) (fn-state-articles p))))
(defthm fn-ctl-projection-statep
  (implies (and (fn-ctl-projectionp a p) (fn-statep p))
           (fn-statep a))
  :hints (("Goal" :in-theory (e/d (fn-statep) (fn-ctl-subseqp)))))
(defthm fn-ctl-visible-filter-subseqp
  (fn-ctl-subseqp (fn-ctl-visible-filter xs ws arts verdicts) xs)
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-by-p))))
(defthm fn-ctl-visible-state-is-a-projection
  (fn-ctl-projectionp (fn-ctl-visible-state p ws verdicts) p)
  :hints (("Goal" :in-theory (disable fn-ctl-visible-filter fn-ctl-visible-state-of))))

; The visible state is an acceptance state whenever the archive is.
(defthm fn-ctl-visible-state-statep
  (implies (fn-statep a)
           (fn-statep (fn-ctl-visible-state a ws verdicts)))
  :hints (("Goal" :use ((:instance fn-ctl-projection-statep
                                   (a (fn-ctl-visible-state a ws verdicts))
                                   (p a)))
           :in-theory (disable fn-ctl-projectionp fn-ctl-visible-state))))

; -----------------------------------------------------------------------------
; The refresh kernel.  Between two refreshes the acceptance archive NEW is
; OLD with at most one article consed (the owner refreshes at every idle
; phase); anything else (start, reopen) is a discontinuity and rebuilds.
; The record a withdrawing article causes (a cancel, or an ordinary article
; with a Supersedes field) is decided under the configuration in force at
; THAT ARTICLE'S OWN Store txid: `fn-ctl-config-at' of the txid of its
; acceptance record in RECORDS (the Store's durable event list) over
; CONFIGS (the Store's configuration journal).  A configuration record at
; the same txid precedes the event (books/config-physical-replay.lisp), so
; this is the configuration its commit saw; a record appended later carries
; a larger txid and changes nothing (`fn-ctl-revoke-changes-decisions-not-
; records').  The live refresh and recovery's rebuild therefore decide every
; record alike (`fn-ctl-refresh-withdrawals-is-the-journal', below).
; Cost: the cons case costs |WS| plus, for an executed cancel, one pass over
; the visible list (fn-ctl-visible-add), plus one walk of RECORDS for the
; txid when the new article names a target; the checks are `equal' on
; shared structure.

; The txid of MSGID's acceptance record, nil when RECORDS holds none.
(defun fn-ctl-record-txid (msgid records)
  (declare (xargs :guard t))
  (if (consp records)
      (if (and (fn-record-p (car records))
               (equal (fn-record-msgid (car records)) msgid))
          (fn-record-txid (car records))
        (fn-ctl-record-txid msgid (cdr records)))
    nil))

(defun fn-ctl-article-withdrawals (a verdicts records configs)
  (declare (xargs :guard t))
  (if (consp a)
      (let ((target (fn-ctl-target-octets (fn-article-payload a))))
        (if target
            (let ((plan (fn-ctl-withdrawal-plan
                         (fn-article-msgid a)
                         (fn-ctl-lookup-verdict (fn-article-msgid a) verdicts)
                         target
                         (fn-ctl-config-at
                          (fn-ctl-record-txid (fn-article-msgid a) records)
                          configs))))
              (if (fn-ctl-withdrawalp plan) (list plan) nil))
          nil))
    nil))
(defun fn-ctl-articles-withdrawals (arts verdicts records configs)
  (declare (xargs :guard t))
  (if (consp arts)
      (fn-ctl-prepend (fn-ctl-article-withdrawals (car arts) verdicts records
                                                  configs)
                      (fn-ctl-articles-withdrawals (cdr arts) verdicts records
                                                   configs))
    nil))
(defun fn-ctl-verdicts-grow-by-p (new old a)
  (declare (xargs :guard t))
  (or (equal new old)
      (and (consp new) (consp (car new)) (consp a)
           (equal (cdr new) old)
           (equal (car (car new)) (fn-article-msgid a)))))
(defun fn-ctl-refresh-withdrawals (new old ws verdicts records configs)
  (declare (xargs :guard t))
  (cond ((equal new old) ws)
        ((and (consp new) (equal (cdr new) old))
         (fn-ctl-prepend (fn-ctl-article-withdrawals (car new) verdicts records
                                                     configs)
                         ws))
        (t (fn-ctl-articles-withdrawals new verdicts records configs))))
(defun fn-ctl-refresh-visible (new old old-visible ws old-verdicts verdicts)
  (declare (xargs :guard t))
  (cond ((and (equal new old) (equal verdicts old-verdicts)) old-visible)
        ((and (consp new) (equal (cdr new) old)
              (fn-ctl-verdicts-grow-by-p verdicts old-verdicts (car new)))
         (fn-ctl-visible-add (car new) old-visible old ws verdicts))
        (t (fn-ctl-visible-articles new ws verdicts))))

(defthm fn-ctl-has-msgid-p-means-member-msgids
  (implies (fn-ctl-has-msgid-p m arts)
           (member-equal m (fn-article-msgids arts))))
(defthm fn-ctl-withdrawn-by-p-of-absent-cause-prefix
  (implies (and (fn-ctl-withdrawalp w)
                (not (fn-ctl-has-msgid-p (fn-ctl-w-cause w) arts)))
           (equal (fn-ctl-withdrawn-by-p x (cons w ws) arts verdicts)
                  (fn-ctl-withdrawn-by-p x ws arts verdicts)))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawal-effect fn-ctl-effect-withdrawsp))))
(defun fn-ctl-causes-all-p (recs c)
  (declare (xargs :guard t))
  (if (consp recs)
      (and (fn-ctl-withdrawalp (car recs))
           (equal (fn-ctl-w-cause (car recs)) c)
           (fn-ctl-causes-all-p (cdr recs) c))
    t))
(defthm fn-ctl-causes-all-p-of-article-withdrawals
  (fn-ctl-causes-all-p (fn-ctl-article-withdrawals a verdicts records configs) (fn-article-msgid a))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawal-plan fn-ctl-withdrawalp
                                      fn-ctl-target-octets fn-ctl-config-at
                                      fn-ctl-record-txid)
           :use ((:instance fn-ctl-withdrawal-plan-record-is-bound
                  (cause (fn-article-msgid a))
                  (verdict (fn-ctl-lookup-verdict (fn-article-msgid a) verdicts))
                  (target (fn-ctl-target-octets (fn-article-payload a)))
                  (cfg (fn-ctl-config-at
                        (fn-ctl-record-txid (fn-article-msgid a) records)
                        configs)))))))
(defthm fn-ctl-withdrawn-by-p-of-absent-causes-append
  (implies (and (fn-ctl-causes-all-p recs c)
                (not (fn-ctl-has-msgid-p c arts)))
           (equal (fn-ctl-withdrawn-by-p x (append recs ws) arts verdicts)
                  (fn-ctl-withdrawn-by-p x ws arts verdicts)))
  :hints (("Goal" :induct (fn-ctl-causes-all-p recs c)
           :in-theory (disable fn-ctl-withdrawn-by-p fn-ctl-withdrawalp))))
(defthm fn-ctl-visible-filter-of-absent-causes-append
  (implies (and (fn-ctl-causes-all-p recs c)
                (not (fn-ctl-has-msgid-p c arts)))
           (equal (fn-ctl-visible-filter xs (append recs ws) arts verdicts)
                  (fn-ctl-visible-filter xs ws arts verdicts)))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-by-p fn-ctl-causes-all-p))))
(defthm fn-ctl-withdrawn-by-p-of-other-verdict
  (implies (not (equal m (fn-article-msgid x)))
           (equal (fn-ctl-withdrawn-by-p x ws arts (cons (cons m v) verdicts))
                  (fn-ctl-withdrawn-by-p x ws arts verdicts)))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawal-effect fn-ctl-effect-withdrawsp
                                      fn-ctl-has-msgid-p))))
(defthm fn-ctl-visible-filter-of-new-verdict
  (implies (not (member-equal m (fn-article-msgids xs)))
           (equal (fn-ctl-visible-filter xs ws arts (cons (cons m v) verdicts))
                  (fn-ctl-visible-filter xs ws arts verdicts)))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-by-p))))

(defthm fn-ctl-visible-of-grown-records-and-verdicts
  (implies (and (not (member-equal (fn-article-msgid a) (fn-article-msgids old)))
                (fn-ctl-verdicts-grow-by-p verdicts old-verdicts a))
           (equal (fn-ctl-visible-articles
                   old (fn-ctl-prepend (fn-ctl-article-withdrawals a verdicts records configs) ws)
                   verdicts)
                  (fn-ctl-visible-articles old ws old-verdicts)))
  :hints (("Goal" :in-theory (disable fn-ctl-visible-filter fn-ctl-article-withdrawals
                                      fn-ctl-causes-all-p)
           :use ((:instance fn-ctl-has-msgid-p-means-member-msgids
                            (m (fn-article-msgid a)) (arts old))
                 (:instance fn-ctl-visible-filter-of-absent-causes-append
                            (recs (fn-ctl-article-withdrawals a verdicts records configs))
                            (c (fn-article-msgid a)) (xs old) (arts old))))))
; KEYSTONE (C3, the owner refresh).  The visible list the refresh carries
; (fn-own-refresh, books/owner.lisp) is the definition's visible list of the
; new archive under the records the refresh carries, whenever the old one
; was, and the archive's Message-IDs are distinct (fn-statep): the
; incremental path and the rebuild agree with the whole-archive filter.
(defthm fn-ctl-refresh-visible-is-visible
  (implies (and (equal old-visible (fn-ctl-visible-articles old ws old-verdicts))
                (no-duplicatesp-equal (fn-article-msgids new)))
           (let ((ws2 (fn-ctl-refresh-withdrawals new old ws verdicts records configs)))
             (equal (fn-ctl-refresh-visible new old old-visible ws2
                                            old-verdicts verdicts)
                    (fn-ctl-visible-articles new ws2 verdicts))))
  :hints (("Goal" :in-theory (e/d (fn-ctl-visible-add-is-visible)
                                  (fn-ctl-visible-add fn-ctl-visible-articles
                                   fn-ctl-article-withdrawals fn-ctl-verdicts-grow-by-p
                                   fn-ctl-articles-withdrawals fn-ctl-prepend-is-append)))))

; The refresh at the level of acceptance states, as the owner uses it: the
; carried archive is the visible state of the old prefix, the carried raw
; list is that prefix's article list.
(defthm fn-ctl-refresh-state-is-visible
  (implies (and (equal old-archive (fn-ctl-visible-state old-p ws old-verdicts))
                (equal old-raw (fn-state-articles old-p))
                (no-duplicatesp-equal (fn-article-msgids (fn-state-articles new-p))))
           (let ((ws2 (fn-ctl-refresh-withdrawals (fn-state-articles new-p) old-raw
                                                  ws verdicts records configs)))
             (equal (fn-ctl-visible-state-of
                     new-p
                     (fn-ctl-refresh-visible (fn-state-articles new-p) old-raw
                                             (fn-state-articles old-archive)
                                             ws2 old-verdicts verdicts))
                    (fn-ctl-visible-state new-p ws2 verdicts))))
  :hints (("Goal" :in-theory (disable fn-ctl-refresh-visible fn-ctl-refresh-withdrawals
                                      fn-ctl-visible-articles fn-ctl-visible-state-of)
           :use ((:instance fn-ctl-refresh-visible-is-visible
                            (new (fn-state-articles new-p))
                            (old (fn-state-articles old-p))
                            (old-visible (fn-ctl-visible-articles
                                          (fn-state-articles old-p) ws old-verdicts)))))))

; -----------------------------------------------------------------------------
; Recovery decides each record under its own txid (brief control-c3d step 2).
; The journal a Store holds: one entry (TXID CAUSE VERDICT TARGET) per
; withdrawing article of ARTS, newest first, the shape
; `fn-ctl-journal-withdrawals' (books/control-authority.lisp) decides.

(defun fn-ctl-archive-entries (arts verdicts records)
  (declare (xargs :guard t))
  (if (consp arts)
      (let* ((a (car arts))
             (target (and (consp a)
                          (fn-ctl-target-octets (fn-article-payload a))))
             (rest (fn-ctl-archive-entries (cdr arts) verdicts records)))
        (if target
            (cons (list (fn-ctl-record-txid (fn-article-msgid a) records)
                        (fn-article-msgid a)
                        (fn-ctl-lookup-verdict (fn-article-msgid a) verdicts)
                        target)
                  rest)
          rest))
    nil))

(defthm fn-ctl-journal-withdrawals-of-append
  (equal (fn-ctl-journal-withdrawals (append xs ys) configs)
         (append (fn-ctl-journal-withdrawals xs configs)
                 (fn-ctl-journal-withdrawals ys configs)))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawal-plan fn-ctl-withdrawalp
                                      fn-ctl-config-at))))

; The rebuild the owner runs at a discontinuity (start, reopen: recovery)
; is the journal definition over the archive's entries.
(defthm fn-ctl-articles-withdrawals-is-the-journal
  (equal (fn-ctl-articles-withdrawals arts verdicts records configs)
         (fn-ctl-journal-withdrawals (fn-ctl-archive-entries arts verdicts records)
                                     configs))
  :hints (("Goal" :induct (fn-ctl-archive-entries arts verdicts records)
           :in-theory (disable fn-ctl-withdrawal-plan fn-ctl-withdrawalp
                               fn-ctl-config-at fn-ctl-target-octets
                               fn-ctl-record-txid fn-ctl-lookup-verdict))))

; Stability of the entries as the Store grows.  (1) A record already found
; keeps its txid when later records are appended.
(defthm fn-ctl-record-txid-of-append
  (implies (fn-ctl-record-txid m records)
           (equal (fn-ctl-record-txid m (append records more))
                  (fn-ctl-record-txid m records))))

(defun fn-ctl-all-recorded-p (arts records)
  (declare (xargs :guard t))
  (if (consp arts)
      (and (or (not (consp (car arts)))
               (not (fn-ctl-target-octets (fn-article-payload (car arts))))
               (fn-ctl-record-txid (fn-article-msgid (car arts)) records))
           (fn-ctl-all-recorded-p (cdr arts) records))
    t))

(defthm fn-ctl-archive-entries-of-appended-records
  (implies (fn-ctl-all-recorded-p arts records)
           (equal (fn-ctl-archive-entries arts verdicts (append records more))
                  (fn-ctl-archive-entries arts verdicts records)))
  :hints (("Goal" :in-theory (disable fn-ctl-target-octets fn-ctl-record-txid))))

; (2) A verdict recorded for a Message-ID outside ARTS changes no entry.
(defthm fn-ctl-lookup-verdict-of-other-cons
  (implies (not (equal m k))
           (equal (fn-ctl-lookup-verdict k (cons (cons m v) verdicts))
                  (fn-ctl-lookup-verdict k verdicts))))

(defthm fn-ctl-archive-entries-of-new-verdict
  (implies (not (member-equal m (fn-article-msgids arts)))
           (equal (fn-ctl-archive-entries arts (cons (cons m v) verdicts) records)
                  (fn-ctl-archive-entries arts verdicts records)))
  :hints (("Goal" :in-theory (disable fn-ctl-target-octets fn-ctl-record-txid
                                      fn-ctl-lookup-verdict))))

; (3) Configuration records appended later carry larger txids than every
; entry: `fn-ctl-revoke-changes-decisions-not-records'.

; The three together: the journal of OLD's entries is unchanged by the
; Store's growth.
(defthm fn-ctl-journal-of-old-entries-is-stable
  (implies (and (fn-ctl-all-recorded-p old r0)
                (fn-ctl-entries-below-p (fn-ctl-archive-entries old v0 r0)
                                        (fn-cfg-record-txid (car more-c))))
           (equal (fn-ctl-journal-withdrawals
                   (fn-ctl-archive-entries old v0 (append r0 more-r))
                   (append c0 more-c))
                  (fn-ctl-journal-withdrawals
                   (fn-ctl-archive-entries old v0 r0) c0)))
  :hints (("Goal" :in-theory (disable fn-ctl-journal-withdrawals
                                      fn-ctl-archive-entries fn-ctl-all-recorded-p
                                      fn-ctl-entries-below-p)
           :use ((:instance fn-ctl-revoke-changes-decisions-not-records
                            (entries (fn-ctl-archive-entries old v0 r0))
                            (configs c0) (more more-c))))))

(defthmd fn-ctl-archive-entries-of-grown-verdicts
  (implies (and (consp verdicts) (consp (car verdicts))
                (not (member-equal (car (car verdicts)) (fn-article-msgids arts))))
           (equal (fn-ctl-archive-entries arts verdicts records)
                  (fn-ctl-archive-entries arts (cdr verdicts) records)))
  :hints (("Goal" :use ((:instance fn-ctl-archive-entries-of-new-verdict
                                   (m (car (car verdicts)))
                                   (v (cdr (car verdicts)))
                                   (verdicts (cdr verdicts))))
           :in-theory (disable fn-ctl-archive-entries-of-new-verdict
                               fn-ctl-archive-entries))))

(defthm fn-ctl-journal-of-consed-entries
  (equal (fn-ctl-journal-withdrawals
          (fn-ctl-archive-entries (cons a old) verdicts records) configs)
         (fn-ctl-prepend (fn-ctl-article-withdrawals a verdicts records configs)
                         (fn-ctl-journal-withdrawals
                          (fn-ctl-archive-entries old verdicts records) configs)))
  :hints (("Goal" :use ((:instance fn-ctl-articles-withdrawals-is-the-journal
                                   (arts (cons a old)))
                        (:instance fn-ctl-articles-withdrawals-is-the-journal
                                   (arts old)))
           :in-theory (disable fn-ctl-articles-withdrawals-is-the-journal
                               fn-ctl-journal-withdrawals fn-ctl-archive-entries
                               fn-ctl-article-withdrawals fn-ctl-prepend-is-append))))

; KEYSTONE (C3, live equals recovery).  Let the records an old view carries
; be the journal of its archive OLD under the durable inputs of its refresh
; (verdicts V0, Store records R0, configuration journal C0), every
; withdrawing article of OLD have its acceptance record in R0, the verdict
; list have grown by at most one pair for a Message-ID outside OLD, and the
; configuration records appended since carry txids above every entry of
; OLD.  Then the records the next refresh carries, over the grown inputs,
; are the journal of the new archive under those grown inputs: what
; recovery computes from the Store at that moment.  Subject:
; `fn-ctl-refresh-withdrawals', called by `fn-own-refresh'
; (books/owner.lisp) with RECORDS = the Store's records and CONFIGS =
; `fn-sn-config-history'; recovery (`fn-own-start') reaches its
; discontinuity arm.
(defthm fn-ctl-refresh-withdrawals-is-the-journal
  (implies (and (equal ws (fn-ctl-journal-withdrawals
                           (fn-ctl-archive-entries old v0 r0) c0))
                (fn-ctl-all-recorded-p old r0)
                (or (equal verdicts v0)
                    (and (consp verdicts) (consp (car verdicts))
                         (equal (cdr verdicts) v0)
                         (not (member-equal (car (car verdicts))
                                            (fn-article-msgids old)))))
                (fn-ctl-entries-below-p (fn-ctl-archive-entries old v0 r0)
                                        (fn-cfg-record-txid (car more-c))))
           (equal (fn-ctl-refresh-withdrawals new old ws verdicts
                                              (append r0 more-r)
                                              (append c0 more-c))
                  (fn-ctl-journal-withdrawals
                   (fn-ctl-archive-entries new verdicts (append r0 more-r))
                   (append c0 more-c))))
  :hints (("Goal" :in-theory (e/d (fn-ctl-refresh-withdrawals)
                                  (fn-ctl-journal-withdrawals
                                   fn-ctl-archive-entries fn-ctl-all-recorded-p
                                   fn-ctl-entries-below-p fn-ctl-article-withdrawals
                                   fn-ctl-prepend-is-append))
           :cases ((equal verdicts v0))
           :use ((:instance fn-ctl-archive-entries-of-grown-verdicts
                            (arts old) (records (append r0 more-r)))))))

; Distinct Message-IDs, the fact the refresh keystone assumes, from the
; article-list recognizer every acceptance state carries.
(defthm fn-ctl-article-listp-msgids-distinct
  (implies (fn-article-listp configured xs)
           (no-duplicatesp-equal (fn-article-msgids xs)))
  :hints (("Goal" :in-theory (disable fn-articlep))))


(in-theory (disable (:d fn-ctl-visible-add) (:d fn-ctl-visible-extend)
                    (:d fn-ctl-drop-via) (:d fn-ctl-causes-p)
                    (:d fn-ctl-withdrawn-via-p)
                    (:d fn-ctl-refresh-visible) (:d fn-ctl-refresh-withdrawals)
                    (:d fn-ctl-article-withdrawals) (:d fn-ctl-articles-withdrawals)
                    (:d fn-ctl-verdicts-grow-by-p) (:d fn-ctl-visible-state)
                    (:d fn-ctl-visible-state-of) (:d fn-ctl-projectionp)
                    (:d fn-ctl-subseqp) (:d fn-ctl-archive-entries)
                    (:d fn-ctl-all-recorded-p) (:d fn-ctl-record-txid)))
