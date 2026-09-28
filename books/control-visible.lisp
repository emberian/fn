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
; fn-replay-composite-record: the article record inside a kind-4 signed
; acceptance composite, decoded as replay decodes it.
(include-book "replay")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-ctl-withdrawal-effect)
                          (:definition fn-ctl-withdrawn-by-p))))

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
                   (fn-ctl-lookup-verdict (fn-article-msgid x) verdicts)
                   (fn-article-payload x))))
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
; Executes by a loop (PKT-876, lane open-depth): one control-stack frame per
; retained article on the owner's open.  The :logic is the recursion,
; unchanged; the :exec is a loop, equal by the guard proof.
(defun fn-ctl-drop-via-rev (xs ws cause verdicts acc)
  (declare (xargs :guard (true-listp acc)))
  (if (consp xs)
      (fn-ctl-drop-via-rev (cdr xs) ws cause verdicts (if (fn-ctl-withdrawn-via-p (car xs) ws cause verdicts) acc (cons (car xs) acc)))
    acc))

(defun fn-ctl-drop-via (xs ws cause verdicts)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp xs)
           (if (fn-ctl-withdrawn-via-p (car xs) ws cause verdicts)
               (fn-ctl-drop-via (cdr xs) ws cause verdicts)
             (cons (car xs) (fn-ctl-drop-via (cdr xs) ws cause verdicts)))
         nil)
       :exec (reverse (fn-ctl-drop-via-rev xs ws cause verdicts nil))))

(encapsulate ()
  (local
   (defthm fn-ctl-drop-via-rev-is-revappend
     (equal (fn-ctl-drop-via-rev xs ws cause verdicts acc)
            (revappend (fn-ctl-drop-via xs ws cause verdicts) acc))
     :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-via-p)))))
  (local
   (defthm fn-ctl-drop-via-true-listp-od
     (true-listp (fn-ctl-drop-via xs ws cause verdicts))))
  (local
   (defthm fn-ctl-drop-via-od-revappend-revappend
     (equal (revappend (revappend x y) z) (revappend y (append x z)))))
  (local
   (defthm fn-ctl-drop-via-od-append-nil-when-true-listp
     (implies (true-listp x) (equal (append x nil) x))))
  (local
   (defthm fn-ctl-drop-via-od-true-listp-of-revappend
     (implies (true-listp y) (true-listp (revappend x y)))))
  (verify-guards fn-ctl-drop-via
    :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-via-p)))))

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

; The Message-ID of an acceptance event: an article record's own, or the
; article record a signed acceptance composite carries (decoded as replay
; decodes it, `fn-replay-composite-record').  Cost: a composite is decoded
; (its article record's octets) when the walk reaches it.
; E is a history event: after the records flip a plain article is a HELD row
; and a signed article's composite is the ROW `fn-hstxa-p' whose interned
; article carries the Message-ID (books/held-record.lisp); the wire forms (a
; record, a composite) read as before.  Refinement over alpha:
; books/history-fold-refinement.lisp fn-ctl-event-msgid-over-alpha.
(defun fn-ctl-event-msgid (e)
  (declare (xargs :guard t))
  (cond ((fn-held-p e) (fn-record-msgid e))
        ((fn-hstxa-p e) (fn-record-msgid (fn-hstxa-held e)))
        ((fn-record-p e) (fn-record-msgid e))
        (t (let ((r (fn-replay-composite-record e)))
             (if (fn-record-p r) (fn-record-msgid r) nil)))))

; The txid of MSGID's acceptance event, nil when RECORDS holds none.
; Pessimistic cost: a walk of RECORDS decoding every signed composite before
; the match, paid once per withdrawing article the refresh first publishes
; (and per withdrawing article at recovery).  An index from Message-ID to
; txid beside the Message-ID trie is the follow-up.
(defun fn-ctl-record-txid (msgid records)
  (declare (xargs :guard t))
  (if (consp records)
      (if (and msgid (equal (fn-ctl-event-msgid (car records)) msgid))
          (fn-store-event-txid (car records))
        (fn-ctl-record-txid msgid (cdr records)))
    nil))

; -----------------------------------------------------------------------------
; The control facts through the history (records flip; flip-L8-2).  After the
; flip an archive article holds a HANDLE, so its octets are not here to
; parse: the facts the control vocabulary reads from them (target, Cancel-Key
; and Cancel-Lock entries) are the CONTROL fact of the article's ROW, decided
; once at intern (books/catalog-record.lisp fn-held-facts-of;
; fn-hf-control-of-held-facts-of says it is `fn-ctl-control-of' of the
; bytes).  RECORDS is the Store's history the refresh already holds.

; The held row a history event carries: a held row itself (a natural head,
; its sequence) or the interned article of a retained accepted-statement
; event; nil for every other event.  Dispatch on the head and the held
; shape (fifteen positions) only: the recognizer `fn-held-p' is never run
; here (executing it hashes every statement of a row's delta, fn-lace-p ->
; fn-stmt-p -> fn-digest).  The shape test is what tells a row from a
; standalone verdict event (fn-stxe-p, books/stx-evidence-records.lisp: a
; natural head too, eight positions, its Message-ID at the row's Message-ID
; position), which the Store accepts into its history
; (fn-sn-prepare-identity, recovery) and which is not an article's row.  On
; every Store event the dispatch is exactly the Message-ID index's
; (books/control-visible-indexed.lisp fn-ctl-row-okp-of-store-event).
(defun fn-ctl-event-row (e)
  (declare (xargs :guard t))
  (cond ((atom e) nil)
        ((eq (car e) :hstxa) (fn-hstxa-held e))
        ((and (natp (car e)) (fn-held-shapep e)) e)
        (t nil)))

; The first history event whose row carries MSGID, nil when none does.
; Pessimistic cost: a walk of RECORDS comparing one Message-ID per row
; (`equal' on strings; no decode, no hash), paid once per new article at a
; refresh and once per record whose target is the new article.
(defun fn-ctl-row-event (msgid records)
  (declare (xargs :guard t))
  (if (consp records)
      (let ((row (fn-ctl-event-row (car records))))
        (if (and msgid row (equal (fn-record-msgid row) msgid))
            (car records)
          (fn-ctl-row-event msgid (cdr records))))
    nil))

; The control fact of MSGID's row, nil when the history holds none.
(defun fn-ctl-row-control (msgid records)
  (declare (xargs :guard t))
  (let ((e (fn-ctl-row-event msgid records)))
    (if e (fn-hf-control (fn-held-facts (fn-ctl-event-row e))) nil)))

; The decision for one article A: nil when its row names no target;
; otherwise the plan for its target and Cancel-Key entries (from its row),
; decided under the configuration in force at its row's txid, a record
; resolved to its target's Cancel-Lock entries as the history holds them
; (nil while the target has not arrived: the refresh resolves them when it
; does, `fn-ctl-resolve-tlocks'), or (:decline REASON).  `control evidence'
; prints this (books/control-evidence.lisp fn-cev-plan).
(defun fn-ctl-article-plan (a verdicts records configs)
  (declare (xargs :guard t))
  (if (consp a)
      (let* ((m (fn-article-msgid a))
             (e (fn-ctl-row-event m records))
             (control (if e (fn-hf-control (fn-held-facts (fn-ctl-event-row e))) nil))
             (target (fn-ctl-control-target control)))
        (if target
            (fn-ctl-w-with-tlocks
             (fn-ctl-withdrawal-plan
              m (fn-ctl-lookup-verdict m verdicts) target
              (fn-ctl-control-keys control)
              (fn-ctl-config-at (fn-store-event-txid e) configs))
             (fn-ctl-control-locks (fn-ctl-row-control target records)))
          nil))
    nil))

; The records one withdrawing article causes.
(defun fn-ctl-article-withdrawals (a verdicts records configs)
  (declare (xargs :guard t))
  (let ((plan (fn-ctl-article-plan a verdicts records configs)))
    (if (fn-ctl-withdrawalp plan) (list plan) nil)))
; -----------------------------------------------------------------------------
; Recovery's decision of every record, executed through one table.  The
; discontinuity arm (start, reopen) decides every article of the archive;
; one `fn-ctl-row-event' walk per article is N x R.  The executable path
; builds a fast alist from Message-ID to the first event carrying its row in
; one pass over R and looks each article (and its target) up in it:
; O(R + N) hash operations.  The logical definition is unchanged
; (`fn-ctl-articles-withdrawals-tbl-is-articles-withdrawals').

(defun fn-ctl-row-table (records tbl)
  (declare (xargs :guard t))
  (if (consp records)
      (let* ((row (fn-ctl-event-row (car records)))
             (m (and row (fn-record-msgid row))))
        (fn-ctl-row-table (cdr records)
                          (if (and m (not (hons-get m tbl)))
                              (hons-acons m (car records) tbl)
                            tbl)))
    tbl))

(defun fn-ctl-row-event-in (m tbl)
  (declare (xargs :guard t))
  (and m (cdr (hons-get m tbl))))

(defthm fn-ctl-row-table-lookup
  (implies m
           (equal (hons-assoc-equal m (fn-ctl-row-table records tbl))
                  (or (hons-assoc-equal m tbl)
                      (let ((e (fn-ctl-row-event m records)))
                        (and e (cons m e))))))
  :hints (("Goal" :induct (fn-ctl-row-table records tbl)
           :in-theory (e/d (fn-ctl-row-event fn-ctl-row-table) (fn-ctl-event-row)))))

(defthm fn-ctl-row-event-in-row-table
  (equal (fn-ctl-row-event-in m (fn-ctl-row-table records nil))
         (fn-ctl-row-event m records))
  :hints (("Goal" :in-theory (e/d (fn-ctl-row-event-in fn-ctl-row-event)
                                  (fn-ctl-row-table fn-ctl-event-row))
           :cases (m))))

(defun fn-ctl-article-plan-in (a verdicts tbl configs)
  (declare (xargs :guard t))
  (if (consp a)
      (let* ((m (fn-article-msgid a))
             (e (fn-ctl-row-event-in m tbl))
             (control (if e (fn-hf-control (fn-held-facts (fn-ctl-event-row e))) nil))
             (target (fn-ctl-control-target control)))
        (if target
            (fn-ctl-w-with-tlocks
             (fn-ctl-withdrawal-plan
              m (fn-ctl-lookup-verdict m verdicts) target
              (fn-ctl-control-keys control)
              (fn-ctl-config-at (fn-store-event-txid e) configs))
             (fn-ctl-control-locks
              (let ((te (fn-ctl-row-event-in target tbl)))
                (if te (fn-hf-control (fn-held-facts (fn-ctl-event-row te))) nil))))
          nil))
    nil))

; Executes by a loop (PKT-876, lane open-depth): one control-stack frame per
; retained article on the owner's open.  The :logic is the recursion,
; unchanged; the :exec is a loop, equal by the guard proof.
(defun fn-ctl-articles-withdrawals-in-loop (rev verdicts tbl configs acc)
  (declare (xargs :guard t))
  (if (consp rev)
      (fn-ctl-articles-withdrawals-in-loop (cdr rev) verdicts tbl configs (fn-ctl-prepend (let ((plan (fn-ctl-article-plan-in (car rev) verdicts tbl configs)))
                                         (if (fn-ctl-withdrawalp plan) (list plan) nil))
                                       acc))
    acc))

(defun fn-ctl-articles-withdrawals-in (arts verdicts tbl configs)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp arts)
           (fn-ctl-prepend (let ((plan (fn-ctl-article-plan-in (car arts) verdicts tbl configs)))
                             (if (fn-ctl-withdrawalp plan) (list plan) nil))
                           (fn-ctl-articles-withdrawals-in (cdr arts) verdicts tbl configs))
         nil)
       :exec (fn-ctl-articles-withdrawals-in-loop (fn-ag-rev-onto arts nil) verdicts tbl configs nil)))

(encapsulate ()
  (local
   (defthm fn-ctl-articles-withdrawals-in-loop-of-rev-onto
     (equal (fn-ctl-articles-withdrawals-in-loop (fn-ag-rev-onto xs zs) verdicts tbl configs nil)
            (fn-ctl-articles-withdrawals-in-loop zs verdicts tbl configs (fn-ctl-articles-withdrawals-in xs verdicts tbl configs)))
     :hints (("Goal" :induct (fn-ag-rev-onto xs zs)
                     :in-theory (disable fn-ctl-article-plan-in fn-ctl-withdrawalp fn-ctl-prepend)))))
  (verify-guards fn-ctl-articles-withdrawals-in
    :hints (("Goal" :in-theory (disable fn-ctl-article-plan-in fn-ctl-withdrawalp fn-ctl-prepend fn-ag-rev-onto)
                    :use ((:instance fn-ctl-articles-withdrawals-in-loop-of-rev-onto (xs arts) (zs nil)))))))

(defthm fn-ctl-article-plan-in-row-table
  (equal (fn-ctl-article-plan-in a verdicts (fn-ctl-row-table records nil) configs)
         (fn-ctl-article-plan a verdicts records configs))
  :hints (("Goal" :in-theory (e/d (fn-ctl-article-plan fn-ctl-row-control fn-ctl-article-plan-in)
                                  (fn-ctl-row-table fn-ctl-row-event-in fn-ctl-row-event
                                   fn-ctl-withdrawal-plan fn-ctl-w-with-tlocks
                                   fn-ctl-lookup-verdict fn-ctl-config-at)))))

(defun fn-ctl-articles-withdrawals (arts verdicts records configs)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp arts)
           (fn-ctl-prepend (fn-ctl-article-withdrawals (car arts) verdicts records
                                                       configs)
                           (fn-ctl-articles-withdrawals (cdr arts) verdicts records
                                                        configs))
         nil)
       :exec
       (let ((tbl (fn-ctl-row-table records nil)))
         (fast-alist-free-on-exit
          tbl (fn-ctl-articles-withdrawals-in arts verdicts tbl configs)))))

(defthm fn-ctl-articles-withdrawals-in-row-table
  (equal (fn-ctl-articles-withdrawals-in arts verdicts (fn-ctl-row-table records nil) configs)
         (fn-ctl-articles-withdrawals arts verdicts records configs))
  :hints (("Goal" :induct (fn-ctl-articles-withdrawals arts verdicts records configs)
           :in-theory (e/d (fn-ctl-articles-withdrawals fn-ctl-articles-withdrawals-in
                            fn-ctl-article-withdrawals)
                           (fn-ctl-row-table fn-ctl-article-plan-in fn-ctl-article-plan)))))

(verify-guards fn-ctl-articles-withdrawals
  :hints (("Goal" :in-theory (disable fn-ctl-article-withdrawals fn-ctl-articles-withdrawals-in
                                      fn-ctl-row-table fn-ctl-prepend-is-append)
           :expand ((fn-ctl-articles-withdrawals arts verdicts records configs)))))

(defun fn-ctl-verdicts-grow-by-p (new old a)
  (declare (xargs :guard t))
  (or (equal new old)
      (and (consp new) (consp (car new)) (consp a)
           (equal (cdr new) old)
           (equal (car (car new)) (fn-article-msgid a)))))
; The records in WS whose target is M, resolved to LOCKS.
(defun fn-ctl-set-tlocks (ws m locks)
  (declare (xargs :guard t))
  (if (consp ws)
      (cons (if (and (fn-ctl-withdrawalp (car ws))
                     (equal (fn-ctl-w-target (car ws)) m))
                (fn-ctl-w-with-tlocks (car ws) locks)
              (car ws))
            (fn-ctl-set-tlocks (cdr ws) m locks))
    ws))

(defun fn-ctl-targets-p (ws m)
  (declare (xargs :guard t))
  (if (consp ws)
      (or (and (fn-ctl-withdrawalp (car ws))
               (equal (fn-ctl-w-target (car ws)) m))
          (fn-ctl-targets-p (cdr ws) m))
    nil))

; A new article M may be the target of records made before it arrived
; (a cancel relayed ahead of its target): they are resolved to its row's
; locks.  An ordinary article no record targets costs one pass over WS and
; no allocation.
(defun fn-ctl-resolve-tlocks (ws m records)
  (declare (xargs :guard t))
  (if (fn-ctl-targets-p ws m)
      (fn-ctl-set-tlocks ws m (fn-ctl-control-locks (fn-ctl-row-control m records)))
    ws))

(defun fn-ctl-refresh-withdrawals (new old ws verdicts records configs)
  (declare (xargs :guard t))
  (cond ((equal new old) ws)
        ((and (consp new) (equal (cdr new) old))
         (fn-ctl-prepend (fn-ctl-article-withdrawals (car new) verdicts records
                                                     configs)
                         (if (consp (car new))
                             (fn-ctl-resolve-tlocks ws (fn-article-msgid (car new))
                                                    records)
                           ws)))
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
                                      fn-ctl-config-at fn-ctl-row-event fn-ctl-row-control
                                      fn-ctl-w-with-tlocks fn-ctl-lookup-verdict)
           :use ((:instance fn-ctl-withdrawal-plan-names-its-cause
                  (cause (fn-article-msgid a))
                  (verdict (fn-ctl-lookup-verdict (fn-article-msgid a) verdicts))
                  (target (fn-ctl-control-target
                           (fn-hf-control
                            (fn-held-facts
                             (fn-ctl-event-row
                              (fn-ctl-row-event (fn-article-msgid a) records))))))
                  (keys (fn-ctl-control-keys
                         (fn-hf-control
                          (fn-held-facts
                           (fn-ctl-event-row
                            (fn-ctl-row-event (fn-article-msgid a) records))))))
                  (cfg (fn-ctl-config-at
                        (fn-store-event-txid (fn-ctl-row-event (fn-article-msgid a) records))
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
; Resolving the records that target M changes no other article's standing.
(defthm fn-ctl-withdrawn-by-p-of-set-tlocks-other
  (implies (not (equal m (fn-article-msgid x)))
           (equal (fn-ctl-withdrawn-by-p x (fn-ctl-set-tlocks ws m locks) arts verdicts)
                  (fn-ctl-withdrawn-by-p x ws arts verdicts)))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawal-effect fn-ctl-effect-withdrawsp
                                      fn-ctl-has-msgid-p fn-ctl-w-with-tlocks))))

(defthm fn-ctl-visible-filter-of-set-tlocks-other
  (implies (not (member-equal m (fn-article-msgids xs)))
           (equal (fn-ctl-visible-filter xs (fn-ctl-set-tlocks ws m locks) arts verdicts)
                  (fn-ctl-visible-filter xs ws arts verdicts)))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawn-by-p fn-ctl-set-tlocks))))

; With the records naming the new article resolved (the cons arm).
(defthm fn-ctl-visible-of-grown-and-resolved
  (implies (and (not (member-equal (fn-article-msgid a) (fn-article-msgids old)))
                (fn-ctl-verdicts-grow-by-p verdicts old-verdicts a))
           (equal (fn-ctl-visible-articles
                   old (fn-ctl-prepend (fn-ctl-article-withdrawals a verdicts records configs)
                                       (fn-ctl-set-tlocks ws (fn-article-msgid a) locks))
                   verdicts)
                  (fn-ctl-visible-articles old ws old-verdicts)))
  :hints (("Goal" :in-theory (disable fn-ctl-visible-filter fn-ctl-article-withdrawals
                                      fn-ctl-set-tlocks fn-ctl-verdicts-grow-by-p
                                      fn-ctl-visible-of-grown-records-and-verdicts)
           :use ((:instance fn-ctl-visible-of-grown-records-and-verdicts
                            (ws (fn-ctl-set-tlocks ws (fn-article-msgid a) locks)))
                 (:instance fn-ctl-visible-filter-of-set-tlocks-other
                            (m (fn-article-msgid a)) (xs old) (arts old)
                            (verdicts old-verdicts))))))

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
  :hints (("Goal" :in-theory (e/d (fn-ctl-visible-add-is-visible
                                   fn-ctl-refresh-withdrawals fn-ctl-refresh-visible)
                                  (fn-ctl-visible-add fn-ctl-visible-articles
                                   fn-ctl-article-withdrawals fn-ctl-verdicts-grow-by-p
                                   fn-ctl-articles-withdrawals fn-ctl-prepend-is-append
                                   fn-ctl-set-tlocks fn-ctl-row-control)))))

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
; The journal a Store holds: one entry (TXID CAUSE VERDICT TARGET KEYS TLOCKS) per
; withdrawing article of ARTS, newest first, the shape
; `fn-ctl-journal-withdrawals' (books/control-authority.lisp) decides.

(defun fn-ctl-archive-entries (arts verdicts records)
  (declare (xargs :guard t))
  (if (consp arts)
      (let* ((a (car arts))
             (m (and (consp a) (fn-article-msgid a)))
             (e (and (consp a) (fn-ctl-row-event m records)))
             (control (if e (fn-hf-control (fn-held-facts (fn-ctl-event-row e))) nil))
             (target (fn-ctl-control-target control))
             (rest (fn-ctl-archive-entries (cdr arts) verdicts records)))
        (if target
            (cons (list (fn-store-event-txid e)
                        m
                        (fn-ctl-lookup-verdict m verdicts)
                        target
                        (fn-ctl-control-keys control)
                        (fn-ctl-control-locks (fn-ctl-row-control target records)))
                  rest)
          rest))
    nil))

(defthm fn-ctl-journal-withdrawals-of-append
  (equal (fn-ctl-journal-withdrawals (append xs ys) configs)
         (append (fn-ctl-journal-withdrawals xs configs)
                 (fn-ctl-journal-withdrawals ys configs)))
  :hints (("Goal" :in-theory (disable fn-ctl-withdrawal-plan fn-ctl-withdrawalp
                                      fn-ctl-config-at fn-ctl-w-with-tlocks))))

; The rebuild the owner runs at a discontinuity (start, reopen: recovery)
; is the journal definition over the archive's entries.
(defthm fn-ctl-articles-withdrawals-is-the-journal
  (equal (fn-ctl-articles-withdrawals arts verdicts records configs)
         (fn-ctl-journal-withdrawals (fn-ctl-archive-entries arts verdicts records)
                                     configs))
  :hints (("Goal" :induct (fn-ctl-archive-entries arts verdicts records)
           :in-theory (disable fn-ctl-withdrawal-plan fn-ctl-withdrawalp
                               fn-ctl-config-at fn-ctl-row-event fn-ctl-row-control
                               fn-ctl-lookup-verdict fn-ctl-w-with-tlocks))))

; -----------------------------------------------------------------------------
; Stability of the entries as the Store grows.  MORE's rows carry only
; Message-IDs in MS (every other event of MORE, an acknowledgement or a
; configuration record, carries no row).

(defun fn-ctl-rows-only-p (records ms)
  (declare (xargs :guard (true-listp ms)))
  (if (consp records)
      (and (let ((row (fn-ctl-event-row (car records))))
             (or (not row) (member-equal (fn-record-msgid row) ms)))
           (fn-ctl-rows-only-p (cdr records) ms))
    t))

(defthm fn-ctl-row-event-of-rows-only
  (implies (and (fn-ctl-rows-only-p more ms) (not (member-equal m ms)))
           (equal (fn-ctl-row-event m more) nil))
  :hints (("Goal" :in-theory (disable fn-ctl-event-row))))

; (1) A Message-ID outside MS keeps its row as the history grows by MORE.
(defthm fn-ctl-row-event-of-append-other
  (implies (and (fn-ctl-rows-only-p more ms) (not (member-equal m ms)))
           (equal (fn-ctl-row-event m (append r0 more))
                  (fn-ctl-row-event m r0)))
  :hints (("Goal" :in-theory (disable fn-ctl-event-row))))

(defthm fn-ctl-row-control-of-append-other
  (implies (and (fn-ctl-rows-only-p more ms) (not (member-equal m ms)))
           (equal (fn-ctl-row-control m (append r0 more))
                  (fn-ctl-row-control m r0)))
  :hints (("Goal" :in-theory (disable fn-ctl-row-event fn-ctl-event-row))))

; The entries with the target locks of target M replaced by LOCKS.
(defun fn-ctl-entries-set-tlocks (es m locks)
  (declare (xargs :guard t))
  (if (consp es)
      (cons (if (equal (fn-ctl-at 3 (car es)) m)
                (list (fn-ctl-at 0 (car es)) (fn-ctl-at 1 (car es))
                      (fn-ctl-at 2 (car es)) (fn-ctl-at 3 (car es))
                      (fn-ctl-at 4 (car es)) locks)
              (car es))
            (fn-ctl-entries-set-tlocks (cdr es) m locks))
    es))

; (2) Growing the history by rows of no article in ARTS: nothing changes.
(defthm fn-ctl-archive-entries-of-appended-nothing
  (implies (fn-ctl-rows-only-p more nil)
           (equal (fn-ctl-archive-entries arts verdicts (append r0 more))
                  (fn-ctl-archive-entries arts verdicts r0)))
  :hints (("Goal" :induct (fn-ctl-archive-entries arts verdicts r0)
           :in-theory (disable fn-ctl-row-event fn-ctl-row-control fn-ctl-event-row
                               fn-ctl-lookup-verdict))))

; (3) Growing the history by rows of one Message-ID M no article of ARTS
; carries: only the target locks of the entries naming M change, to M's.
(defthm fn-ctl-archive-entries-of-appended-one
  (implies (and (fn-ctl-rows-only-p more (list m))
                (not (member-equal m (fn-article-msgids arts))))
           (equal (fn-ctl-archive-entries arts verdicts (append r0 more))
                  (fn-ctl-entries-set-tlocks
                   (fn-ctl-archive-entries arts verdicts r0) m
                   (fn-ctl-control-locks (fn-ctl-row-control m (append r0 more))))))
  :hints (("Goal" :induct (fn-ctl-archive-entries arts verdicts r0)
           :in-theory (disable fn-ctl-row-event fn-ctl-row-control fn-ctl-event-row
                               fn-ctl-lookup-verdict))))

; (4) The journal of the entries with M's locks replaced is the journal with
; the records naming M resolved.
(defthm fn-ctl-w-with-tlocks-of-with-tlocks
  (equal (fn-ctl-w-with-tlocks (fn-ctl-w-with-tlocks w a) b)
         (fn-ctl-w-with-tlocks w b)))

(defthm fn-ctl-withdrawal-plan-names-its-target
  (implies (fn-ctl-withdrawalp (fn-ctl-withdrawal-plan cause verdict target keys cfg))
           (equal (fn-ctl-w-target (fn-ctl-withdrawal-plan cause verdict target keys cfg))
                  target))
  :hints (("Goal" :use fn-ctl-withdrawal-plan-record-is-bound
           :in-theory (disable fn-ctl-withdrawal-plan-record-is-bound))))

(defthm fn-ctl-journal-of-entries-set-tlocks
  (equal (fn-ctl-journal-withdrawals (fn-ctl-entries-set-tlocks es m locks) configs)
         (fn-ctl-set-tlocks (fn-ctl-journal-withdrawals es configs) m locks))
  :hints (("Goal" :induct (fn-ctl-entries-set-tlocks es m locks)
           :in-theory (disable fn-ctl-withdrawal-plan fn-ctl-withdrawalp
                               fn-ctl-config-at fn-ctl-w-with-tlocks))))

(defthm fn-ctl-set-tlocks-of-untargeted
  (implies (not (fn-ctl-targets-p ws m))
           (equal (fn-ctl-set-tlocks ws m locks) ws)))

(defthm fn-ctl-resolve-tlocks-is-set-tlocks
  (equal (fn-ctl-resolve-tlocks ws m records)
         (fn-ctl-set-tlocks ws m (fn-ctl-control-locks (fn-ctl-row-control m records))))
  :hints (("Goal" :in-theory (disable fn-ctl-row-control fn-ctl-set-tlocks))))

; (5) A verdict recorded for a Message-ID outside ARTS changes no entry.
(defthm fn-ctl-lookup-verdict-of-other-cons
  (implies (not (equal m k))
           (equal (fn-ctl-lookup-verdict k (cons (cons m v) verdicts))
                  (fn-ctl-lookup-verdict k verdicts))))

(defthm fn-ctl-archive-entries-of-new-verdict
  (implies (not (member-equal m (fn-article-msgids arts)))
           (equal (fn-ctl-archive-entries arts (cons (cons m v) verdicts) records)
                  (fn-ctl-archive-entries arts verdicts records)))
  :hints (("Goal" :in-theory (disable fn-ctl-row-event fn-ctl-row-control
                                      fn-ctl-lookup-verdict))))

; (6) Configuration records appended later carry larger txids than every
; entry: `fn-ctl-revoke-changes-decisions-not-records'.

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

; How the Store's history grew between two refreshes, as the refresh's arms
; read it: nothing new (no row appended); one article A consed on (only A's
; rows appended, A's Message-ID new); or a discontinuity (anything).
(defun fn-ctl-history-grows-by-p (more-r new old)
  (declare (xargs :guard t))
  (cond ((equal new old) (fn-ctl-rows-only-p more-r nil))
        ((and (consp new) (equal (cdr new) old))
         (if (consp (car new))
             (and (not (member-equal (fn-article-msgid (car new))
                                     (fn-article-msgids old)))
                  (fn-ctl-rows-only-p more-r (list (fn-article-msgid (car new)))))
           (fn-ctl-rows-only-p more-r nil)))
        (t t)))

; No configuration record appended: nothing to decide again (the refresh at
; which no configuration changed, the common case).
(defthm fn-ctl-configs-through-of-append-atom
  (implies (atom more)
           (equal (fn-ctl-configs-through txid (append configs more))
                  (fn-ctl-configs-through txid configs))))

(defthm fn-ctl-journal-of-append-atom
  (implies (atom more)
           (equal (fn-ctl-journal-withdrawals entries (append configs more))
                  (fn-ctl-journal-withdrawals entries configs)))
  :hints (("Goal" :induct (fn-ctl-journal-withdrawals entries configs)
           :in-theory (disable fn-ctl-withdrawal-plan fn-ctl-withdrawalp
                               fn-cfg-apply-record fn-ctl-w-with-tlocks))))

; The old records over the grown history: unchanged, or resolved for the one
; new Message-ID M.
(defthm fn-ctl-journal-of-old-entries-grown-by-nothing
  (implies (and (or (equal verdicts v0)
                    (and (consp verdicts) (consp (car verdicts))
                         (equal (cdr verdicts) v0)
                         (not (member-equal (car (car verdicts))
                                            (fn-article-msgids old)))))
                (or (atom more-c)
                    (fn-ctl-entries-below-p (fn-ctl-archive-entries old v0 r0)
                                            (fn-cfg-record-txid (car more-c))))
                (fn-ctl-rows-only-p more-r nil))
           (equal (fn-ctl-journal-withdrawals
                   (fn-ctl-archive-entries old verdicts (append r0 more-r))
                   (append c0 more-c))
                  (fn-ctl-journal-withdrawals (fn-ctl-archive-entries old v0 r0) c0)))
  :hints (("Goal" :cases ((equal verdicts v0))
           :in-theory (disable fn-ctl-journal-withdrawals fn-ctl-archive-entries
                               fn-ctl-entries-below-p fn-ctl-rows-only-p binary-append)
           :use ((:instance fn-ctl-archive-entries-of-grown-verdicts
                            (arts old) (records (append r0 more-r)))
                 (:instance fn-ctl-archive-entries-of-appended-nothing
                            (arts old) (verdicts v0) (more more-r))
                 (:instance fn-ctl-revoke-changes-decisions-not-records
                            (entries (fn-ctl-archive-entries old v0 r0))
                            (configs c0) (more more-c))))))

(defthm fn-ctl-journal-of-old-entries-grown-by-one
  (implies (and (or (equal verdicts v0)
                    (and (consp verdicts) (consp (car verdicts))
                         (equal (cdr verdicts) v0)
                         (not (member-equal (car (car verdicts))
                                            (fn-article-msgids old)))))
                (or (atom more-c)
                    (fn-ctl-entries-below-p (fn-ctl-archive-entries old v0 r0)
                                            (fn-cfg-record-txid (car more-c))))
                (fn-ctl-rows-only-p more-r (list m))
                (not (member-equal m (fn-article-msgids old))))
           (equal (fn-ctl-journal-withdrawals
                   (fn-ctl-archive-entries old verdicts (append r0 more-r))
                   (append c0 more-c))
                  (fn-ctl-set-tlocks
                   (fn-ctl-journal-withdrawals (fn-ctl-archive-entries old v0 r0) c0)
                   m (fn-ctl-control-locks (fn-ctl-row-control m (append r0 more-r))))))
  :hints (("Goal" :cases ((equal verdicts v0))
           :in-theory (disable fn-ctl-journal-withdrawals fn-ctl-archive-entries
                               fn-ctl-entries-below-p fn-ctl-rows-only-p binary-append
                               fn-ctl-set-tlocks fn-ctl-entries-set-tlocks
                               fn-ctl-row-control fn-ctl-control-locks)
           :use ((:instance fn-ctl-archive-entries-of-grown-verdicts
                            (arts old) (records (append r0 more-r)))
                 (:instance fn-ctl-archive-entries-of-appended-one
                            (arts old) (verdicts v0) (more more-r))
                 (:instance fn-ctl-revoke-changes-decisions-not-records
                            (entries (fn-ctl-archive-entries old v0 r0))
                            (configs c0) (more more-c))))))

; KEYSTONE (C3, live equals recovery).  Let the records an old view carries
; be the journal of its archive OLD under the durable inputs of its refresh
; (verdicts V0, Store records R0, configuration journal C0), the verdict
; list have grown by at most one pair for a Message-ID outside OLD, the
; configuration records appended since carry txids above every entry of
; OLD, and the history have grown by the rows of the new article only.
; Then the records the next refresh carries, over the grown inputs, are the
; journal of the new archive under those grown inputs: what recovery
; computes from the Store at that moment.  A cancel relayed ahead of its
; target is resolved to the target's locks when the target arrives
; (`fn-ctl-resolve-tlocks'), exactly as recovery reads them.  Subject:
; `fn-ctl-refresh-withdrawals', called by `fn-own-refresh'
; (books/owner.lisp) with RECORDS = the Store's records and CONFIGS =
; `fn-sn-config-history'; recovery (`fn-own-start') reaches its
; discontinuity arm.
(defthm fn-ctl-refresh-withdrawals-is-the-journal
  (implies (and (equal ws (fn-ctl-journal-withdrawals
                           (fn-ctl-archive-entries old v0 r0) c0))
                (or (equal verdicts v0)
                    (and (consp verdicts) (consp (car verdicts))
                         (equal (cdr verdicts) v0)
                         (not (member-equal (car (car verdicts))
                                            (fn-article-msgids old)))))
                (or (atom more-c)
                    (fn-ctl-entries-below-p (fn-ctl-archive-entries old v0 r0)
                                            (fn-cfg-record-txid (car more-c))))
                (fn-ctl-history-grows-by-p more-r new old))
           (equal (fn-ctl-refresh-withdrawals new old ws verdicts
                                              (append r0 more-r)
                                              (append c0 more-c))
                  (fn-ctl-journal-withdrawals
                   (fn-ctl-archive-entries new verdicts (append r0 more-r))
                   (append c0 more-c))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ctl-refresh-withdrawals fn-ctl-history-grows-by-p)
                           (fn-ctl-journal-withdrawals
                            fn-ctl-archive-entries fn-ctl-rows-only-p
                            fn-ctl-entries-below-p fn-ctl-article-withdrawals
                            fn-ctl-prepend-is-append fn-ctl-set-tlocks
                            fn-ctl-row-control fn-ctl-control-locks binary-append
                            fn-ctl-articles-withdrawals
                            fn-ctl-journal-of-old-entries-grown-by-nothing
                            fn-ctl-journal-of-old-entries-grown-by-one))
           :use ((:instance fn-ctl-journal-of-consed-entries
                            (a (car new)) (old (cdr new)) (verdicts verdicts)
                            (records (append r0 more-r)) (configs (append c0 more-c)))
                 (:instance fn-ctl-articles-withdrawals-is-the-journal
                            (arts new) (records (append r0 more-r))
                            (configs (append c0 more-c)))
                 (:instance fn-ctl-journal-of-old-entries-grown-by-nothing)
                 (:instance fn-ctl-journal-of-old-entries-grown-by-nothing
                            (old (cdr new)))
                 (:instance fn-ctl-journal-of-old-entries-grown-by-one
                            (old (cdr new)) (m (fn-article-msgid (car new))))))))

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
                    (:d fn-ctl-record-txid) (:d fn-ctl-row-event)
                    (:d fn-ctl-row-control) (:d fn-ctl-event-row)
                    (:d fn-ctl-article-plan) (:d fn-ctl-set-tlocks)
                    (:d fn-ctl-targets-p) (:d fn-ctl-resolve-tlocks)
                    (:d fn-ctl-rows-only-p) (:d fn-ctl-entries-set-tlocks)
                    (:d fn-ctl-history-grows-by-p)
                    (:d fn-ctl-event-msgid)))

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:rewrite fn-ctl-refresh-visible-is-visible)
                    (:rewrite fn-ctl-visible-add-is-visible)))
