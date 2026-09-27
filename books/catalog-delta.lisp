; fn: the committed delta and the served view as a version (wave 5, lane
; catalog-slice step 5, 2026-09-26; D33; the consolidation design 1.4, 4.4).
;
; A completion emits ONE delta (books/catalog-commit.lisp fn-cat-complete:
; the :article case); a cancel, a redecision and a policy change are the
; other kinds.  Every projection consumes the delta instead of comparing
; two worlds: the group and Message-ID projections ARE catalog columns, so
; their consumption is fn-cat-commit's own correspondence (PRF-201); the
; visibility and verdict columns consume :withdraw and :redecide by one
; export each; a :policy delta touches a RANGE of rows and is applied in
; bounded batches under a quantum, never in one unbounded step (D27).
;
;   (:article seq msgid numbers handle facts context)  fn-dart-p: a commit at SEQ
;   (:withdraw target by)          a cancel committed after its target: the target
;                                  row is withdrawn at the count (fn-cat-withdraw)
;   (:withdraw-pending msgid by)   a cancel committed before its target: no row
;                                  to mark; the target's initial visibility is the
;                                  commit's business (recorded, applied to no row)
;   (:redecide seq context)        a verdict under a new generation (fn-cat-redecide)
;   (:policy generation from to)   the rows [from, to) re-decided under GENERATION
;                                  from their bytes (fn-cat-recontext): RESUMABLE
;
; THE SERVED VIEW IS A VERSION.  A connection's view is a natural V, the
; catalog count when the view was taken: the reader sees rows seq < V, and
; a row withdrawn at W when V <= W (fn-cat-visible-at, books/catalog.lisp).
; No per-connection copy of the article list (fn-own-conn-archive, deletion
; map 4.4); a delta never changes a pinned version (C3 within a command);
; GROUP and LISTGROUP advance the connection's version to the count between
; commands (fn-view-advance).  The cancel-after-target case is the witness:
; a reader pinned before a cancel sees the article until it advances past
; the cancel's version (fn-view-cancel-after-target).
;
; Every step is bounded by its quantum (fn-cat-apply-delta-step-bounded);
; the one-shot application is the reference.  That the resumable run under
; any quanta equals the one-shot application is stated below as OPEN (not
; proved in this lane's budget; a ground check passes).
;
; PRF-202 as registered (fn-view-apply-is-refresh against fn-own-refresh's
; view) needs the maintained relation R of step 6 between the catalog and
; the owner; this book proves the delta's application and the version
; semantics over the catalog alone, and the record says so.

(in-package "ACL2")
(include-book "catalog-commit")

; -----------------------------------------------------------------------------
; The grammar.

(defun fn-delta-p (d)
  (declare (xargs :guard t))
  (and (consp d)
       (case (car d)
         (:article (fn-dart-p d))
         (:withdraw (and (true-listp d) (equal (len d) 3)
                         (natp (nth 1 d)) (natp (nth 2 d))))
         (:withdraw-pending (and (true-listp d) (equal (len d) 3)
                                 (fn-record-msgidp (nth 1 d)) (natp (nth 2 d))))
         (:redecide (and (true-listp d) (equal (len d) 3)
                         (natp (nth 1 d)) (fn-hc-p (nth 2 d))))
         (:policy (and (true-listp d) (equal (len d) 4)
                       (natp (nth 1 d)) (natp (nth 2 d)) (natp (nth 3 d))
                       (<= (nth 2 d) (nth 3 d))))
         (otherwise nil))))

(defun fn-delta-kind (d)
  (declare (xargs :guard (fn-delta-p d)))
  (car d))

(defthm fn-delta-p-of-delta-of-row
  (implies (and (natp seq) (fn-held-p row))
           (fn-delta-p (fn-delta-of-row seq row)))
  :hints (("Goal" :in-theory (enable fn-delta-of-row fn-dart-internals fn-held-p))))

; -----------------------------------------------------------------------------
; Re-deciding a row's context from its bytes under a generation.

(defun fn-cat-recontext (seq keyring generation fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp seq) (< seq (fn-cat-count fn-cat))
                              (fn-prin-keyringp keyring) (natp generation)
                              (< (fn-record-payload (fn-cat-at seq fn-cat))
                                 (fn-arena-count fn-arena)))))
  (let ((row (fn-cat-at seq fn-cat)))
    (fn-cat-redecide seq
                     (fn-held-context-of (fn-arena-payload (fn-record-payload row) fn-arena)
                                         keyring generation)
                     fn-cat)))



(local (defthm fn-cdl-payload-of-with-context
   (equal (fn-record-payload (fn-held-with-context h ctx)) (fn-record-payload h))
   :hints (("Goal" :in-theory (enable fn-held-with-context fn-record-internals
                                      fn-held-internals)))))

(defthm fn-cat-redecide-keeps-handles
  (implies (and (natp seq) (< seq (fn-cat-count fn-cat)))
           (equal (fn-record-payload (fn-cat-at k (fn-cat-redecide seq ctx fn-cat)))
                  (fn-record-payload (fn-cat-at k fn-cat)))))

(defthm fn-cat-redecide-count
  (implies (and (natp seq) (< seq (fn-cat-count fn-cat)))
           (equal (fn-cat-count (fn-cat-redecide seq ctx fn-cat)) (fn-cat-count fn-cat))))

(defthm fn-cat-handles-inp-of-redecide
  (implies (and (natp seq) (< seq (fn-cat-count fn-cat)))
           (equal (fn-cat-handles-inp n fn-arena (fn-cat-redecide seq ctx fn-cat))
                  (fn-cat-handles-inp n fn-arena fn-cat))))

; The rows [i, to) re-decided, oldest first: the reference application of
; a :policy delta.
(defun fn-cat-recontext-range (i to keyring generation fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp i) (natp to) (<= to (fn-cat-count fn-cat))
                              (fn-prin-keyringp keyring) (natp generation)
                              (fn-cat-handles-inp to fn-arena fn-cat))
                  :measure (nfix (- to i))
                  :verify-guards nil))
  (if (or (not (natp i)) (not (natp to)) (>= i to))
      fn-cat
    (let ((fn-cat (fn-cat-recontext i keyring generation fn-arena fn-cat)))
      (fn-cat-recontext-range (+ i 1) to keyring generation fn-arena fn-cat))))

(defthm fn-cat-recontext-range-count
  (implies (<= to (fn-cat-count fn-cat))
           (equal (fn-cat-count (fn-cat-recontext-range i to keyring generation fn-arena fn-cat))
                  (fn-cat-count fn-cat)))
  :hints (("Goal" :induct (fn-cat-recontext-range i to keyring generation fn-arena fn-cat)
           :in-theory (e/d (fn-cat-recontext)
                           (fn-cat-redecide-is-update-nth fn-cat-count-is-len fn-cat-at-is-nth
                            fn-cat-p-is-held-listp)))))

(defthm fn-cat-recontext-range-keeps-handles
  (implies (<= to (fn-cat-count fn-cat))
           (equal (fn-cat-handles-inp n fn-arena
                                      (fn-cat-recontext-range i to keyring generation
                                                              fn-arena fn-cat))
                  (fn-cat-handles-inp n fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-cat-recontext-range i to keyring generation fn-arena fn-cat)
           :in-theory (e/d (fn-cat-recontext)
                           (fn-cat-redecide-is-update-nth fn-cat-count-is-len fn-cat-at-is-nth
                            fn-cat-p-is-held-listp)))))

(verify-guards fn-cat-recontext-range
  :hints (("Goal" :in-theory (disable fn-cat-p-is-held-listp fn-cat-count-is-len fn-cat-at-is-nth
                                      fn-cat-redecide-is-update-nth)
           :use ((:instance fn-cat-handles-inp-at (n to) (seq i))))))

; -----------------------------------------------------------------------------
; The one-shot application: the reference.

(defun fn-cat-apply-delta (d keyring fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (fn-delta-p d) (fn-prin-keyringp keyring)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :guard-hints (("Goal" :in-theory (e/d (fn-delta-p)
                                                        (fn-cat-p-is-held-listp fn-cat-count-is-len
                                                         fn-cat-at-is-nth))))))
  (case (car d)
    (:withdraw (if (< (nth 1 d) (fn-cat-count fn-cat))
                   (fn-cat-withdraw (nth 1 d) (nth 2 d) fn-cat)
                 fn-cat))
    (:redecide (if (< (nth 1 d) (fn-cat-count fn-cat))
                   (fn-cat-redecide (nth 1 d) (nth 2 d) fn-cat)
                 fn-cat))
    (:policy (fn-cat-recontext-range (nth 2 d) (min (nth 3 d) (fn-cat-count fn-cat))
                                     keyring (nth 1 d) fn-arena fn-cat))
    ; :article is the commit's own effect; :withdraw-pending marks no row.
    (otherwise fn-cat)))

; -----------------------------------------------------------------------------
; The resumable application.  A cursor is the next row of a :policy range;
; one step re-decides at most QUANTUM rows and says whether it is done.
; The other kinds complete in one step.

(defun fn-cat-apply-delta-step (d cursor quantum keyring fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (fn-delta-p d) (natp cursor) (posp quantum)
                              (fn-prin-keyringp keyring)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :guard-hints (("Goal" :in-theory (e/d (fn-delta-p)
                                                        (fn-cat-p-is-held-listp fn-cat-count-is-len
                                                         fn-cat-at-is-nth))))))
  (if (eq (car d) :policy)
      (let* ((to (min (nfix (nth 3 d)) (fn-cat-count fn-cat)))
             (from (max (nfix cursor) (nfix (nth 2 d))))
             (stop (min to (+ from (nfix quantum))))
             (fn-cat (fn-cat-recontext-range from stop keyring (nth 1 d) fn-arena fn-cat)))
        (mv stop (>= stop to) fn-cat))
    (let ((fn-cat (fn-cat-apply-delta d keyring fn-arena fn-cat)))
      (mv cursor t fn-cat))))

; What a step answers: its cursor and whether it is done, with the step
; closed (the measure and the keystone read these).
(defthm fn-cat-apply-delta-step-cursor
  (equal (mv-nth 0 (fn-cat-apply-delta-step d cursor quantum keyring fn-arena fn-cat))
         (if (eq (car d) :policy)
             (min (min (nfix (nth 3 d)) (fn-cat-count fn-cat))
                  (+ (max (nfix cursor) (nfix (nth 2 d))) (nfix quantum)))
           cursor))
  :hints (("Goal" :in-theory (e/d (fn-cat-apply-delta-step)
                                  (fn-cat-recontext-range fn-cat-apply-delta
                                   fn-cat-count-is-len fn-cat-at-is-nth fn-cat-p-is-held-listp)))))

(defthm fn-cat-apply-delta-step-done
  (equal (mv-nth 1 (fn-cat-apply-delta-step d cursor quantum keyring fn-arena fn-cat))
         (if (eq (car d) :policy)
             (>= (min (min (nfix (nth 3 d)) (fn-cat-count fn-cat))
                      (+ (max (nfix cursor) (nfix (nth 2 d))) (nfix quantum)))
                 (min (nfix (nth 3 d)) (fn-cat-count fn-cat)))
           t))
  :hints (("Goal" :in-theory (e/d (fn-cat-apply-delta-step)
                                  (fn-cat-recontext-range fn-cat-apply-delta
                                   fn-cat-count-is-len fn-cat-at-is-nth fn-cat-p-is-held-listp)))))

(defthm fn-cat-apply-delta-step-catalog
  (equal (mv-nth 2 (fn-cat-apply-delta-step d cursor quantum keyring fn-arena fn-cat))
         (if (eq (car d) :policy)
             (fn-cat-recontext-range (max (nfix cursor) (nfix (nth 2 d)))
                                     (min (min (nfix (nth 3 d)) (fn-cat-count fn-cat))
                                          (+ (max (nfix cursor) (nfix (nth 2 d))) (nfix quantum)))
                                     keyring (nth 1 d) fn-arena fn-cat)
           (fn-cat-apply-delta d keyring fn-arena fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-cat-apply-delta-step)
                                  (fn-cat-recontext-range fn-cat-apply-delta
                                   fn-cat-count-is-len fn-cat-at-is-nth fn-cat-p-is-held-listp)))))

(in-theory (disable fn-cat-apply-delta-step))

; Run the steps to completion under a schedule of quanta (a list of
; positive naturals; the last quantum repeats).  The measure is the
; distance from the cursor to the delta's own range end.
(defun fn-cat-apply-in-quanta (d cursor quanta keyring fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (fn-delta-p d) (natp cursor) (fn-prin-keyringp keyring)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :measure (nfix (- (+ 1 (nfix (nth 3 d))) (nfix cursor)))
                  :hints (("Goal" :in-theory (disable fn-cat-count-is-len fn-cat-at-is-nth
                                                      fn-cat-p-is-held-listp)))
                  :verify-guards nil))
  (let ((q (if (and (consp quanta) (posp (car quanta))) (car quanta) 1)))
    (mv-let (cursor2 done fn-cat)
      (fn-cat-apply-delta-step d cursor q keyring fn-arena fn-cat)
      (if (or done (not (natp cursor)) (<= cursor2 cursor))
          fn-cat
        (fn-cat-apply-in-quanta d cursor2 (if (consp (cdr quanta)) (cdr quanta) quanta)
                                keyring fn-arena fn-cat)))))

; -----------------------------------------------------------------------------
; The theorems.

; A step touches at most QUANTUM rows.
(defthm fn-cat-apply-delta-step-bounded
  (implies (and (natp cursor) (posp quantum))
           (mv-let (cursor2 done fn-cat2)
             (fn-cat-apply-delta-step d cursor quantum keyring fn-arena fn-cat)
             (declare (ignore done fn-cat2))
             (<= cursor2 (+ (max cursor (nfix (nth 2 d))) quantum))))
  :rule-classes nil)

; The range split at any point in it is the range.
(local
 (defthm fn-cat-recontext-range-split
   (implies (and (natp i) (natp m) (natp to) (<= i m) (<= m to))
            (equal (fn-cat-recontext-range m to keyring generation fn-arena
                                           (fn-cat-recontext-range i m keyring generation
                                                                   fn-arena fn-cat))
                   (fn-cat-recontext-range i to keyring generation fn-arena fn-cat)))
   :hints (("Goal" :induct (fn-cat-recontext-range i m keyring generation fn-arena fn-cat)))))

; A range that starts at or past its end is the identity.
(local
 (defthm fn-cat-recontext-range-empty
   (implies (>= (nfix i) (nfix to))
            (equal (fn-cat-recontext-range i to keyring generation fn-arena fn-cat) fn-cat))))

; OPEN (catalog-slice-2, 2026-09-26): the theorem that the resumable
; application from the range's start, under any schedule of quanta, is the
; one-shot application (fn-cat-apply-in-quanta = fn-cat-apply-delta under
; fn-delta-p, natp cursor, cursor <= from).  Its inductive form (a run from a
; cursor inside the range is the remaining range) did not close within the
; lane's budget: the arithmetic over the nested min of the range end, the
; count and the quantum split into cases the split lemma above did not
; reach.  The ground check in tests/acl2/catalog-delta-tests.lisp (the
; :policy case one shot and in quanta (1) and (2) over a two-row catalog)
; passes by computation and is a check, not a proof.  PKT-585 names it.

; -----------------------------------------------------------------------------
; The served view as a version.

; GROUP and LISTGROUP: the connection's version becomes the count.
(defun fn-view-advance (fn-cat)
  (declare (xargs :stobjs fn-cat))
  (fn-cat-count fn-cat))

; What a reader at version V sees of row SEQ.
(defun fn-view-sees (v seq fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (natp v) (natp seq) (< seq (fn-cat-count fn-cat)))))
  (fn-cat-visible-at seq v fn-cat))

; A delta never moves a pinned version (C3 within a command): the version is
; a number the delta does not touch.  Stated as the definition of the pinned
; view's application, so a consumer that applies a delta to a connection
; changes nothing but the catalog.
(defun fn-view-apply (v d)
  (declare (xargs :guard (and (natp v) (fn-delta-p d))) (ignore d))
  v)

; KEYSTONE (the design's witness case): a cancel of TARGET committed when
; the count is W withdraws the target at W; a reader pinned at V <= W with
; TARGET < V still sees it; after the cancel's own commit the count is W + 1,
; and a reader who advances there (or past) does not.
(defthm fn-view-cancel-after-target
  (implies (and (natp target) (natp by) (natp v)
                (< target (fn-cat-count fn-cat))
                (null (fn-held-withdrawn (fn-cat-at target fn-cat)))
                (equal (car (fn-cat-apply-delta (list :withdraw target by) keyring fn-arena fn-cat))
                       (car (fn-cat-withdraw target by fn-cat))))
           (let ((c2 (fn-cat-withdraw target by fn-cat)))
             (and (equal (fn-held-withdrawn (fn-cat-at target c2))
                         (cons (fn-cat-count fn-cat) by))
                  (equal (fn-view-sees v target c2)
                         (and (< target v) (<= v (fn-cat-count fn-cat))))
                  (implies (and (< target v) (<= v (fn-cat-count fn-cat)))
                           (fn-view-sees v target c2))
                  (not (fn-view-sees (+ 1 (fn-cat-count fn-cat)) target c2)))))
  :hints (("Goal" :in-theory (enable fn-cat-mark-withdrawn fn-held-with-withdrawn
                                     fn-cat-visiblep fn-held-internals fn-record-internals))))
