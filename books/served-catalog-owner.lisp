; served-catalog-owner.lisp -- the catalog at the owner's entries (step 8 of
; the catalog slice, the R side; planning/evidence/catalog-slice-2026-09-26.md).
;
; The host maintains the catalog at three entries, each an ACL2 decision the
; host only plumbs (host/owner-host.lisp):
;   E  fn-sca-load-held-rows    at recovery (fn-owner-install-extended): the
;                               catalog of the installed store's ROWS, from
;                               empty -- plain article rows and the held
;                               article row of every signed composite
;                               (catalog-columns: signed-post's red) --
;                               reading no byte and sealing nothing
;                               (the records flip; fn-sca-load-history is
;                               the pre-flip load over wire records, which
;                               clears the arena, and the host no longer
;                               calls it);
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
; The prepare (T1) is fn-cat-prepare-sealed, called by the host after its one
; seal of the POST's buffer (fn-owner-cat-prepare-sealed): the pending holds
; the store's row, which names that sealed handle; it equals what
; books/catalog-commit.lisp fn-cat-prepare would have prepared
; (fn-cat-prepare-is-seal-then-prepare-sealed) without a second seal.
;
; R (books/catalog-relation.lisp fn-cat-history-relation) is established by E
; (fn-sca-ocl-relation-at-recover, fn-sca-ocl-relation-at-full-open, below,
; over the host's fn-sca-load-held-rows) and preserved by T2 in both forms
; (fn-sca-ocl-relation-of-finish below over the host's fn-sca-finish;
; fn-cat-ocl-relation-of-article-finish, fn-cat-relation-of-complete-hidden)
; and by T4 (fn-cat-ocl-relation-of-withdraw), all in books/catalog-entries
; and catalog-relation; the theorems below are this book's shapes of those
; keystones over the functions the host calls.
;
; The JOIN -- that the view a pin names in the catalog (books/served-catalog-
; chain.lisp fn-scr-view-of) holds the pinned archive's articles, the
; hypothesis fn-scr-catalogp carries -- is stated here as fn-sca-join.  Its
; invariant form fn-scj-joinp and its preservation at the host's article and
; identity finishes are books/served-catalog-join.lisp (lane sca-join, PRF-302);
; its establishment at the opens and the row equation (numbering) are still
; OPEN, so the served chain keeps it as a hypothesis.

(in-package "ACL2")

(include-book "served-catalog-chain")
(include-book "catalog-entries")
(include-book "catalog-refresh")
(include-book "store-intern")
(include-book "catalog-availability-refinement")
(include-book "history-fold-refinement")   ; fn-row-composite-okp: what the intern makes of a row

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

; The row and view lemmas below never reason about a Message-ID's syntax;
; these rules fired uselessly through every Message-ID term (815 k prover
; steps in fn-sca-withdraw-targets-hides alone; catalog-columns, 2026-09-27).
(local (in-theory (disable fn-nntp-article-idp-is-consp fn-scat-article-idp-is-msgid-idp
                           fn-scat-msgid-idp fn-nntp-index-msgid-okp-stringp
                           fn-nntp-index-msgid-okp fn-cp-id-length-bound)))

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
                            fn-cat-count-is-len fn-cat-at-is-nth fn-cat-p-is-rowsp)))
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

; The targets of the withdrawals CAUSE contributed: every withdrawal record
; of the view's list whose cause is CAUSE (sca-join, 2026-09-27: the whole
; list, not the run at its head; the refresh prepends the newest article's
; records, but a head-run scan leans on an ordering of the list that no
; invariant carries, and the join's preservation, books/served-catalog-join
; fn-scj-view-after-finish-is-refresh, needs every record CAUSE made).  One
; pass over the view's withdrawal list, as the refresh's own
; fn-ctl-causes-p makes for every new article.
; Executes by a loop (PKT-877, lane serve-depth): the recursion took one
; control-stack frame per element.  The :logic is the recursion, unchanged;
; the :exec collects onto an accumulator and reverses it (revappend).
(defun fn-sca-targets-of-loop (cause ws acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp ws)
      (if (and (fn-ctl-withdrawalp (car ws)) (equal (fn-ctl-w-cause (car ws)) cause))
          (fn-sca-targets-of-loop cause (cdr ws) (cons (fn-ctl-w-target (car ws)) acc))
        (fn-sca-targets-of-loop cause (cdr ws) acc))
    (revappend acc nil)))

(defun fn-sca-targets-of (cause ws)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp ws)
           (if (and (fn-ctl-withdrawalp (car ws))
                    (equal (fn-ctl-w-cause (car ws)) cause))
               (cons (fn-ctl-w-target (car ws)) (fn-sca-targets-of cause (cdr ws)))
             (fn-sca-targets-of cause (cdr ws)))
         nil)
       :exec (fn-sca-targets-of-loop cause ws nil)))

(local
 (defthm fn-sca-targets-of-loop-is-revappend
   (equal (fn-sca-targets-of-loop cause ws acc)
          (revappend acc (fn-sca-targets-of cause ws)))
   :hints (("Goal" :induct (fn-sca-targets-of-loop cause ws acc)
                   :in-theory (union-theories '(fn-sca-targets-of-loop fn-sca-targets-of revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(verify-guards fn-sca-targets-of-loop)

(verify-guards fn-sca-targets-of
  :hints (("Goal"
           :in-theory
           (union-theories '(revappend fn-sca-targets-of)
                           (union-theories (theory 'minimal-theory)
                                           (executable-counterpart-theory :here)))
           :use
           ((:instance fn-sca-targets-of-loop-is-revappend (acc nil))))))


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

; -----------------------------------------------------------------------------
; The records flip: the prepare after the host's one seal (T1), and E over
; the store's ROWS.
;
; After the flip an accepted article's payload is a handle into the arena
; (books/payload-arena.lisp) and the store's history is ROWS: held records
; (books/held-record.lisp), composite rows and the other events, interned by
; the open (books/store-intern.lisp).  On a POST the store prepares the row
; at the arena's count WITHOUT sealing (fn-intern-row-at), and the host seals
; the buffer next (fn-arena-seal-buffer): after that seal the row names the
; newest handle.  The catalog's prepare is then the store's row itself
; (fn-cat-prepare-sealed): one seal per POST, where fn-cat-prepare interns
; the buffer a second time.  At recovery the catalog commits the store's
; rows as they are (fn-sca-load-held-rows): it reads no byte and seals
; nothing, where fn-sca-load-history clears the arena under the store's
; handles and re-interns wire records.

; T1 after the seal: the pending commit holds ROW when ROW names the newest
; handle; refused by name when a commit is pending (:pending, as
; fn-cat-prepare) or when ROW names any other handle (:not-sealed).
(defun fn-cat-prepare-sealed (w row plan reservation pending fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)))
  (cond (pending (list :pending))
        ((and (natp (fn-record-payload row))
              (equal (fn-record-payload row) (1- (fn-arena-count fn-arena))))
         (let ((expected (fn-cat-count fn-cat)))
           (fn-pc-make (cons (nfix (fn-record-txid w)) expected)
                       expected row plan reservation)))
        (t (list :not-sealed))))

(local (defthm fn-sca-pc-fields-of-make
   (and (equal (fn-pc-token (fn-pc-make token expected held plan reservation)) token)
        (equal (fn-pc-expected (fn-pc-make token expected held plan reservation)) expected)
        (equal (fn-pc-held (fn-pc-make token expected held plan reservation)) held)
        (equal (fn-pc-plan (fn-pc-make token expected held plan reservation)) plan)
        (equal (fn-pc-reservation (fn-pc-make token expected held plan reservation))
               reservation))
   :hints (("Goal" :in-theory (enable fn-pc-internals)))))

(local (defthm fn-sca-pc-p-of-make
   (implies (and (natp txid) (natp expected) (fn-held-p held))
            (fn-pc-p (fn-pc-make (cons txid expected) expected held plan reservation)))
   :hints (("Goal" :in-theory (e/d (fn-pc-p fn-pc-internals fn-pc-tokenp fn-pc-anyp)
                                   (fn-held-p))))))

(local (defthm fn-sca-seal-buffer-is-seal-list
   (equal (fn-arena-seal-buffer fn-octets fn-arena)
          (fn-arena-seal-list (fn-octets-list fn-octets) fn-arena))
   :hints (("Goal" :use ((:instance fn-cat-intern-is-intern-list))
            :in-theory (e/d (fn-cat-intern fn-cat-intern-list fn-held-wire)
                            (fn-cat-intern-is-intern-list))))))

(local (defthm fn-sca-payload-of-row-at
   (equal (fn-record-payload (fn-intern-row-at w keyring generation h)) h)
   :hints (("Goal" :in-theory (enable fn-intern-row-at)))))

(local (defthm fn-sca-arena-count-natp
   (natp (fn-arena-count fn-arena))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-arena-count-is-len)))))

(local (defthm fn-sca-record-p-shapep
   (implies (fn-record-p w) (fn-record-shapep w))
   :hints (("Goal" :in-theory (enable fn-record-p)))))

; KEYSTONE (T1, one seal per POST): the store's row at the arena's count A,
; after the host's seal of the buffer, is prepared: the pending commit's held
; row is exactly the row catalog-slice's intern would have built (so the
; completion and relation theorems over fn-cat-prepare's pending describe
; it), its handle is A's count, the seal's new handle holds the buffer's
; octets, and when those octets are W's payload the held row materializes
; in the sealed arena to W itself.
(defthm fn-cat-prepare-sealed-names-the-sealed-handle
  (implies (and (fn-record-p w) (natp generation))
           (let* ((row (fn-intern-row-at w keyring generation (fn-arena-count fn-arena)))
                  (arena2 (fn-arena-seal-buffer fn-octets fn-arena))
                  (pc (fn-cat-prepare-sealed w row plan reservation nil arena2 fn-cat)))
             (and (fn-pc-p pc)
                  (equal (fn-pc-token pc) (cons (nfix (fn-record-txid w)) (fn-cat-count fn-cat)))
                  (equal (fn-pc-expected pc) (fn-cat-count fn-cat))
                  (equal (fn-pc-held pc) (mv-nth 0 (fn-cat-intern-list w keyring generation fn-arena)))
                  (equal (fn-pc-plan pc) plan)
                  (equal (fn-pc-reservation pc) reservation)
                  (equal (fn-record-payload (fn-pc-held pc)) (fn-arena-count fn-arena))
                  (equal (fn-arena-count arena2) (+ 1 (fn-arena-count fn-arena)))
                  (equal (fn-arena-payload (fn-arena-count fn-arena) arena2)
                         (fn-octets-list fn-octets))
                  (implies (equal (fn-octets-list fn-octets) (fn-record-payload w))
                           (equal (fn-held-wire-of (fn-pc-held pc) arena2) w)))))
  :hints (("Goal" :in-theory (e/d (fn-cat-prepare-sealed)
                                  (fn-intern-row-at fn-cat-intern-list fn-held-wire-of
                                   fn-pc-make fn-pc-p fn-record-p
                                   fn-arena-payload-is-nth fn-arena-count-is-len
                                   fn-arena-seal-list-is-append fn-arena-seal-buffer-is-append
                                   fn-cat-count-is-len))
           :use ((:instance fn-cat-intern-list-is-row-at-count)
                 (:instance fn-held-p-of-intern-list)
                 (:instance fn-intern-list-handle)
                 (:instance fn-arena-seal-new-handle (xs (fn-octets-list fn-octets)))
                 (:instance fn-arena-seal-count (xs (fn-octets-list fn-octets)))
                 (:instance fn-cat-intern-list-materializes))
           :do-not-induct t)))

; The equation with catalog-slice's prepare: over the buffer holding W's
; payload, fn-cat-prepare's commit IS fn-cat-prepare-sealed's over the row at
; the count and the sealed arena, and fn-cat-prepare's arena IS that sealed
; arena.  So everything proved of fn-cat-prepare's pending holds of this one.
(defthm fn-cat-prepare-is-seal-then-prepare-sealed
  (implies (and (fn-record-p w)
                (equal (fn-octets-list fn-octets) (fn-record-payload w)))
           (let ((row (fn-intern-row-at w keyring generation (fn-arena-count fn-arena)))
                 (arena2 (fn-arena-seal-buffer fn-octets fn-arena)))
             (and (equal (mv-nth 0 (fn-cat-prepare w plan reservation fn-octets keyring generation
                                                   pending fn-arena fn-cat))
                         (fn-cat-prepare-sealed w row plan reservation pending arena2 fn-cat))
                  (implies (not pending)
                           (equal (mv-nth 1 (fn-cat-prepare w plan reservation fn-octets keyring
                                                            generation pending fn-arena fn-cat))
                                  arena2)))))
  :hints (("Goal" :in-theory (e/d (fn-cat-prepare fn-cat-prepare-sealed)
                                  (fn-intern-row-at fn-cat-intern-list fn-cat-intern
                                   fn-pc-make fn-record-p
                                   fn-arena-payload-is-nth fn-arena-count-is-len
                                   fn-arena-seal-list-is-append fn-arena-seal-buffer-is-append
                                   fn-cat-count-is-len))
           :use ((:instance fn-cat-intern-is-intern-list)
                 (:instance fn-held-wire-of-wire-record)
                 (:instance fn-cat-intern-list-is-row-at-count)
                 (:instance fn-arena-seal-count (xs (fn-octets-list fn-octets))))
           :do-not-induct t)))

; Held-row loader definitions are shared with the narrow availability boundary.

; The kinds by shape: a held-shaped value (a catalog row) and a wire record's
; shape are no other event.
(local (defthm fn-sca-held-shape-is-no-other-event
   (implies (fn-held-shapep x)
            (and (not (fn-store-retention-event-p x))
                 (not (fn-stxe-p x)) (not (fn-stxk-p x)) (not (fn-stxa-p x))
                 (not (fn-hstxa-p x))
                 (not (fn-cpe-eventp x)) (not (fn-th-topic-eventp x))))
   :hints (("Goal" :use ((:instance fn-hstxa-p-forward-shape))
            :in-theory (e/d (fn-store-retention-event-p
                             fn-stxe-p fn-stxe-shapep fn-stxk-p fn-stxk-shapep
                             fn-stxa-p fn-stxa-shapep fn-cpe-eventp fn-held-shapep
                             fn-th-topic-eventp fn-th-local-admin-eventp)
                            (fn-hstxa-p))))))

(local (defthm fn-sca-record-shape-is-no-other-event
   (implies (fn-record-shapep x)
            (and (not (fn-store-retention-event-p x))
                 (not (fn-stxe-p x)) (not (fn-stxk-p x)) (not (fn-stxa-p x))
                 (not (fn-cpe-eventp x)) (not (fn-th-topic-eventp x))))
   :hints (("Goal" :in-theory (enable fn-record-shapep fn-store-retention-event-p
                                      fn-stxe-p fn-stxe-shapep fn-stxk-p fn-stxk-shapep
                                      fn-stxa-p fn-stxa-shapep fn-cpe-eventp
                                      fn-th-topic-eventp fn-th-local-admin-eventp)))))

(local (defthm fn-sca-held-wire-shapep
   (fn-record-shapep (fn-held-wire h b))
   :hints (("Goal" :in-theory (enable fn-held-wire fn-record-shapep fn-record-internals)))))

(local (defthm fn-sca-cat-rowp-held-shapep
   (implies (fn-cat-rowp x) (fn-held-shapep x))
   :hints (("Goal" :in-theory (enable fn-cat-rowp)))))

(local (defthm fn-sca-store-event-rowp-is-held
   (implies (and (fn-store-event-p x) (fn-cat-rowp x))
            (fn-held-p x))
   :hints (("Goal" :in-theory (union-theories '(fn-store-event-p)
                                              (theory 'minimal-theory))
            :use ((:instance fn-sca-cat-rowp-held-shapep)
                  (:instance fn-sca-held-shape-is-no-other-event))))))

; A store event of the composite shape is a composite row: no other kind
; has the tag and a catalog row in third place (a held row starts with its
; sequence; a keyring snapshot's third field is a number).
; No other kind of store event carries the composite's tag.
(local (defthm fn-sca-held-is-not-tagged-composite (implies (and (fn-held-p x) (consp x)) (not (equal (car x) :hstxa))) :hints (("Goal" :in-theory (enable fn-held-p fn-held-shapep fn-record-sequence fn-held-internals fn-record-internals fn-record-uint64p fn-held-accessors-are-the-wire-accessors)))))
(local (defthm fn-sca-ret-is-not-tagged-composite (implies (and (fn-store-retention-event-p x) (consp x)) (not (equal (car x) :hstxa))) :hints (("Goal" :in-theory (enable fn-store-retention-event-p)))))
(local (defthm fn-sca-stxe-is-not-tagged-composite (implies (and (fn-stxe-p x) (consp x)) (not (equal (car x) :hstxa))) :hints (("Goal" :in-theory (enable fn-stxe-p fn-stxe-shapep fn-stxe-sequence fn-record-uint32p)))))
(local (defthm fn-sca-stxk-is-not-tagged-composite (implies (and (fn-stxk-p x) (consp x)) (not (equal (car x) :hstxa))) :hints (("Goal" :in-theory (enable fn-stxk-p fn-stxk-shapep fn-stxk-sequence fn-record-uint32p)))))
(local (defthm fn-sca-cpe-is-not-tagged-composite (implies (and (fn-cpe-eventp x) (consp x)) (not (equal (car x) :hstxa))) :hints (("Goal" :in-theory (enable fn-cpe-eventp)))))
(local (defthm fn-sca-topic-is-not-tagged-composite (implies (and (fn-th-topic-eventp x) (consp x)) (not (equal (car x) :hstxa))) :hints (("Goal" :in-theory (enable fn-th-topic-eventp fn-th-local-admin-eventp)))))

(local (defthm fn-sca-composite-shape-is-composite
   (implies (and (fn-store-event-p x) (fn-sca-composite-shapep x))
            (fn-hstxa-p x))
   :hints (("Goal" :in-theory (union-theories '(fn-store-event-p fn-sca-composite-shapep
                                                fn-sca-held-is-not-tagged-composite
                                                fn-sca-ret-is-not-tagged-composite
                                                fn-sca-stxe-is-not-tagged-composite
                                                fn-sca-stxk-is-not-tagged-composite
                                                fn-sca-cpe-is-not-tagged-composite
                                                fn-sca-topic-is-not-tagged-composite)
                                              (theory 'minimal-theory))))))

(local (defthm fn-sca-composite-held-is-held
   (implies (fn-hstxa-p x) (fn-held-p (fn-hstxa-held x)))
   :hints (("Goal" :in-theory (enable fn-hstxa-p fn-hstxa-held)))))

(defthm fn-sca-held-rowsp-of-record-values
  (implies (fn-sf-record-valuesp rows) (fn-sca-held-rowsp rows))
  :hints (("Goal" :induct (fn-sca-held-rowsp rows)
           :in-theory (e/d (fn-sf-record-valuesp fn-sca-composite-shapep)
                           (fn-store-event-p fn-held-p fn-cat-rowp fn-hstxa-p)))))

; A store event that is no held record materializes to no wire record.
(local (defthm fn-sca-other-event-wire-not-record
   (implies (and (fn-store-event-p x) (not (fn-held-p x)))
            (not (fn-record-p (fn-row-wire-of x fn-arena))))
   :hints (("Goal" :cases ((fn-hstxa-p x))
            :in-theory (e/d (fn-store-event-p fn-row-wire-of)
                            (fn-record-p fn-held-p fn-hstxa-p fn-stxa-p
                             fn-store-retention-event-p fn-stxe-p fn-stxk-p
                             fn-cpe-eventp fn-th-topic-eventp fn-row-bytes))
            :use ((:instance fn-record-is-no-other-wire-event)
                  (:instance fn-stxa-is-no-other-wire-event (x (fn-hstxa-stxa x)))
                  (:instance fn-hstxa-p-fields))))))

; A held row materializes, through a handle in the arena, to its wire.
(local (defthm fn-sca-row-wire-of-held
   (implies (and (fn-held-p h) (fn-row-handle-inp h fn-arena))
            (equal (fn-row-wire-of h fn-arena) (fn-held-wire-of h fn-arena)))
   :hints (("Goal" :in-theory (enable fn-row-wire-of fn-row-bytes fn-held-wire-of
                                      fn-row-handle-inp)))))

; A held row whose wire is a wire event materializes to a wire record.
(local (defthm fn-sca-held-wire-event-is-record
   (implies (and (fn-held-p h) (fn-row-handle-inp h fn-arena)
                 (fn-wire-event-p (fn-row-wire-of h fn-arena)))
            (fn-record-p (fn-row-wire-of h fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-held-wire-of fn-wire-event-p)
                                   (fn-held-p fn-record-p fn-held-wire fn-row-wire-of
                                    fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
                                    fn-cpe-eventp fn-th-topic-eventp fn-arena-payload-is-nth
                                    fn-record-shapep))
            :use ((:instance fn-sca-record-shape-is-no-other-event
                             (x (fn-held-wire h (fn-arena-payload (fn-record-payload h) fn-arena))))
                  (:instance fn-sca-held-wire-shapep
                             (b (fn-arena-payload (fn-record-payload h) fn-arena))))))))

; The commit of an already-interned row, visible or withdrawn at its own
; index, is catalog-slice's completion of a pending that holds it
; (fn-cat-relation-of-complete, -complete-hidden): the step of E over rows.
(local (defthm fn-sca-complete-of-made
   (implies (equal e (fn-cat-count fn-cat))
            (and (equal (mv-nth 2 (fn-cat-complete (cons 0 e) (fn-pc-make (cons 0 e) e h nil nil)
                                                   fn-cat))
                        (fn-cat-commit h fn-cat))
                 (equal (mv-nth 2 (fn-cat-complete-hidden (cons 0 e) (fn-pc-make (cons 0 e) e h nil nil)
                                                          0 fn-cat))
                        (fn-cat-commit (fn-held-with-withdrawn h (cons e 0)) fn-cat))))
   :hints (("Goal" :in-theory (e/d (fn-cat-complete fn-cat-complete-hidden)
                                   (fn-pc-make fn-cat-commit-is-append fn-cat-count-is-len))))))

(defthm fn-sca-commit-row-keeps-relation
  (implies (and (fn-cat-history-relation records fn-arena fn-cat)
                (fn-held-p row) (fn-row-handle-inp row fn-arena)
                (fn-record-p (fn-row-wire-of row fn-arena)))
           (and (fn-cat-history-relation (append records (list (fn-row-wire-of row fn-arena)))
                                         fn-arena (fn-cat-commit row fn-cat))
                (fn-cat-history-relation
                 (append records (list (fn-row-wire-of row fn-arena))) fn-arena
                 (fn-cat-commit (fn-held-with-withdrawn row (cons (fn-cat-count fn-cat) 0)) fn-cat))))
  :hints (("Goal" :in-theory (e/d (fn-row-handle-inp)
                                  (fn-cat-history-relation fn-held-p fn-record-p fn-pc-make fn-pc-p
                                   fn-row-wire-of fn-held-wire-of fn-cat-complete fn-cat-complete-hidden
                                   fn-cat-commit-is-append fn-cat-count-is-len
                                   fn-arena-count-is-len fn-arena-payload-is-nth))
           :use ((:instance fn-cat-relation-of-complete
                            (pending (fn-pc-make (cons 0 (fn-cat-count fn-cat)) (fn-cat-count fn-cat)
                                                 row nil nil))
                            (token (cons 0 (fn-cat-count fn-cat)))
                            (w (fn-held-wire-of row fn-arena)))
                 (:instance fn-cat-relation-of-complete-hidden
                            (pending (fn-pc-make (cons 0 (fn-cat-count fn-cat)) (fn-cat-count fn-cat)
                                                 row nil nil))
                            (token (cons 0 (fn-cat-count fn-cat)))
                            (w (fn-held-wire-of row fn-arena)) (by 0))
                 (:instance fn-sca-complete-of-made (e (fn-cat-count fn-cat)) (h row))
                 (:instance fn-sca-pc-p-of-make (txid 0) (expected (fn-cat-count fn-cat))
                            (held row) (plan nil) (reservation nil)))
           :do-not-induct t)))

(local (defthm fn-sca-relation-of-non-article
   (implies (not (fn-record-p r))
            (equal (fn-cat-history-relation (append history (list r)) fn-arena fn-cat)
                   (fn-cat-history-relation history fn-arena fn-cat)))
   :hints (("Goal" :in-theory (e/d (fn-cat-history-relation)
                                   (fn-cat-count-is-len fn-cat-at-is-nth fn-cat-p-is-rowsp
                                    fn-cat-handles-inp fn-cat-wire-list fn-record-p))))))

(local (defthm fn-sca-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local (defthm fn-sca-handles-of-cons
   (implies (and (consp rows) (fn-rows-handles-inp rows fn-arena))
            (and (fn-rows-handles-inp (cdr rows) fn-arena)
                 (or (not (fn-held-p (car rows))) (fn-row-handle-inp (car rows) fn-arena))
                 (or (fn-held-p (car rows)) (not (fn-hstxa-p (car rows)))
                     (fn-row-handle-inp (fn-hstxa-held (car rows)) fn-arena))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-rows-handles-inp)
                                   (fn-held-p fn-hstxa-p fn-row-handle-inp))))))

(local (defthm fn-sca-composite-is-not-held
   (implies (fn-hstxa-p x) (not (fn-held-p x)))
   :hints (("Goal" :use ((:instance fn-hstxa-is-not-held))
            :in-theory (disable fn-hstxa-p fn-held-p)))))

(local (defthm fn-sca-composite-is-shaped
   (implies (fn-hstxa-p x) (fn-sca-composite-shapep x))
   :hints (("Goal" :use ((:instance fn-sca-composite-held-is-held)
                         (:instance fn-held-p-implies-cat-rowp (x (fn-hstxa-held x))))
            :in-theory (union-theories '(fn-sca-composite-shapep fn-hstxa-p)
                                       (theory 'minimal-theory))))))

(local (defthm fn-sca-composite-is-not-cat-row
   (implies (fn-hstxa-p x) (not (fn-cat-rowp x)))
   :hints (("Goal" :use ((:instance fn-sca-cat-rowp-held-shapep)
                         (:instance fn-sca-held-shape-is-no-other-event))
            :in-theory (disable fn-hstxa-p fn-cat-rowp fn-held-shapep)))))

; One row of E: an article row committed (visible, or withdrawn at its own
; index), a composite row's article row the same, any other store event
; skipped; the history grows by the row's ARTICLE (fn-cat-history-article).
(local (defthm fn-sca-load-step
   (implies (and (fn-cat-history-relation history fn-arena fn-cat)
                 (fn-store-event-p r)
                 (or (not (fn-held-p r)) (fn-row-handle-inp r fn-arena))
                 (or (fn-held-p r) (not (fn-hstxa-p r))
                     (fn-row-handle-inp (fn-hstxa-held r) fn-arena))
                 (fn-row-composite-okp r fn-arena))
            (fn-cat-history-relation
             (append history (list (fn-cat-history-article r fn-arena))) fn-arena
             (fn-sca-load-held-row r view-index fn-cat)))
   :hints (("Goal" :cases ((fn-held-p r) (fn-hstxa-p r))
            :in-theory (union-theories '(fn-sca-relation-of-non-article fn-sca-load-held-row
                                         fn-cat-history-article fn-row-composite-okp
                                         (:executable-counterpart fn-cat-rowp)
                                         (:executable-counterpart fn-hstxa-p)
                                         (:executable-counterpart fn-held-p)
                                         (:executable-counterpart fn-store-event-p)
                                         (:executable-counterpart fn-sca-composite-shapep))
                                       (theory 'minimal-theory))
            :use ((:instance fn-sca-store-event-rowp-is-held (x r))
                  (:instance fn-sca-composite-shape-is-composite (x r))
                  (:instance fn-sca-composite-is-shaped (x r))
                  (:instance fn-sca-composite-is-not-cat-row (x r))
                  (:instance fn-sca-composite-is-not-held (x r))
                  (:instance fn-sca-composite-held-is-held (x r))
                  (:instance fn-sca-other-event-wire-not-record (x r))
                  (:instance fn-held-p-implies-cat-rowp (x r))
                  (:instance fn-sca-commit-row-keeps-relation (records history) (row r))
                  (:instance fn-sca-commit-row-keeps-relation (records history)
                             (row (fn-hstxa-held r))))))))

(local (defun fn-sca-held-ind (rows history view-index fn-arena fn-cat)
   (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil)
            (irrelevant history))
   (if (consp rows)
       (let ((fn-cat (fn-sca-load-held-row (car rows) view-index fn-cat)))
         (fn-sca-held-ind (cdr rows)
                          (append history (list (fn-cat-history-article (car rows) fn-arena)))
                          view-index fn-arena fn-cat))
     fn-cat)))

(defthm fn-sca-load-held-rows-from-keeps-relation
  (implies (and (fn-cat-history-relation history fn-arena fn-cat)
                (fn-sf-record-valuesp rows)
                (fn-rows-handles-inp rows fn-arena)
                (fn-rows-composites-okp rows fn-arena))
           (fn-cat-history-relation (append history (fn-cat-history-articles rows fn-arena)) fn-arena
                                    (fn-sca-load-held-rows-from rows view-index fn-cat)))
  :hints (("Goal" :induct (fn-sca-held-ind rows history view-index fn-arena fn-cat)
           :expand ((fn-sca-load-held-rows-from rows view-index fn-cat)
                    (fn-cat-history-articles rows fn-arena)
                    (fn-sf-record-valuesp rows)
                    (fn-rows-composites-okp rows fn-arena))
           :in-theory (union-theories '(fn-sca-append-assoc fn-sca-relation-of-append-atom
                                        car-cons cdr-cons binary-append
                                        (:induction fn-sca-held-ind))
                                      (theory 'minimal-theory)))
          ("Subgoal *1/2" :expand ((fn-cat-history-articles rows fn-arena)
                                   (fn-sca-load-held-rows-from rows view-index fn-cat)))
          ("Subgoal *1/1" :use ((:instance fn-sca-handles-of-cons)
                                (:instance fn-sca-load-step (r (car rows)))))))


; Classification changes cached facts, never handles or materialized wire.
; Follow the actual available fold rather than the retained raw proof helper.
(local (defthm fn-sca-prepare-availability-keeps-handle-in
  (equal (fn-row-handle-inp (fn-cat-prepare-row-availability h fn-arena) fn-arena)
         (fn-row-handle-inp h fn-arena))
  :hints (("Goal" :in-theory (enable fn-row-handle-inp)))))

(local (defthm fn-sca-prepare-availability-keeps-held-wire-of
  (equal (fn-held-wire-of (fn-cat-prepare-row-availability h fn-arena) fn-arena)
         (fn-held-wire-of h fn-arena))
  :hints (("Goal" :in-theory (enable fn-held-wire-of)))))

(local (defthm fn-sca-prepare-availability-keeps-row-wire
  (implies (fn-held-p h)
           (equal (fn-row-wire-of (fn-cat-prepare-row-availability h fn-arena) fn-arena)
                  (fn-row-wire-of h fn-arena)))
  :hints (("Goal" :in-theory (enable fn-row-wire-of)))))

(local (defthm fn-sca-available-held-step-keeps-relation
  (implies (and (fn-cat-history-relation records fn-arena fn-cat)
                (fn-held-p h) (fn-row-handle-inp h fn-arena)
                (fn-record-p (fn-row-wire-of h fn-arena)))
           (fn-cat-history-relation
            (append records (list (fn-row-wire-of h fn-arena))) fn-arena
            (fn-sca-load-held-row (fn-cat-prepare-row-availability h fn-arena)
                                 view-index fn-cat)))
  :hints (("Goal" :use ((:instance fn-sca-commit-row-keeps-relation
                                 (row (fn-cat-prepare-row-availability h fn-arena))))
           :in-theory (e/d (fn-sca-load-held-row)
                           (fn-cat-history-relation fn-cat-prepare-row-availability
                            fn-cat-commit-is-append fn-held-p fn-cat-rowp
                            fn-row-handle-inp fn-row-wire-of fn-held-wire-of))))))

(local (defthm fn-sca-available-load-step
   (implies (and (fn-cat-history-relation history fn-arena fn-cat)
                 (fn-store-event-p r)
                 (or (not (fn-held-p r)) (fn-row-handle-inp r fn-arena))
                 (or (fn-held-p r) (not (fn-hstxa-p r))
                     (fn-row-handle-inp (fn-hstxa-held r) fn-arena))
                 (fn-row-composite-okp r fn-arena))
            (fn-cat-history-relation
             (append history (list (fn-cat-history-article r fn-arena))) fn-arena
             (fn-sca-load-held-available-row r view-index fn-arena fn-cat)))
   :hints (("Goal" :cases ((fn-held-p r) (fn-hstxa-p r))
            :in-theory (union-theories '(fn-sca-relation-of-non-article fn-sca-load-held-available-row
                                         fn-sca-load-held-row fn-cat-history-article fn-row-composite-okp
                                         (:executable-counterpart fn-cat-rowp)
                                         (:executable-counterpart fn-hstxa-p)
                                         (:executable-counterpart fn-held-p)
                                         (:executable-counterpart fn-store-event-p)
                                         (:executable-counterpart fn-sca-composite-shapep))
                                       (theory 'minimal-theory))
            :use ((:instance fn-sca-store-event-rowp-is-held (x r))
                  (:instance fn-sca-composite-shape-is-composite (x r))
                  (:instance fn-sca-composite-is-shaped (x r))
                  (:instance fn-sca-composite-is-not-cat-row (x r))
                  (:instance fn-sca-composite-is-not-held (x r))
                  (:instance fn-sca-composite-held-is-held (x r))
                  (:instance fn-sca-other-event-wire-not-record (x r))
                  (:instance fn-held-p-implies-cat-rowp (x r))
                  (:instance fn-sca-available-held-step-keeps-relation (records history) (h r))
                  (:instance fn-sca-available-held-step-keeps-relation (records history)
                             (h (fn-hstxa-held r))))))))

(local (defun fn-sca-held-available-ind (rows history view-index fn-arena fn-cat)
   (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil)
            (irrelevant history))
   (if (consp rows)
       (let ((fn-cat (fn-sca-load-held-available-row (car rows) view-index fn-arena fn-cat)))
         (fn-sca-held-available-ind (cdr rows)
                          (append history (list (fn-cat-history-article (car rows) fn-arena)))
                          view-index fn-arena fn-cat))
     fn-cat)))

(defthm fn-sca-load-held-available-from-keeps-relation
  (implies (and (fn-cat-history-relation history fn-arena fn-cat)
                (fn-sf-record-valuesp rows)
                (fn-rows-handles-inp rows fn-arena)
                (fn-rows-composites-okp rows fn-arena))
           (fn-cat-history-relation (append history (fn-cat-history-articles rows fn-arena)) fn-arena
                                    (fn-sca-load-held-available-from rows view-index fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-sca-held-available-ind rows history view-index fn-arena fn-cat)
           :expand ((fn-sca-load-held-available-from rows view-index fn-arena fn-cat)
                    (fn-cat-history-articles rows fn-arena)
                    (fn-sf-record-valuesp rows)
                    (fn-rows-composites-okp rows fn-arena))
           :in-theory (union-theories '(fn-sca-append-assoc fn-sca-relation-of-append-atom
                                        car-cons cdr-cons binary-append
                                        (:induction fn-sca-held-available-ind))
                                      (theory 'minimal-theory)))
          ("Subgoal *1/2" :expand ((fn-cat-history-articles rows fn-arena)
                                   (fn-sca-load-held-available-from rows view-index fn-arena fn-cat)))
          ("Subgoal *1/1" :use ((:instance fn-sca-handles-of-cons)
                                (:instance fn-sca-available-load-step (r (car rows)))))))

; KEYSTONE (E after the flip, with the signed articles): committing the
; store's rows from the cleared catalog establishes R over the rows'
; ARTICLES (fn-cat-history-articles: a held row and a composite row's held
; article row read by handle), under the invariants the open establishes of
; the rows: they are store events (fn-intern-events-are-store-events), their
; handles are in the arena (fn-intern-events-handles-in), and each is what
; the intern makes of a row (fn-rows-composites-okp,
; books/history-fold-refinement.lisp; fn-sca-intern-events-composites-okp
; below).  No byte is read and no payload sealed.
(defthm fn-sca-load-held-rows-establishes-relation
  (implies (and (fn-arena-p fn-arena)
                (fn-sf-record-valuesp rows)
                (fn-rows-handles-inp rows fn-arena)
                (fn-rows-composites-okp rows fn-arena))
           (fn-cat-history-relation (fn-cat-history-articles rows fn-arena) fn-arena
                                    (fn-sca-load-held-rows rows view-index fn-arena fn-cat)))
  :hints (("Goal" :use ((:instance fn-sca-load-held-available-from-keeps-relation
                                   (history nil) (fn-cat nil)))
           :in-theory (e/d (fn-sca-load-held-rows fn-cat-history-relation)
                           (fn-sca-load-held-available-from-keeps-relation fn-sca-load-held-available-from
                            fn-cat-history-articles fn-sf-record-valuesp fn-rows-handles-inp
                            fn-rows-composites-okp)))))

; The installed store's rows are store events: the owner's live relation
; carries the store's structural state (books/owner-commit-carried.lisp
; fn-ccar-ocl-relation-carries-sn-statep), whose record list is one.
(defthm fn-sca-ocl-store-rows-are-values
  (implies (fn-ocl-relation oc)
           (fn-sf-record-valuesp (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
  :hints (("Goal" :use ((:instance fn-ccar-ocl-relation-carries-sn-statep))
           :in-theory (e/d (fn-sn-statep fn-sf-statep)
                           (fn-ocl-relation fn-sf-phase-shapep fn-sf-success-listp fn-node-statep)))))

; The open's intern makes every row what fn-rows-composites-okp names
; (books/history-fold-refinement.lisp fn-intern-event-composite-okp, one
; event; below, the list), and a later seal keeps what a row reads.
; What a held row reads survives a later seal (the arena grows at its end).
(local (defthm fn-sca-nth-of-append-below-len
   (implies (and (natp i) (< i (len a)))
            (equal (nth i (append a b)) (nth i a)))
   :hints (("Goal" :in-theory (enable nth)))))

(local (defthm fn-sca-row-wire-of-held-survives-seal
   (implies (and (fn-held-p h) (fn-row-handle-inp h fn-arena))
            (and (equal (fn-row-wire-of h (fn-arena-seal-list xs fn-arena))
                        (fn-row-wire-of h fn-arena))
                 (fn-row-handle-inp h (fn-arena-seal-list xs fn-arena))))
   :hints (("Goal" :in-theory (e/d (fn-row-wire-of fn-row-bytes fn-row-handle-inp
                                    fn-held-wire-of fn-arena-payload-is-nth
                                    fn-arena-seal-list-is-append fn-arena-count-is-len)
                                   (fn-held-p fn-held-wire))))))

(local (defthm fn-sca-composite-okp-survives-seal
   (implies (and (fn-rows-handles-inp (list row) fn-arena)
                 (fn-row-composite-okp row fn-arena))
            (and (fn-row-composite-okp row (fn-arena-seal-list xs fn-arena))
                 (fn-rows-handles-inp (list row) (fn-arena-seal-list xs fn-arena))))
   :hints (("Goal" :cases ((fn-held-p row) (fn-hstxa-p row))
            :in-theory (e/d (fn-rows-handles-inp fn-row-composite-okp)
                            (fn-held-p fn-hstxa-p fn-row-wire-of fn-row-handle-inp
                             fn-arena-seal-list-is-append))
            :use ((:instance fn-sca-row-wire-of-held-survives-seal (h row))
                  (:instance fn-sca-row-wire-of-held-survives-seal (h (fn-hstxa-held row)))
                  (:instance fn-sca-composite-held-is-held (x row))
                  (:instance fn-sca-composite-is-not-held (x row)))))))

(local (defthm fn-sca-composite-okp-survives-intern-events
   (implies (and (fn-rows-handles-inp (list row) fn-arena)
                 (fn-row-composite-okp row fn-arena))
            (and (fn-row-composite-okp row (mv-nth 1 (fn-intern-events ws keyring generation fn-arena)))
                 (fn-rows-handles-inp (list row)
                                      (mv-nth 1 (fn-intern-events ws keyring generation fn-arena)))))
   :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
            :in-theory (union-theories '(fn-intern-events fn-intern-event-arena
                                         fn-sca-composite-okp-survives-seal
                                         mv-nth car-cons cdr-cons
                                         (:executable-counterpart zp)
                                         (:induction fn-intern-events))
                                       (theory 'minimal-theory))))))

(defthm fn-sca-intern-events-composites-okp
  (implies (and (fn-arena-p fn-arena) (natp generation) (fn-wire-event-listp ws)
                (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad)))
           (fn-rows-composites-okp (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))
                                   (mv-nth 1 (fn-intern-events ws keyring generation fn-arena))))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events fn-rows-composites-okp fn-wire-event-listp)
                           (fn-intern-event fn-row-composite-okp fn-rows-handles-inp
                            fn-wire-event-p fn-arena-seal-list-is-append fn-record-p
                            fn-stxa-p fn-replay-composite-record fn-cat-intern-list
                            fn-intern-event-arena)))
          ("Subgoal *1/4"
           :use ((:instance fn-intern-event-composite-okp (w (car ws)))
                 (:instance fn-intern-event-handle-in (w (car ws)))
                 (:instance fn-intern-events-arena-p (ws (list (car ws))))
                 (:instance fn-sca-composite-okp-survives-intern-events
                            (row (mv-nth 0 (fn-intern-event (car ws) keyring generation fn-arena)))
                            (ws (cdr ws))
                            (fn-arena (mv-nth 1 (fn-intern-event (car ws) keyring generation fn-arena))))))))

; KEYSTONE (E at the host's entries, over the flipped store).  The owner
; host/owner-host.lisp fn-owner-install-extended installs from the capture of
; any prefix of ROWS extended over any suffix (fn-owner-recover-rows: prefix
; nil; fn-owner-recover-from-checkpoint, -from-store-open: the verified
; checkpoint's rows), when it is not :fault, holds exactly those rows at an
; idle store, and the catalog the host then loads from them
; (fn-sca-load-held-rows, under any view index) is in R with it -- R over
; the rows' ARTICLES through the arena the rows' handles index
; (fn-cat-history-articles: plain and signed).  The two row hypotheses (the
; handles are in the arena; each row is what the intern makes of one,
; fn-rows-composites-okp) are what the open's intern establishes (full open
; below) and what a checkpoint load must establish of its rows; that the
; rows are store events follows from the install
; (fn-sca-ocl-store-rows-are-values).  The
; host extends with fn-rii-sco-extend, which is fn-sco-extend
; (books/replay-identity-index.lisp fn-rii-sco-extend-is-sco-extend).
(defthm fn-sca-ocl-relation-at-recover
  (let* ((oc (fn-ock-recover-extended
              (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
              configs frontier max-conns))
         (rows (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
    (implies (and (not (equal oc :fault))
                  (fn-arena-p fn-arena)
                  (fn-rows-handles-inp (append prefix suffix) fn-arena)
                  (fn-rows-composites-okp (append prefix suffix) fn-arena))
             (and (equal rows (append prefix suffix))
                  (fn-own-store-idlep (fn-own-store (fn-ocfg-owner oc)))
                  (fn-cat-ocl-relation oc fn-arena
                                       (fn-sca-load-held-rows rows view-index fn-arena fn-cat)))))
  :hints (("Goal" :use (fn-ock-recover-installs-ocl-relation
                        fn-owner-recover-from-checkpoint-equals-full-recover
                        (:instance fn-cbo-recover-full-store (events (append prefix suffix)))
                        (:instance fn-cbo-open-ok-records-and-phase (events (append prefix suffix)))
                        (:instance fn-sca-ocl-store-rows-are-values
                                   (oc (fn-ock-recover-extended
                                        (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
                                        configs frontier max-conns)))
                        (:instance fn-sca-load-held-rows-establishes-relation
                                   (rows (append prefix suffix))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-cat-ocl-relation)))))

; The open's intern: an event list the intern accepts is a list of wire
; events (fn-intern-event refuses every other value).
(local (defthm fn-sca-intern-event-accepts-wire-event
   (implies (not (equal (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad))
            (fn-wire-event-p w))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories '(fn-intern-event fn-wire-event-p
                                                mv-nth car-cons cdr-cons
                                                (:executable-counterpart zp)
                                                (:executable-counterpart equal))
                                              (theory 'minimal-theory))))))

(defthm fn-sca-intern-events-accepts-wire-events
  (implies (and (true-listp ws)
                (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad)))
           (fn-wire-event-listp ws))
  :rule-classes nil
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (union-theories '(fn-intern-events fn-wire-event-listp true-listp
                                        mv-nth car-cons cdr-cons (:executable-counterpart zp)
                                        (:executable-counterpart equal)
                                        (:executable-counterpart fn-wire-event-listp)
                                        (:induction fn-intern-events))
                                      (theory 'minimal-theory)))
          ("Subgoal *1/4" :use ((:instance fn-sca-intern-event-accepts-wire-event (w (car ws)))))
          ("Subgoal *1/3" :use ((:instance fn-sca-intern-event-accepts-wire-event (w (car ws)))))
          ("Subgoal *1/2" :use ((:instance fn-sca-intern-event-accepts-wire-event (w (car ws)))))))

; KEYSTONE (E2 and E1, the full open).  The rows the open interns from the
; decoded journal WS into the cleared arena (books/store-intern.lisp
; fn-intern-events under the open's keyring nil and generation 0; the native
; chunked intern is the same step, books/store-recover-stream.lisp
; fn-srs-one-step-is-the-intern-of-the-decode): the installed store's
; history is WS through that arena, and the catalog the host loads is in R.
; The hypotheses are the host's own checks (:bad, :fault) and WS a true list.
(local (defthm fn-sca-arena-p-of-clear
   (fn-arena-p (fn-arena-clear fn-arena))
   :hints (("Goal" :in-theory (enable fn-arena-clear)))))

(defthm fn-sca-ocl-relation-at-full-open
  (let* ((arena0 (fn-arena-clear fn-arena))
         (rows (mv-nth 0 (fn-intern-events ws nil 0 arena0)))
         (arena (mv-nth 1 (fn-intern-events ws nil 0 arena0)))
         (oc (fn-ock-recover-extended
              (fn-sco-extend (fn-sco-capture configs nil) configs rows)
              configs frontier max-conns)))
    (implies (and (true-listp ws)
                  (not (equal rows :bad))
                  (not (equal oc :fault)))
             (and (equal (fn-rows-wire-of (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                                          arena)
                         ws)
                  (fn-cat-ocl-relation
                   oc arena
                   (fn-sca-load-held-rows (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                                          view-index arena fn-cat)))))
  :hints (("Goal" :use ((:instance fn-sca-ocl-relation-at-recover
                                   (prefix nil)
                                   (suffix (mv-nth 0 (fn-intern-events ws nil 0 (fn-arena-clear fn-arena))))
                                   (fn-arena (mv-nth 1 (fn-intern-events ws nil 0 (fn-arena-clear fn-arena)))))
                        (:instance fn-sca-intern-events-accepts-wire-events
                                   (keyring nil) (generation 0) (fn-arena (fn-arena-clear fn-arena)))
                        (:instance fn-intern-events-arena-p
                                   (keyring nil) (generation 0) (fn-arena (fn-arena-clear fn-arena)))
                        (:instance fn-intern-events-handles-in
                                   (keyring nil) (generation 0) (fn-arena (fn-arena-clear fn-arena)))
                        (:instance fn-intern-events-materializes
                                   (keyring nil) (generation 0) (fn-arena (fn-arena-clear fn-arena)))
                        (:instance fn-sca-intern-events-composites-okp
                                   (keyring nil) (generation 0) (fn-arena (fn-arena-clear fn-arena)))
                        (:instance fn-intern-events-are-store-events
                                   (keyring nil) (generation 0) (fn-arena (fn-arena-clear fn-arena))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(binary-append fn-sca-arena-p-of-clear
                                        (:executable-counterpart natp)
                                        (:executable-counterpart consp))))))

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


; KEYSTONE (T2 at the host's finish, over the flipped store).
; host/owner-host.lisp fn-owner-finish-submission installs the finished owner
; (fn-apc-own-finish, which is fn-ccar-own-finish under the carried parse
; and the store's event index: books/owner-parse-carried.lisp
; fn-apc-own-finish-is-own-finish) and then runs fn-sca-finish with the token
; it reads off the store's completion, (sequence-or-txid of the completion .
; the pending's expected).  Before the finish the store is at :completing,
; the ARTICLES of its rows through the arena are the catalog's history
; RECORDS0 followed by the completing record W, and the pending holds the
; store's own row for W (fn-cat-prepare-sealed: its handle is in the arena
; and it materializes to W).  After, R holds as the equality at the idle
; store, with the owner's live relation.
(defthm fn-sca-ocl-relation-of-finish
  (let* ((s (fn-own-store (fn-ocfg-owner oc)))
         (token (cons (nfix (cdr (fn-sf-completion (fn-sn-files s)))) (fn-pc-expected pending)))
         (w (fn-held-wire-of (fn-pc-held pending) fn-arena)))
    (implies (and (fn-ocl-relation oc)
                  (fn-cat-history-relation records0 fn-arena fn-cat)
                  (fn-sn-completion-enabledp s)
                  (equal (fn-sf-article-records (fn-cat-history-articles (fn-sf-records (fn-sn-files s)) fn-arena))
                         (append (fn-sf-article-records records0) (list w)))
                  (fn-pc-p pending)
                  (equal token (fn-pc-token pending))
                  (equal (fn-pc-expected pending) (fn-cat-count fn-cat))
                  (< (fn-record-payload (fn-pc-held pending)) (fn-arena-count fn-arena))
                  (fn-record-p w))
             (fn-cat-ocl-relation
              (fn-ocfg-with-owner oc (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena)))
              fn-arena
              (mv-nth 2 (fn-sca-finish token pending view-index targets fn-cat)))))
  :hints (("Goal" :use ((:instance fn-cat-ocl-relation-of-article-finish-by
                                   (w (fn-held-wire-of (fn-pc-held pending) fn-arena))
                                   (fn-cat2 (mv-nth 2 (fn-sca-finish
                                                       (cons (nfix (cdr (fn-sf-completion
                                                                         (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
                                                             (fn-pc-expected pending))
                                                       pending view-index targets fn-cat))))
                        (:instance fn-sca-finish-keeps-the-relation
                                   (records records0)
                                   (token (cons (nfix (cdr (fn-sf-completion
                                                            (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
                                                (fn-pc-expected pending)))
                                   (w (fn-held-wire-of (fn-pc-held pending) fn-arena))))
           :in-theory (theory 'minimal-theory))))

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
; The join: the view a pin names holds the pinned archive's articles.
; Stated over the owner's current view: its version and archive.  Carried as
; fn-scj-joinp and preserved by the finishes in books/served-catalog-join.lisp;
; until its establishment at the opens lands it is the hypothesis the served
; chain carries (fn-scr-catalogp).

(defun-nx fn-sca-join (o fn-arena fn-cat)
  (equal (fn-state-articles (fn-own-view-archive (fn-own-view o)))
         (fn-cat-view-articles (fn-scr-view-of (fn-own-view-version (fn-own-view o)) fn-cat)
                               fn-arena fn-cat)))

; -----------------------------------------------------------------------------
; The overview column at the owner's catalog entries (lane served-columns,
; PRF-332): F (books/served-columns.lisp fn-scol-okp, a conjunct of
; fn-scr-catalogp) at E, T1, T2 and T4.  E commits the store's rows as they
; are, so it establishes F exactly when those rows are faithful to the arena
; (fn-scol-history-okp: every article row, and every composite's held row,
; carries the facts of its handle's octets or no column); T1's row is the
; store's intern at the sealed handle (fn-intern-row-at: faithful when the
; handle denotes the record's payload, which the one seal of the POST's
; buffer makes true: fn-cat-prepare-sealed-names-the-sealed-handle); T2
; commits that row; T4 only withdraws.  That the store's history rows stay
; faithful across the owner's steps and the opens is the same obligation as
; the join's establishment (books/served-catalog-join.lisp), still OPEN.

(local (defthm fn-scol-okp-of-load-held-row
   (implies (and (fn-scol-okp fn-arena fn-cat)
                 (or (not (fn-cat-rowp r)) (fn-scol-row-okp r fn-arena))
                 (or (not (fn-sca-composite-shapep r))
                     (fn-scol-row-okp (fn-hstxa-held r) fn-arena)))
            (fn-scol-okp fn-arena (fn-sca-load-held-row r view-index fn-cat)))
   :hints (("Goal" :in-theory (e/d (fn-sca-load-held-row)
                                   (fn-sca-composite-shapep fn-cat-rowp fn-held-with-withdrawn
                                    fn-cat-commit-is-append fn-midx-lookup fn-scol-okp))))))

(defthm fn-scol-okp-of-load-held-rows-from
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-scol-history-okp rows fn-arena))
           (fn-scol-okp fn-arena (fn-sca-load-held-rows-from rows view-index fn-cat)))
  :hints (("Goal" :induct (fn-sca-load-held-rows-from rows view-index fn-cat)
           :in-theory (e/d (fn-sca-load-held-rows-from)
                           (fn-sca-load-held-row fn-sca-composite-shapep fn-cat-rowp)))))

; E.
(defthm fn-scol-okp-of-load-held-rows
  (implies (and (fn-arena-p fn-arena)
                (fn-scol-history-okp rows fn-arena))
           (fn-scol-okp fn-arena (fn-sca-load-held-rows rows view-index fn-arena fn-cat)))
  :hints (("Goal" :use ((:instance fn-sca-load-held-rows-establishes-byte-facts))
           :in-theory (disable fn-scol-okp fn-scol-history-okp
                               fn-sca-load-held-rows
                               fn-sca-load-held-rows-establishes-byte-facts))))

; T1: the store's intern at a handle denoting the record's payload.
(defthm fn-scol-row-okp-of-intern-row-at
  (implies (equal (fn-nntp-payload-bytes h fn-arena) (fn-record-payload w))
           (fn-scol-row-okp (fn-intern-row-at w keyring generation h) fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-scol-row-okp fn-intern-row-at)
                                  (fn-held-facts-of fn-held-context-of)))))

; T2.
(defthm fn-scol-okp-of-sca-complete
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-scol-row-okp (fn-pc-held pending) fn-arena))
           (fn-scol-okp fn-arena (mv-nth 2 (fn-sca-complete token pending view-index fn-cat))))
  :hints (("Goal" :in-theory (e/d (fn-sca-complete fn-cat-complete fn-cat-complete-hidden)
                                  (fn-held-with-withdrawn fn-cat-commit-is-append
                                   fn-midx-lookup fn-scol-okp)))))

; T4.
(defthm fn-scol-okp-of-sca-withdraw-targets
  (implies (and (fn-scol-okp fn-arena fn-cat) (natp by))
           (fn-scol-okp fn-arena (fn-sca-withdraw-targets targets view-index by fn-cat)))
  :hints (("Goal" :induct (fn-sca-withdraw-targets targets view-index by fn-cat)
           :in-theory (e/d (fn-sca-withdraw-targets)
                           (fn-cat-view-last-visible fn-cat-withdraw-is-mark fn-midx-lookup
                            fn-scol-okp)))))

; The host's finish (T4 then T2).
(defthm fn-scol-okp-of-sca-finish
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-scol-row-okp (fn-pc-held pending) fn-arena)
                (or (null pending) (natp (fn-pc-expected pending))))
           (fn-scol-okp fn-arena (mv-nth 2 (fn-sca-finish token pending view-index targets fn-cat))))
  :hints (("Goal" :in-theory (e/d (fn-sca-finish) (fn-sca-complete fn-sca-withdraw-targets)))))
