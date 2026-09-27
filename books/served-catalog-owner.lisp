; served-catalog-owner.lisp -- the catalog at the owner's entries (step 8 of
; the catalog slice, the R side; planning/evidence/catalog-slice-2026-09-26.md).
;
; The host maintains the catalog at three entries, each an ACL2 decision the
; host only plumbs (host/owner-host.lisp):
;   E  fn-sca-load-held-rows    at recovery (fn-owner-install-extended): the
;                               catalog of the installed store's ROWS, from
;                               empty, reading no byte and sealing nothing
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
; hypothesis fn-scr-catalogp carries -- is stated here as fn-sca-join and is
; an OPEN proof target (the boundary owner's R3): its teeth are in the test
; book; what continues without it is the served path under the hypothesis.

(in-package "ACL2")

(include-book "served-catalog-chain")
(include-book "catalog-entries")
(include-book "catalog-refresh")
(include-book "store-intern")

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

; E over the rows.  The guard's domain: every row of the catalog's shape is
; a held record (the store's history is store events: fn-sf-record-valuesp,
; which implies it: fn-sca-held-rowsp-of-record-values).  The body dispatches
; on the digest-free shape fn-cat-rowp and never executes fn-held-p.
(defun fn-sca-held-rowsp (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (or (not (fn-cat-rowp (car rows))) (fn-held-p (car rows)))
           (fn-sca-held-rowsp (cdr rows)))
    t))

; One row: an article row (by the digest-free shape) committed, visible when
; the view shows its Message-ID, else withdrawn at its own index as
; fn-cat-load-row-hidden commits it; any other event skipped.
(defun fn-sca-load-held-row (r view-index fn-cat)
  (declare (xargs :stobjs fn-cat
                  :guard (or (not (fn-cat-rowp r)) (fn-held-p r))
                  :guard-hints (("Goal" :in-theory (e/d (fn-held-withdrawnp) (fn-held-p))
                                 :use ((:instance fn-held-p-of-fn-held-with-withdrawn
                                                  (h r) (w (cons (fn-cat-count fn-cat) 0))))))))
  (if (fn-cat-rowp r)
      (if (fn-midx-lookup (fn-record-msgid r) view-index)
          (fn-cat-commit r fn-cat)
        (fn-cat-commit (fn-held-with-withdrawn r (cons (fn-cat-count fn-cat) 0)) fn-cat))
    fn-cat))

(defun fn-sca-load-held-rows-from (rows view-index fn-cat)
  (declare (xargs :stobjs fn-cat :guard (fn-sca-held-rowsp rows)))
  (if (consp rows)
      (let ((fn-cat (fn-sca-load-held-row (car rows) view-index fn-cat)))
        (fn-sca-load-held-rows-from (cdr rows) view-index fn-cat))
    fn-cat))

(defun fn-sca-load-held-rows (rows view-index fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-sca-held-rowsp rows))
           (ignorable fn-arena))
  (let ((fn-cat (fn-cat-clear fn-cat)))
    (fn-sca-load-held-rows-from rows view-index fn-cat)))

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

(defthm fn-sca-held-rowsp-of-record-values
  (implies (fn-sf-record-valuesp rows) (fn-sca-held-rowsp rows))
  :hints (("Goal" :induct (fn-sca-held-rowsp rows)
           :in-theory (e/d (fn-sf-record-valuesp) (fn-store-event-p fn-held-p fn-cat-rowp)))))

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

(local (defun fn-sca-held-ind (rows history view-index fn-arena fn-cat)
   (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil)
            (irrelevant history))
   (if (consp rows)
       (let ((fn-cat (fn-sca-load-held-row (car rows) view-index fn-cat)))
         (fn-sca-held-ind (cdr rows) (append history (list (fn-row-wire-of (car rows) fn-arena)))
                          view-index fn-arena fn-cat))
     fn-cat)))

(local (defthm fn-sca-handles-of-cons
   (implies (and (consp rows) (fn-rows-handles-inp rows fn-arena))
            (and (fn-rows-handles-inp (cdr rows) fn-arena)
                 (or (not (fn-held-p (car rows))) (fn-row-handle-inp (car rows) fn-arena))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-rows-handles-inp)
                                   (fn-held-p fn-hstxa-p fn-row-handle-inp))))))

; One row of E: an article row committed (visible, or withdrawn at its own
; index), any other store event skipped; the history grows by the row's wire.
(local (defthm fn-sca-load-step
   (implies (and (fn-cat-history-relation history fn-arena fn-cat)
                 (fn-store-event-p r)
                 (or (not (fn-held-p r)) (fn-row-handle-inp r fn-arena))
                 (fn-wire-event-p (fn-row-wire-of r fn-arena)))
            (fn-cat-history-relation
             (append history (list (fn-row-wire-of r fn-arena))) fn-arena
             (fn-sca-load-held-row r view-index fn-cat)))
   :hints (("Goal" :cases ((fn-held-p r))
            :in-theory (union-theories '(fn-sca-relation-of-non-article fn-sca-load-held-row)
                                       (theory 'minimal-theory))
            :use ((:instance fn-sca-store-event-rowp-is-held (x r))
                  (:instance fn-sca-other-event-wire-not-record (x r))
                  (:instance fn-held-p-implies-cat-rowp (x r))
                  (:instance fn-sca-held-wire-event-is-record (h r))
                  (:instance fn-sca-commit-row-keeps-relation (records history) (row r)))))))

(defthm fn-sca-load-held-rows-from-keeps-relation
  (implies (and (fn-cat-history-relation history fn-arena fn-cat)
                (fn-sf-record-valuesp rows)
                (fn-rows-handles-inp rows fn-arena)
                (fn-wire-event-listp (fn-rows-wire-of rows fn-arena)))
           (fn-cat-history-relation (append history (fn-rows-wire-of rows fn-arena)) fn-arena
                                    (fn-sca-load-held-rows-from rows view-index fn-cat)))
  :hints (("Goal" :induct (fn-sca-held-ind rows history view-index fn-arena fn-cat)
           :expand ((fn-sca-load-held-rows-from rows view-index fn-cat)
                    (fn-rows-wire-of rows fn-arena)
                    (fn-sf-record-valuesp rows))
           :in-theory (union-theories '(fn-sca-append-assoc fn-sca-relation-of-append-atom
                                        fn-wire-event-listp car-cons cdr-cons binary-append
                                        (:induction fn-sca-held-ind))
                                      (theory 'minimal-theory)))
          ("Subgoal *1/2" :expand ((fn-rows-wire-of rows fn-arena)
                                   (fn-sca-load-held-rows-from rows view-index fn-cat)))
          ("Subgoal *1/1" :use ((:instance fn-sca-handles-of-cons)
                                (:instance fn-sca-load-step (r (car rows)))))))

; KEYSTONE (E after the flip): committing the store's rows from the cleared
; catalog establishes R over the rows' wire events (store-intern's ALPHA),
; under the invariants the open establishes of the rows: they are store
; events (fn-intern-events-are-store-events), their handles are in the arena
; (fn-intern-events-handles-in), and they materialize to wire events
; (fn-intern-events-materializes).  No byte is read and no payload sealed.
(defthm fn-sca-load-held-rows-establishes-relation
  (implies (and (fn-arena-p fn-arena)
                (fn-sf-record-valuesp rows)
                (fn-rows-handles-inp rows fn-arena)
                (fn-wire-event-listp (fn-rows-wire-of rows fn-arena)))
           (fn-cat-history-relation (fn-rows-wire-of rows fn-arena) fn-arena
                                    (fn-sca-load-held-rows rows view-index fn-arena fn-cat)))
  :hints (("Goal" :use ((:instance fn-sca-load-held-rows-from-keeps-relation
                                   (history nil) (fn-cat nil)))
           :in-theory (e/d (fn-sca-load-held-rows fn-cat-history-relation)
                           (fn-sca-load-held-rows-from-keeps-relation fn-sca-load-held-rows-from
                            fn-rows-wire-of fn-sf-record-valuesp fn-rows-handles-inp
                            fn-wire-event-listp)))))


; The installed store's rows are store events: the owner's live relation
; carries the store's structural state (books/owner-commit-carried.lisp
; fn-ccar-ocl-relation-carries-sn-statep), whose record list is one.
(defthm fn-sca-ocl-store-rows-are-values
  (implies (fn-ocl-relation oc)
           (fn-sf-record-valuesp (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
  :hints (("Goal" :use ((:instance fn-ccar-ocl-relation-carries-sn-statep))
           :in-theory (e/d (fn-sn-statep fn-sf-statep)
                           (fn-ocl-relation fn-sf-phase-shapep fn-sf-success-listp fn-node-statep)))))

; KEYSTONE (E at the host's entries, over the flipped store).  The owner
; host/owner-host.lisp fn-owner-install-extended installs from the capture of
; any prefix of ROWS extended over any suffix (fn-owner-recover-rows: prefix
; nil; fn-owner-recover-from-checkpoint, -from-store-open: the verified
; checkpoint's rows), when it is not :fault, holds exactly those rows at an
; idle store, and the catalog the host then loads from them
; (fn-sca-load-held-rows, under any view index) is in R with it -- R over
; ALPHA of the rows through the arena the rows' handles index.  The two row
; hypotheses are what the open's intern establishes (full open below) and
; what a checkpoint load must establish of its rows; that the rows are store
; events follows from the install (fn-sca-ocl-store-rows-are-values).  The
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
                  (fn-wire-event-listp (fn-rows-wire-of (append prefix suffix) fn-arena)))
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
                  (equal (fn-sf-article-records (fn-rows-wire-of (fn-sf-records (fn-sn-files s)) fn-arena))
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
; The join (OPEN): the view a pin names holds the pinned archive's articles.
; Stated over the owner's current view: its version and archive.  Proving it
; is the R-side completion of step 8; until then it is the hypothesis the
; served chain carries (fn-scr-catalogp), with teeth in the test book.

(defun-nx fn-sca-join (o fn-arena fn-cat)
  (equal (fn-state-articles (fn-own-view-archive (fn-own-view o)))
         (fn-cat-view-articles (fn-scr-view-of (fn-own-view-version (fn-own-view o)) fn-cat)
                               fn-arena fn-cat)))
