; fn: the entry-and-transition map of R at the host's entries (wave 5, lane
; catalog-boundary-owner, 2026-09-26; gpt-6's wave-5 review section 5 and
; consolidation review section 9; D33; the consolidation design 1.5).
;
; R is books/catalog-relation.lisp's fn-cat-history-relation: the catalog's
; rows, materialized by handle from the arena, are the ARTICLE records of a
; history, in order.  That book establishes it from the creators and by the
; load fold over any record list, and preserves it by withdraw, redecide and
; the completion.  This book says WHICH history: the one the owner the host
; installs replays, at every entry the host has, and it says when the
; equality holds and when only a prefix does.
;
; TWO FINDINGS this map rests on (both theorems of the store books):
;
;  1. The finish does not append to the history.  `fn-snt-finish-keeps-records'
;     (books/store-node-traces.lisp): the record enters `fn-sf-records' at the
;     durable write (the K0 program, through fn-own-store-step's `fn-snrt-step'
;     arms, whose records only grow: `fn-own-snrt-step-records-prefix'); the
;     finish (`fn-sn-finish', reached by host/owner-host.lisp
;     fn-owner-finish-submission through `fn-ccar-own-finish') installs the
;     article into the acceptance and returns the store to :ready.  So
;     between the write and the finish the history LEADS the catalog by the
;     pending row, and R holds as a PREFIX (fn-cat-history-prefix-relation);
;     at every idle phase (`fn-own-store-idlep', where the owner refreshes
;     its view) R holds as the EQUALITY.  fn-cat-ocl-relation states both.
;
;  2. The owner the host installs satisfies `fn-ocl-relation'
;     (books/config-owner-live.lisp: the configuration-aware relation, with
;     `fn-cst-relation' on the store), and the store-only `fn-snt-relation'
;     does not transfer to it (books/store-open-bridge.lisp, the note above
;     fn-cpo-open-observed-success-has-history-relation).  So the relation
;     the host needs conjoins fn-ocl-relation, not fn-own-relation:
;     catalog-relation's fn-cat-owner-relation is the model-level form; the
;     host-level form is fn-cat-ocl-relation below.
;
; THE ENTRIES (each theorem names the host function that reaches it; the
; line is found by tools/current_view.py, never written here):
;
;   Every entry installs the owner from the store's ROWS (the open interns
;   the decoded journal: books/store-intern.lisp fn-intern-events) and loads
;   the catalog from those rows (host/owner-host.lisp fn-owner-install-
;   extended -> books/served-catalog-owner.lisp fn-sca-load-held-rows, which
;   reads no byte and seals nothing).
;   E1 init.  host/native/io.lisp fnn-command-init writes an empty store; the
;      first open is E2 with no records (fn-sca-ocl-relation-at-full-open
;      with ws = nil: the catalog cleared).
;   E2 full replay.  fn-owner-recover-from-store-open (the native owner) and
;      fn-owner-recover-rows (the bridge): fn-ock-recover-extended over
;      (fn-rii-sco-extend (fn-sco-capture configs nil) configs rows),
;      fn-rii-sco-extend-is-sco-extend.  KEYSTONE
;      fn-sca-ocl-relation-at-full-open: over the rows the open interned from
;      the decoded journal WS into the cleared arena, the installed store's
;      history is WS through that arena and the catalog the host loads is in
;      R with the installed owner; no hypothesis beyond the host's :bad and
;      :fault checks (and WS a true list, as every decoder answers).
;   E3 checkpoint.  fn-owner-recover-from-checkpoint and
;      fn-owner-recover-from-store-open (fnn-recover-from-state-checkpoint):
;      the verified checkpoint is the capture of a prefix of rows, extended
;      over the suffix rows interned on top of the loaded arena.  KEYSTONE
;      fn-sca-ocl-relation-at-recover: for ANY prefix and suffix whose rows
;      are store events with their handles in the arena and materialize to
;      wire events (what the intern establishes, fn-intern-events-are-store-
;      events / -handles-in / -materializes, and what the checkpoint load
;      must establish of its rows), the catalog the host loads is in R.
;   E4 import.  host/native/io.lisp fnn-command-store-import writes the plan's
;      files as init writes them and runs the ORDINARY open (fnn-recover): E2
;      over the imported records (books/store-export.lisp,
;      fn-sxp-import-of-export-replays-the-same-history).  No new entry.
;   E5 recovery after a cut.  fnn-recover after a process death is E2 or E3
;      over the crash image (the model event fn-own-reopen); the catalog is
;      rebuilt by the same fold: every process-death cut re-enters here.
;
; THE TRANSITIONS (R preserved), at the host's call granularity:
;
;   T1 the durable write.  fn-owner-step / fn-owner-io / fn-owner-prepare*
;      (fn-own-store-step: fn-snrt-step): the history grows by a prefix
;      (fn-own-snrt-step-records-prefix); fn-cat-prefix-relation-of-growth:
;      the prefix form is kept, the catalog untouched.  A refused reservation
;      and a known abort (fn-sn-refuse-reservation, fn-sn-known-abort) are
;      arms of the same step: covered.  fn-cat-abandon touches no row.
;   T2 the completion of an article.  fn-owner-finish-submission
;      (fn-ccar-own-finish = fn-own-finish, keystone fn-ccar-own-finish-is-own-
;      finish): fn-cat-ocl-relation-of-article-finish: with the catalog equal
;      to the committed prefix and the completing record W the newest
;      article, fn-cat-complete of the pending PreparedCommit whose held row
;      materializes to W restores the EQUALITY at the idle store the finish
;      leaves (fn-snt-finish-image: :ready).  fn-ocl-relation is kept by
;      fn-ocmt-post-commit-preserves-ocl-relation (books/owner-commit-ocl.lisp).
;   T3 the completion of a non-article event (retention, identity: a `keys
;      redecide' kind-3 change, consumer, topic): fn-cat-ocl-relation-of-
;      other-finish: the catalog is untouched and the equality holds after,
;      because fn-sf-article-records skips the event (fn-cat-relation-of-non-
;      article-append).
;   T4 withdrawal.  fn-cat-withdraw (the cancel's effect on its target):
;      fn-cat-ocl-relation-of-withdraw, in both forms; the cancel's own row is
;      T2.  ORDER (gpt-6's publication-order case): the host must call
;      fn-cat-withdraw BEFORE fn-cat-complete of the cancel row, so the
;      withdrawal's version is the count before the cancel and the version
;      that first sees the cancel does not see its target (the refresh's
;      fn-ctl-visible-add drops the target when the cancel is added:
;      books/catalog-refresh.lisp).
;   T5 redecision.  fn-cat-redecide (keys redecide, PRF-166; the kind-3 record
;      is T1 then T3): fn-cat-ocl-relation-of-redecide, in both forms.
;   T6 reads preserve R trivially (no export mutates).  The served connection
;      invariant fn-served-connp (books/served.lisp) is the SAME discipline
;      one level up (PKT-615, lane transit-pipelining's two submission
;      theorems assume it): established at connection open and at every
;      entry above (connections are nil after a recovery: fn-own-start,
;      fn-own-reopen), preserved by every served step; its discharge is
;      catalog-slice-5's, which owns the served arms.
;
; What is NOT here: the joined owner's second payload field and the served
; bytes (PRF-204), the held-record reads of the arms (step 7b), the host
; calling fn-cat-load at these entries (step 8, PKT-585).  The theorems are
; over the functions those steps will call, at the entries the host has.

(in-package "ACL2")
(include-book "catalog-relation")
(include-book "owner-checkpoint-open")
(include-book "owner-commit-ocl")

; -----------------------------------------------------------------------------
; The load fold over an appended history (E3: the checkpoint's rows, then the
; suffix), and over the empty one (E1).

(defthm fn-cat-load-of-nil
  (equal (fn-cat-load nil keyring generation fn-arena fn-cat)
         (mv fn-arena fn-cat))
  :hints (("Goal" :in-theory (enable fn-cat-load))))

(defthm fn-cat-load-of-append
  (equal (fn-cat-load (append a b) keyring generation fn-arena fn-cat)
         (fn-cat-load b keyring generation
                      (mv-nth 0 (fn-cat-load a keyring generation fn-arena fn-cat))
                      (mv-nth 1 (fn-cat-load a keyring generation fn-arena fn-cat))))
  :hints (("Goal" :induct (fn-cat-load a keyring generation fn-arena fn-cat)
           :in-theory (e/d (fn-cat-load)
                           (fn-cat-load-row fn-cat-count-is-len fn-cat-at-is-nth
                            fn-cat-p-is-rowsp)))))

; -----------------------------------------------------------------------------
; The article sub-history of a prefix is a prefix of the article sub-history;
; R depends on a history only through its article sub-history.

(defthm fn-sf-article-records-of-prefix
  (implies (fn-sf-prefixp xs ys)
           (fn-sf-prefixp (fn-sf-article-records xs) (fn-sf-article-records ys)))
  :hints (("Goal" :induct (fn-sf-prefixp xs ys))))

(defthm fn-sf-article-records-true-listp
  (true-listp (fn-sf-article-records x)))

(defthm fn-cat-history-relation-reads-the-articles
  (implies (equal (fn-sf-article-records a) (fn-sf-article-records b))
           (equal (fn-cat-history-relation a fn-arena fn-cat)
                  (fn-cat-history-relation b fn-arena fn-cat)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cat-history-relation)
                                  (fn-cat-count-is-len fn-cat-at-is-nth fn-cat-p-is-rowsp
                                   fn-cat-handles-inp fn-cat-wire-list)))))

; An event that is not an article, appended to the history, changes what the
; catalog must materialize not at all (T3, T5).
(defthm fn-cat-relation-of-non-article-append
  (implies (not (fn-record-p r))
           (equal (fn-cat-history-relation (append history (list r)) fn-arena fn-cat)
                  (fn-cat-history-relation history fn-arena fn-cat)))
  :hints (("Goal" :use ((:instance fn-cat-history-relation-reads-the-articles
                                   (a (append history (list r))) (b history))))))

; -----------------------------------------------------------------------------
; The prefix form of R: between the durable write and the finish.

(defun fn-cat-history-prefix-relation (records fn-arena fn-cat)
  ; Proof vocabulary (fn-sf-prefixp is not guard-verified); never executed on
  ; a served path, like fn-cat-owner-relation.
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (and (fn-cat-p fn-cat)
       (fn-arena-p fn-arena)
       (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
       (fn-sf-prefixp (fn-cat-wire-list 0 fn-arena fn-cat)
                      (fn-sf-article-records records))))

(defthm fn-cat-relation-is-prefix-relation
  (implies (fn-cat-history-relation records fn-arena fn-cat)
           (fn-cat-history-prefix-relation records fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-cat-history-relation fn-cat-history-prefix-relation)
                                  (fn-cat-count-is-len fn-cat-at-is-nth fn-cat-p-is-rowsp
                                   fn-cat-handles-inp fn-cat-wire-list fn-sf-article-records))
           :use ((:instance fn-sf-prefixp-reflexive (xs (fn-sf-article-records records)))
                 (:instance fn-sf-article-records-true-listp (x records))))))

; T1: the history grows, the catalog stands, the prefix form is kept.
(defthm fn-cat-prefix-relation-of-growth
  (implies (and (fn-cat-history-prefix-relation records fn-arena fn-cat)
                (fn-sf-prefixp records more))
           (fn-cat-history-prefix-relation more fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-cat-history-prefix-relation)
                                  (fn-cat-count-is-len fn-cat-at-is-nth fn-cat-p-is-rowsp
                                   fn-cat-handles-inp fn-cat-wire-list))
           :use ((:instance fn-sf-prefixp-transitive
                            (xs (fn-cat-wire-list 0 fn-arena fn-cat))
                            (ys (fn-sf-article-records records))
                            (zs (fn-sf-article-records more)))))))

; -----------------------------------------------------------------------------
; The row updates keep the materialized rows (T4, T5), in the prefix form
; too.  (catalog-relation proves these for the equality form with local
; lemmas; the two wire-list facts are restated here, non-locally.)

(local (defthm fn-cbo-payload-of-with-withdrawn
   (equal (fn-record-payload (fn-held-with-withdrawn h w)) (fn-record-payload h))
   :hints (("Goal" :in-theory (enable fn-held-with-withdrawn fn-record-internals
                                      fn-held-internals)))))

(local (defthm fn-cbo-payload-of-with-context
   (equal (fn-record-payload (fn-held-with-context h ctx)) (fn-record-payload h))
   :hints (("Goal" :in-theory (enable fn-held-with-context fn-record-internals
                                      fn-held-internals)))))

(local (defthm fn-cbo-wire-of-with-withdrawn
   (equal (fn-held-wire (fn-held-with-withdrawn h w) payload) (fn-held-wire h payload))
   :hints (("Goal" :in-theory (enable fn-held-wire fn-held-with-withdrawn fn-record-internals
                                      fn-held-internals)))))

(local (defthm fn-cbo-wire-of-with-context
   (equal (fn-held-wire (fn-held-with-context h ctx) payload) (fn-held-wire h payload))
   :hints (("Goal" :in-theory (enable fn-held-wire fn-held-with-context fn-record-internals
                                      fn-held-internals)))))

(local (defthm fn-cbo-wire-of-at-withdraw
   (implies (and (natp target) (< target (fn-cat-count fn-cat)) (natp k))
            (equal (fn-held-wire-of (fn-cat-at k (fn-cat-withdraw target by fn-cat)) fn-arena)
                   (fn-held-wire-of (fn-cat-at k fn-cat) fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-cat-mark-withdrawn fn-held-wire-of)
                                   (fn-cat-p-is-rowsp))))))

(local (defthm fn-cbo-wire-of-at-redecide
   (implies (and (natp seq) (< seq (fn-cat-count fn-cat)) (natp k))
            (equal (fn-held-wire-of (fn-cat-at k (fn-cat-redecide seq ctx fn-cat)) fn-arena)
                   (fn-held-wire-of (fn-cat-at k fn-cat) fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-held-wire-of) (fn-cat-p-is-rowsp))))))

(local (defthm fn-cbo-count-of-withdraw
   (implies (and (natp target) (< target (fn-cat-count fn-cat)))
            (equal (fn-cat-count (fn-cat-withdraw target by fn-cat)) (fn-cat-count fn-cat)))
   :hints (("Goal" :in-theory (enable fn-cat-mark-withdrawn)))))

(defthm fn-cat-wire-list-of-withdraw
  (implies (and (natp target) (< target (fn-cat-count fn-cat)) (natp i))
           (equal (fn-cat-wire-list i fn-arena (fn-cat-withdraw target by fn-cat))
                  (fn-cat-wire-list i fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-cat-wire-list i fn-arena fn-cat)
           :in-theory (disable fn-cat-withdraw-is-mark fn-cat-count-is-len fn-cat-at-is-nth
                               fn-cat-p-is-rowsp fn-held-wire-of))))

(defthm fn-cat-wire-list-of-redecide
  (implies (and (natp seq) (< seq (fn-cat-count fn-cat)) (natp i))
           (equal (fn-cat-wire-list i fn-arena (fn-cat-redecide seq ctx fn-cat))
                  (fn-cat-wire-list i fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-cat-wire-list i fn-arena fn-cat)
           :in-theory (disable fn-cat-redecide-is-update-nth fn-cat-count-is-len fn-cat-at-is-nth
                               fn-cat-p-is-rowsp fn-held-wire-of))))

(local (defthm fn-cbo-handles-of-withdraw
   (implies (and (natp target) (< target (fn-cat-count fn-cat)))
            (equal (fn-cat-handles-inp n fn-arena (fn-cat-withdraw target by fn-cat))
                   (fn-cat-handles-inp n fn-arena fn-cat)))
   :hints (("Goal" :in-theory (e/d (fn-cat-mark-withdrawn) (fn-cat-p-is-rowsp))))))

(local (defthm fn-cbo-cat-p-of-withdraw
   (implies (and (fn-cat-p fn-cat) (natp target) (< target (fn-cat-count fn-cat)) (natp by))
            (fn-cat-p (fn-cat-withdraw target by fn-cat)))
   :hints (("Goal" :use ((:instance fn-cat-withdraw{preserved}))
            :in-theory (e/d (fn-cat-p fn-cat-withdraw fn-cat-count)
                            (fn-cat-p-is-rowsp fn-cat-withdraw-is-mark fn-cat-count-is-len))))))

(local (defthm fn-cbo-cat-p-of-redecide
   (implies (and (fn-cat-p fn-cat) (natp seq) (< seq (fn-cat-count fn-cat)) (fn-hc-p ctx))
            (fn-cat-p (fn-cat-redecide seq ctx fn-cat)))
   :hints (("Goal" :use ((:instance fn-cat-redecide{preserved} (context ctx)))
            :in-theory (e/d (fn-cat-p fn-cat-redecide fn-cat-count)
                            (fn-cat-p-is-rowsp fn-cat-redecide-is-update-nth
                             fn-cat-count-is-len))))))

(defthm fn-cat-prefix-relation-of-withdraw
  (implies (and (fn-cat-history-prefix-relation records fn-arena fn-cat)
                (natp target) (< target (fn-cat-count fn-cat)) (natp by))
           (fn-cat-history-prefix-relation records fn-arena (fn-cat-withdraw target by fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-cat-history-prefix-relation)
                                  (fn-cat-withdraw-is-mark fn-cat-count-is-len fn-cat-at-is-nth
                                   fn-cat-p-is-rowsp fn-cat-handles-inp fn-cat-wire-list)))))

(defthm fn-cat-prefix-relation-of-redecide
  (implies (and (fn-cat-history-prefix-relation records fn-arena fn-cat)
                (natp seq) (< seq (fn-cat-count fn-cat)) (fn-hc-p ctx))
           (fn-cat-history-prefix-relation records fn-arena (fn-cat-redecide seq ctx fn-cat)))
  :hints (("Goal" :in-theory (e/d (fn-cat-history-prefix-relation)
                                  (fn-cat-redecide-is-update-nth fn-cat-count-is-len fn-cat-at-is-nth
                                   fn-cat-p-is-rowsp fn-cat-handles-inp fn-cat-wire-list)))))

; -----------------------------------------------------------------------------
; R against the configured owner the host holds (fn-owner-core /
; fn-owner-ocfg, host/owner-host.lisp): the equality at idle phases, the
; prefix otherwise, and the owner's own live relation.  The history is the
; ARTICLES of the store's ROWS read through the arena (fn-cat-history-articles
; below): after the records flip `fn-sf-records' holds interned rows whose
; article payload is a HANDLE, and no held row is fn-record-p, so R over the
; raw rows would read no article at all (the vacuity catalog-columns
; removed, 2026-09-27); and a signed article is a composite row whose held
; row carries it, which ALPHA by wire (fn-rows-wire-of) reads as the wire
; composite, no article (signed-post's red).

; ALPHA for the catalog: each row of the store's history read as the ARTICLE
; it serves, through the arena.  A held row (a plain article) and the held
; row inside a composite row (a signed article: the atomic acceptance whose
; article the intern made a held row, books/store-intern.lisp
; fn-intern-event) are both read by their handle (fn-row-wire-of of the held
; row); any other row is its wire event, which is no article.  (For a
; composite, fn-rows-wire-of reads the wire composite, which
; fn-sf-article-records skips: a relation over it had no signed articles --
; the red signed-post found, catalog-columns 2026-09-27.)
(defun fn-cat-history-article (row fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (fn-hstxa-p row)
      (fn-row-wire-of (fn-hstxa-held row) fn-arena)
    (fn-row-wire-of row fn-arena)))

(defun fn-cat-history-articles (rows fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (atom rows)
      nil
    (cons (fn-cat-history-article (car rows) fn-arena)
          (fn-cat-history-articles (cdr rows) fn-arena))))

(defun-nx fn-cat-ocl-relation (oc fn-arena fn-cat)
  (let* ((s (fn-own-store (fn-ocfg-owner oc)))
         (history (fn-cat-history-articles (fn-sf-records (fn-sn-files s)) fn-arena)))
    (and (fn-ocl-relation oc)
         (if (fn-own-store-idlep s)
             (fn-cat-history-relation history fn-arena fn-cat)
           (fn-cat-history-prefix-relation history fn-arena fn-cat)))))

; -----------------------------------------------------------------------------
; E1, E2, E3 (and E4, E5 through them): the owner fn-owner-recover-extended
; installs, on either path.  The keystones over the catalog the host loads
; there (fn-sca-load-held-rows over the store's rows) are in
; books/served-catalog-owner.lisp: fn-sca-ocl-relation-at-recover,
; fn-sca-ocl-relation-at-full-open.  These two facts about the installed
; store are what they read.

; The store of the owner the full open installs is the opened Store, and the
; open was :ok.
(defthm fn-cbo-recover-full-store
  (implies (not (equal (fn-ock-recover-full configs frontier events max-conns) :fault))
           (and (equal (fn-own-store
                        (fn-ocfg-owner (fn-ock-recover-full configs frontier events max-conns)))
                       (fn-sn-open-state (fn-cpo-open-observed configs frontier events)))
                (equal (fn-sn-open-kind (fn-cpo-open-observed configs frontier events)) :ok)))
  :hints (("Goal" :in-theory (union-theories
                              (theory 'minimal-theory)
                              '(fn-ock-recover-full fn-ock-install fn-ocfg-owner-of-fn-ocfg-make
                                fn-own-configure fn-own-start fn-own-store-of-fn-own-make
                                fn-own-refresh-keeps-fields)))))

; The opened Store's records are the events and its phase is idle.
(defthm fn-cbo-open-ok-records-and-phase
  (implies (equal (fn-sn-open-kind (fn-cpo-open-observed configs frontier events)) :ok)
           (and (equal (fn-sf-records
                        (fn-sn-files (fn-sn-open-state (fn-cpo-open-observed configs frontier events))))
                       events)
                (fn-own-store-idlep
                 (fn-sn-open-state (fn-cpo-open-observed configs frontier events)))))
  :hints (("Goal" :use (fn-orec-open-kind-ok-is-okp fn-cpo-open-success-exact-image)
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-own-store-idlep fn-snt-idle-phasep
                                        (:executable-counterpart member-equal))))))

; -----------------------------------------------------------------------------
; T2: the article completion at the host's finish.  The host installs
; (fn-ocfg-with-owner oc (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena))),
; and fn-ccar-own-finish is fn-own-finish, whose owner is fn-own-complete.

(local
 (defthm fn-cbo-finish-owner-is-complete
   (equal (cdr (fn-ccar-own-finish o cfg fn-arena)) (fn-own-complete o))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                              '(fn-ccar-own-finish-is-own-finish fn-own-finish
                                                cdr-cons))))))

(local
 (defthm fn-cbo-complete-store
   (implies (fn-sn-completion-enabledp (fn-own-store o))
            (equal (fn-own-store (fn-own-complete o)) (fn-sn-finish (fn-own-store o))))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                              '(fn-own-complete fn-own-refresh-keeps-fields
                                                fn-own-store-of-fn-own-make))))))

(local
 (defthm fn-cbo-finish-is-idle
   (implies (fn-sn-completion-enabledp s)
            (fn-own-store-idlep (fn-sn-finish s)))
   :hints (("Goal" :use fn-snt-finish-image
            :in-theory (union-theories (theory 'minimal-theory)
                                       '(fn-own-store-idlep fn-snt-idle-phasep
                                         (:executable-counterpart member-equal)))))))

(local
 (defthm fn-cbo-ocfg-owner-of-with-owner
   (equal (fn-ocfg-owner (fn-ocfg-with-owner oc o)) o)
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                              '(fn-ocfg-with-owner fn-ocfg-owner-of-fn-ocfg-make))))))

; KEYSTONE (T2).  Before the finish the store is at :completing with the
; history's articles the catalog's rows followed by the completing record W,
; and the pending PreparedCommit's held row materializes to W (alpha).  After
; the host's finish and fn-cat-complete by the pending's token, R holds as
; the equality at the idle store, and the owner's live relation with it.
(defthm fn-cat-ocl-relation-of-article-finish
  (implies (and (fn-ocl-relation oc)
                (fn-cat-history-relation records0 fn-arena fn-cat)
                (fn-sn-completion-enabledp (fn-own-store (fn-ocfg-owner oc)))
                (equal (fn-sf-article-records
                        (fn-cat-history-articles (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                                         fn-arena))
                       (append (fn-sf-article-records records0) (list w)))
                (fn-pc-p pending)
                (equal token (fn-pc-token pending))
                (equal (fn-pc-expected pending) (fn-cat-count fn-cat))
                (< (fn-record-payload (fn-pc-held pending)) (fn-arena-count fn-arena))
                (equal (fn-held-wire-of (fn-pc-held pending) fn-arena) w)
                (fn-record-p w))
           (fn-cat-ocl-relation
            (fn-ocfg-with-owner oc (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena)))
            fn-arena
            (mv-nth 2 (fn-cat-complete token pending fn-cat))))
  :hints (("Goal" :use (fn-ocmt-post-commit-preserves-ocl-relation
                        (:instance fn-cat-relation-of-complete (records records0))
                        (:instance fn-cat-history-relation-reads-the-articles
                                   (a (append records0 (list w)))
                                   (b (fn-cat-history-articles
                                       (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                                       fn-arena))
                                   (fn-cat (mv-nth 2 (fn-cat-complete token pending fn-cat))))
                        (:instance fn-snt-finish-keeps-records (s (fn-own-store (fn-ocfg-owner oc))))
                        (:instance fn-cbo-finish-is-idle (s (fn-own-store (fn-ocfg-owner oc))))
                        (:instance fn-cbo-complete-store (o (fn-ocfg-owner oc))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-cat-ocl-relation fn-cbo-finish-owner-is-complete
                                        fn-cbo-ocfg-owner-of-with-owner
                                        fn-sf-article-records-of-append fn-sf-article-records
                                        car-cons cdr-cons
                                        (:executable-counterpart consp))))))

; T2 in the form the host's finish needs: whatever catalog step restores R
; over the history's articles (the article completion, or the host's
; T4-then-T2 books/served-catalog-owner.lisp fn-sca-finish), the owner the
; finish installs is in R with it, at the idle store the finish leaves.
(defthm fn-cat-ocl-relation-of-article-finish-by
  (implies (and (fn-ocl-relation oc)
                (fn-sn-completion-enabledp (fn-own-store (fn-ocfg-owner oc)))
                (equal (fn-sf-article-records
                        (fn-cat-history-articles (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                                         fn-arena))
                       (append (fn-sf-article-records records0) (list w)))
                (fn-record-p w)
                (fn-cat-history-relation (append records0 (list w)) fn-arena fn-cat2))
           (fn-cat-ocl-relation
            (fn-ocfg-with-owner oc (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena)))
            fn-arena fn-cat2))
  :hints (("Goal" :use (fn-ocmt-post-commit-preserves-ocl-relation
                        (:instance fn-cat-history-relation-reads-the-articles
                                   (a (append records0 (list w)))
                                   (b (fn-cat-history-articles
                                       (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                                       fn-arena))
                                   (fn-cat fn-cat2))
                        (:instance fn-snt-finish-keeps-records (s (fn-own-store (fn-ocfg-owner oc))))
                        (:instance fn-cbo-finish-is-idle (s (fn-own-store (fn-ocfg-owner oc))))
                        (:instance fn-cbo-complete-store (o (fn-ocfg-owner oc))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-cat-ocl-relation fn-cbo-finish-owner-is-complete
                                        fn-cbo-ocfg-owner-of-with-owner
                                        fn-sf-article-records-of-append fn-sf-article-records
                                        car-cons cdr-cons
                                        (:executable-counterpart consp))))))

; The state before T2 is a state of R (its prefix form): the catalog's rows
; are a prefix of the history's articles.
(local (defthm fn-cbo-prefixp-of-append
   (implies (true-listp x) (fn-sf-prefixp x (append x y)))
   :hints (("Goal" :induct (true-listp x)))))

(defthm fn-cat-ocl-relation-before-article-finish
  (implies (and (fn-ocl-relation oc)
                (fn-cat-history-relation records0 fn-arena fn-cat)
                (equal (fn-sf-article-records
                        (fn-cat-history-articles (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
                                         fn-arena))
                       (append (fn-sf-article-records records0) (list w))))
           (fn-cat-history-prefix-relation
            (fn-cat-history-articles (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) fn-arena)
            fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-cat-history-relation fn-cat-history-prefix-relation)
                                  (fn-cat-count-is-len fn-cat-at-is-nth fn-cat-p-is-rowsp
                                   fn-cat-handles-inp fn-cat-wire-list fn-sf-article-records))
           :use ((:instance fn-cbo-prefixp-of-append
                            (x (fn-sf-article-records records0)) (y (list w)))
                 (:instance fn-sf-article-records-true-listp (x records0))))))

; T3: the completion of a non-article event keeps the catalog and the
; equality.
(defthm fn-cat-ocl-relation-of-other-finish
  (implies (and (fn-ocl-relation oc)
                (fn-sn-completion-enabledp (fn-own-store (fn-ocfg-owner oc)))
                (fn-cat-history-relation
                 (fn-cat-history-articles (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))) fn-arena)
                 fn-arena fn-cat))
           (fn-cat-ocl-relation
            (fn-ocfg-with-owner oc (cdr (fn-ccar-own-finish (fn-ocfg-owner oc) cfg fn-arena)))
            fn-arena fn-cat))
  :hints (("Goal" :use (fn-ocmt-post-commit-preserves-ocl-relation
                        (:instance fn-snt-finish-keeps-records (s (fn-own-store (fn-ocfg-owner oc))))
                        (:instance fn-cbo-finish-is-idle (s (fn-own-store (fn-ocfg-owner oc))))
                        (:instance fn-cbo-complete-store (o (fn-ocfg-owner oc))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-cat-ocl-relation fn-cbo-finish-owner-is-complete
                                        fn-cbo-ocfg-owner-of-with-owner)))))

; T4, T5: the row updates keep R against the owner, in both forms.
(defthm fn-cat-ocl-relation-of-withdraw
  (implies (and (fn-cat-ocl-relation oc fn-arena fn-cat)
                (natp target) (< target (fn-cat-count fn-cat)) (natp by))
           (fn-cat-ocl-relation oc fn-arena (fn-cat-withdraw target by fn-cat)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-cat-ocl-relation fn-cat-relation-of-withdraw
                                               fn-cat-prefix-relation-of-withdraw)))))

(defthm fn-cat-ocl-relation-of-redecide
  (implies (and (fn-cat-ocl-relation oc fn-arena fn-cat)
                (natp seq) (< seq (fn-cat-count fn-cat)) (fn-hc-p ctx))
           (fn-cat-ocl-relation oc fn-arena (fn-cat-redecide seq ctx fn-cat)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-cat-ocl-relation fn-cat-relation-of-redecide
                                               fn-cat-prefix-relation-of-redecide)))))
