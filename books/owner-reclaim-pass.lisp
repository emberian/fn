; fn: the online reclaim pass that installs (Q16 (a), lane online-reclaim-3,
; 2026-09-29; the coordinator's decisions of 2026-09-29 in
; build/coordinator/lanedumps/online-reclaim.md).
;
; books/owner-reclaim.lisp decides the pass's row rewrite (its octets are
; the offline rewrite) and its decision.  This book decides what the pass
; does around them on a RUNNING owner (host/native/owner.lisp
; fnn-owner-reclaim-pass, through host/owner-host.lisp fn-owner-orcp-*):
;
;   1. Its memory.  The pass holds a second generation of the state (the
;      rewritten rows, the rebuilt Store and its catalog/history columns)
;      beside the served one.  Before it walks, it BORROWS that generation's
;      demand over the captured store -- N records charging C history octets
;      (books/heap-store-figure.lisp fn-heap-reclaim-demand-octets, the
;      figure's own model) -- from the run's completion reserve, the owner's
;      work reserve (books/owner-credits.lisp fn-mca-owner-octets; lane
;      reclaim-funding, planning/design/reclaim-funding-2026-10-04.md),
;      under its own key :reclaim (fn-mcr-borrow).  No user's operation is
;      admitted against that reserve and the borrow leaves the articles'
;      room as it was (fn-orcp-reserve-keeps-the-articles-room), so a pass
;      over any store the profile admits is funded on every ledger the run
;      reaches with no pass in flight (KEYSTONE fn-orcp-profile-admitted-
;      reclaim-is-funded).  A refusal is by name, the ledger unchanged; the
;      credit is returned when the pass ends, whatever its end
;      (fn-mcr-return).  Before this lane the pass resized :reclaim out of the
;      articles' pool at sixteen list octets times the offline verbs' four
;      extra history copies: 453 MB for 2,100 articles, refused (S152).
;   2. The swap.  The rebuild runs off the owner mutex over the captured
;      history; under the mutex the swap is taken only when nothing was
;      committed since the capture (the delta is empty: the count, the
;      frontier and the Store are the captured ones) and no off-mutex
;      reader but the pass holds the arena.  Otherwise it is deferred by
;      name (:delta, :readers) and the pass installs nothing.  (A
;      non-empty delta becomes absorbable in O(delta) with the carried
;      finalize verdict, lane incremental-finalize; until then a pass
;      under continuous posting defers.)
;   3. The cuts.  Each step of the pass is a model crash point; a process
;      death before the install's rename leaves the old publication, from
;      the rename on the new one (the byte program's
;      fn-bs-scp-program-crash-is-old-or-new), never a mix; a rerun after a
;      death past the install rewrites nothing more.
(in-package "ACL2")
(include-book "def-loop")
(include-book "owner-reclaim")
(include-book "def-loop")
(include-book "reclaim-cuts") ; *fn-orcp-cuts*
(include-book "owner-credits")
(include-book "owner-checkpoint-open")
(include-book "replay-identity-index")

; -----------------------------------------------------------------------------
; 1. The pass's memory.

(defconst *fn-orcp-credit-key* *fn-mca-reclaim*)

; THE OPT-IN (lane reclaim-funding, section 11, ember's ruling 2026-10-04):
; live reclaim is the operator's choice, `[resources] reclaim_live = true'.
; LIVE is that key.  Without it no owner's work reserve beyond the open's
; exists (books/owner-credits.lisp fn-mca-owner-octets) and a live pass that
; installs (`store reclaim', `--recorded') is refused by name, :offline-only,
; before anything is recorded or reserved; the offline verbs are as ever and
; the dry run, which holds no second generation, is unchanged.
(defun fn-orcp-request-word (mode live word)
  (declare (xargs :guard t))
  (if (and (member-eq mode '(:recorded :reclaim)) (not live))
      :offline-only
    word))

; The reservation over the captured store, N records charging C history
; octets: (:ok CREDITS') with the demand borrowed under :reclaim, or a
; refusal by name with CREDITS kept.  Without the opt-in: (:refused
; :offline-only) -- the request already refused it; this is the capture's
; own check.
(defun fn-orcp-reserve (credits n c live)
  (declare (xargs :guard t))
  (if live
      (fn-mcr-borrow credits *fn-orcp-credit-key* (fn-heap-reclaim-demand-octets n c))
    (list :refused :offline-only)))

; The ledger after the reservation: the reserved one, or CREDITS unchanged.
(defun fn-orcp-reserved-credits (credits n c live)
  (declare (xargs :guard t))
  (fn-mca-ok-or (fn-orcp-reserve credits n c live) credits))

; The pass ended (installed, deferred, abandoned or failed): its credit back
; to the completion reserve.
(defun fn-orcp-release (credits)
  (declare (xargs :guard t))
  (fn-mca-ok-or (fn-mcr-return credits *fn-orcp-credit-key*) credits))

(defthm fn-orcp-credit-key-is-no-connection-or-commit-key
  (and (not (equal (fn-mca-conn-key id) *fn-orcp-credit-key*))
       (not (equal *fn-mca-open* *fn-orcp-credit-key*))
       (not (equal *fn-mca-sealed* *fn-orcp-credit-key*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-mca-conn-key))))

;; The run's ledger in the theorems below is one the run reaches with no
;; pass in flight (books/owner-credits.lisp fn-mca-pass-free-p:
;; fn-mca-initial-is-pass-free, fn-mca-served-steps-keep-pass-free, and
;; fn-orcp-release-of-reserve-is-pass-free below); a second pass is refused
;; :in-flight before it reserves (host/owner-host.lisp fn-owner-orc-capture,
;; S038).

; KEYSTONE.  The reservation never over-commits the ledger, and when it is
; admitted the pass holds exactly its demand while every other operation's
; credit is what it was.
(defthm fn-orcp-reserve-keeps-funded
  (implies (fn-mcr-fundedp credits)
           (fn-mcr-fundedp (fn-orcp-reserved-credits credits n c live)))
  :hints (("Goal" :use ((:instance fn-mcr-borrow-and-return-keep-funded
                                   (l credits) (id *fn-orcp-credit-key*)
                                   (x (fn-heap-reclaim-demand-octets n c))))
                  :in-theory (e/d (fn-orcp-reserved-credits fn-orcp-reserve fn-mca-ok-or)
                                  (fn-mcr-borrow fn-mcr-fundedp fn-heap-reclaim-demand-octets
                                   fn-mcr-borrow-and-return-keep-funded)))))

(defthm fn-orcp-reserve-holds-the-estimate
  (implies (equal (car (fn-orcp-reserve credits n c live)) :ok)
           (and (equal (fn-mcr-credit-of *fn-orcp-credit-key*
                                         (fn-mcr-ops (fn-orcp-reserved-credits credits n c live)))
                       (fn-heap-reclaim-demand-octets n c))
                (implies (not (equal k *fn-orcp-credit-key*))
                         (equal (fn-mcr-credit-of k (fn-mcr-ops (fn-orcp-reserved-credits
                                                                 credits n c live)))
                                (fn-mcr-credit-of k (fn-mcr-ops credits))))))
  :hints (("Goal" :use ((:instance fn-mcr-borrow-sets-the-credit
                                   (l credits) (id *fn-orcp-credit-key*) (a k)
                                   (x (fn-heap-reclaim-demand-octets n c))))
                  :in-theory (e/d (fn-orcp-reserved-credits fn-orcp-reserve)
                                  (fn-mcr-borrow fn-heap-reclaim-demand-octets
                                   fn-mcr-borrow-sets-the-credit)))))

; A refusal is by name and leaves the ledger as it was.
(defthm fn-orcp-reserve-refused-by-name
  (implies (not (equal (car (fn-orcp-reserve credits n c live)) :ok))
           (and (member-equal (fn-orcp-reserve credits n c live)
                              '((:refused :operation-already-admitted)
                                (:refused :completion-reserve-exhausted)
                                (:refused :offline-only)))
                (equal (fn-orcp-reserved-credits credits n c live) credits)))
  :hints (("Goal" :use ((:instance fn-mcr-borrow-refused-by-name
                                   (l credits) (id *fn-orcp-credit-key*)
                                   (x (fn-heap-reclaim-demand-octets n c))))
                  :in-theory (e/d (fn-orcp-reserved-credits fn-orcp-reserve fn-mca-ok-or)
                                  (fn-mcr-borrow fn-heap-reclaim-demand-octets
                                   fn-mcr-borrow-refused-by-name)))))

; K3.  The reservation never takes the users' room: an admitted borrow
; leaves the funded total -- so the room every article's credit is admitted
; against, budget less total -- as it was; with
; fn-mcr-resize-and-move-keep-the-rest (no article transition changes the
; completion reserve) the two are disjoint.
(defthm fn-orcp-reserve-keeps-the-articles-room
  (implies (and (fn-mcr-opsp (fn-mcr-ops credits))
                (equal (car (fn-orcp-reserve credits n c live)) :ok))
           (and (equal (fn-mcr-total (fn-orcp-reserved-credits credits n c live))
                       (fn-mcr-total credits))
                (equal (fn-mcr-budget (fn-orcp-reserved-credits credits n c live))
                       (fn-mcr-budget credits))))
  :hints (("Goal" :use ((:instance fn-mcr-borrow-keeps-the-total
                                   (l credits) (id *fn-orcp-credit-key*)
                                   (x (fn-heap-reclaim-demand-octets n c)))
                        (:instance fn-mcr-borrow-sets-the-credit
                                   (l credits) (id *fn-orcp-credit-key*) (a nil)
                                   (x (fn-heap-reclaim-demand-octets n c))))
                  :in-theory (e/d (fn-orcp-reserved-credits fn-orcp-reserve)
                                  (fn-mcr-borrow fn-heap-reclaim-demand-octets fn-mcr-total
                                   fn-mcr-borrow-keeps-the-total fn-mcr-borrow-sets-the-credit)))))

; THE OPT-IN, off: no reservation, whatever the ledger, the store or the
; demand -- refused by name, the ledger unchanged.  (The request is refused
; before this, fn-orcp-request-word; this is the capture's own check.)
(defthm fn-orcp-reserve-refused-without-the-opt-in
  (and (equal (fn-orcp-reserve credits n c nil) '(:refused :offline-only))
       (equal (fn-orcp-reserved-credits credits n c nil) credits))
  :hints (("Goal" :in-theory (e/d (fn-orcp-reserve fn-orcp-reserved-credits fn-mca-ok-or)
                                  (fn-mcr-borrow)))))

; The request: the passes that install are refused by name without the
; opt-in, before anything is recorded or reserved; with it, and for the dry
; run always, the request's own answer stands.
(defthm fn-orcp-request-word-refuses-an-installing-pass-without-the-opt-in
  (implies (member-equal mode '(:recorded :reclaim))
           (equal (fn-orcp-request-word mode nil word) :offline-only))
  :hints (("Goal" :in-theory (enable fn-orcp-request-word))))

(defthm fn-orcp-request-word-keeps-the-answer-with-the-opt-in-or-for-a-dry-run
  (and (equal (fn-orcp-request-word mode t word) word)
       (equal (fn-orcp-request-word :dry-run live word) word))
  :hints (("Goal" :in-theory (enable fn-orcp-request-word))))

(local
 (defthm fn-orcp-demand-within-the-owner-reserve
   (implies (and live
                 (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
                 (<= (nfix c) (nfix (fn-bs-profile-max-history-octets profile))))
            (<= (fn-heap-reclaim-demand-octets n c) (fn-mca-owner-octets profile live)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (e/d (fn-mca-owner-octets fn-mca-reclaim-reserve-octets
                                    fn-heap-reclaim-octets)
                                   (fn-heap-reclaim-demand-octets fn-heap-store-open-octets
                                    fn-heap-reclaim-excess-octets
                                    fn-bs-profile-max-transactions fn-bs-profile-max-history-octets))
            :use ((:instance fn-heap-reclaim-demand-octets-monotone
                             (n1 n) (c1 c)
                             (n2 (fn-bs-profile-max-transactions profile))
                             (c2 (fn-bs-profile-max-history-octets profile)))
                  (:instance fn-heap-open-and-excess-hold-the-reclaim
                             (ou (fn-heap-open-octets-bound profile nil))
                             (on (fn-heap-open-records-bound profile nil))))))))

; KEYSTONE (K1), CONDITIONED ON THE OPT-IN.  A live reclaim over any store the profile admits -- N
; records within T, charging C history octets within H, as the history gate
; keeps every store (fn-cvec-roomp-is-within-the-profile) -- is funded on a
; pass-free ledger of a run that asked for it (LIVE): the reservation is
; admitted.  (With fn-heap-store-live-figure-holds-every-store-and-its-
; reclaim: the dynamic space the launcher reserved for it holds what it is
; admitted to build.)
(defthm fn-orcp-profile-admitted-reclaim-is-funded
  (implies (and live
                (fn-mca-pass-free-p credits profile live)
                (<= (nfix n) (nfix (fn-bs-profile-max-transactions profile)))
                (<= (nfix c) (nfix (fn-bs-profile-max-history-octets profile))))
           (equal (car (fn-orcp-reserve credits n c live)) :ok))
  :hints (("Goal" :in-theory (e/d (fn-orcp-reserve fn-mca-pass-free-p)
                                  (fn-mcr-borrow fn-heap-reclaim-demand-octets fn-mca-owner-octets
                                   fn-bs-profile-max-transactions fn-bs-profile-max-history-octets
                                   fn-orcp-demand-within-the-owner-reserve))
           :use fn-orcp-demand-within-the-owner-reserve)))

; The release always succeeds, keeps the ledger funded and leaves the pass
; holding nothing.
(defthm fn-orcp-release-frees-the-pass
  (and (implies (fn-mcr-fundedp credits)
                (fn-mcr-fundedp (fn-orcp-release credits)))
       (equal (fn-mcr-credit-of *fn-orcp-credit-key* (fn-mcr-ops (fn-orcp-release credits)))
              0))
  :hints (("Goal" :use ((:instance fn-mcr-borrow-and-return-keep-funded
                                   (l credits) (id *fn-orcp-credit-key*))
                        (:instance fn-mcr-return-gives-back-the-credit
                                   (l credits) (id *fn-orcp-credit-key*) (a nil)))
                  :in-theory (e/d (fn-orcp-release)
                                  (fn-mcr-return fn-mcr-fundedp
                                   fn-mcr-borrow-and-return-keep-funded
                                   fn-mcr-return-gives-back-the-credit)))))

; The pass's end restores what it found: a release after an admitted
; reservation leaves a pass-free ledger pass-free again, with the completion
; reserve and every operation as they were.
(defthm fn-orcp-release-of-reserve-is-pass-free
  (implies (and (fn-mca-pass-free-p credits profile live)
                (fn-mcr-opsp (fn-mcr-ops credits))
                (equal (car (fn-orcp-reserve credits n c live)) :ok))
           (let ((l2 (fn-orcp-release (fn-orcp-reserved-credits credits n c live))))
             (and (fn-mca-pass-free-p l2 profile live)
                  (equal (fn-mcr-completion l2) (fn-mcr-completion credits))
                  (equal (fn-mcr-ops l2) (fn-mcr-ops credits)))))
  :hints (("Goal" :use ((:instance fn-mcr-return-of-borrow
                                   (l credits) (id *fn-orcp-credit-key*)
                                   (x (fn-heap-reclaim-demand-octets n c))))
                  :in-theory (e/d (fn-orcp-release fn-orcp-reserved-credits fn-orcp-reserve
                                   fn-mca-pass-free-p)
                                  (fn-mcr-borrow fn-mcr-return fn-heap-reclaim-demand-octets
                                   fn-mca-owner-octets fn-mcr-return-of-borrow)))))

; -----------------------------------------------------------------------------
; 2. The swap.

; Under the owner mutex, after the rebuild: COUNT-CAP, FRONTIER-CAP, S-CAP
; the capture's record count, frontier and Store; COUNT-NOW, FRONTIER-NOW,
; S-NOW the owner's now; READERS the off-mutex arena readers besides the
; pass.  The counts and frontiers are compared first (O(1)); the Stores only
; when they agree (a Store unchanged since the capture is the captured
; pointer, which EQUAL answers at once).
;   :delta    something was committed since the capture (deferred by name
;             until the delta is absorbable; the pass installs nothing).
;   :busy     the commit pipeline holds a submission (queued, pending or
;             in flight: IDLE nil), decided against the old Store (retried
;             a bounded number of times, then deferred by name).
;   :readers  another reader holds the arena off the mutex (retried a
;             bounded number of times, then deferred by name).
;   :swap     the install and the swap are exact.
(defun fn-orcp-swap-word (count-cap frontier-cap s-cap count-now frontier-now s-now idle readers)
  (declare (xargs :guard t))
  (cond ((not (and (equal count-now count-cap) (equal frontier-now frontier-cap)))
         :delta)
        ((not (equal s-now s-cap)) :delta)
        ((not idle) :busy)
        ((not (equal readers 0)) :readers)
        (t :swap)))

; KEYSTONE.  A swap is taken only over exactly the captured Store with no
; other reader: the rebuilt state replaces a state that is the capture, so
; the swapped owner's history is the rewrite of the owner's whole history
; (fn-orcp-swapped-history-is-the-offline-rewrite below).
(defthm fn-orcp-swap-only-over-the-capture
  (implies (equal (fn-orcp-swap-word count-cap frontier-cap s-cap
                                     count-now frontier-now s-now idle readers)
                  :swap)
           (and (equal s-now s-cap)
                (equal count-now count-cap)
                (equal frontier-now frontier-cap)
                idle
                (equal readers 0)))
  :rule-classes nil)

; The swapped history's octets are the offline rewrite of the whole current
; history: the rows now are the captured rows (the swap word), and their
; rewrite's octets are fn-rclp-events of their octets
; (fn-orc-rewrite-rows-is-the-offline-rewrite).
(defthm fn-orcp-swapped-history-is-the-offline-rewrite
  (implies (and (equal (fn-orcp-swap-word count-cap frontier-cap s-cap
                                          count-now frontier-now s-now idle readers)
                       :swap)
                (equal rows (fn-sf-records (fn-sn-files s-cap))))
           (equal (fn-orc-rows-octets (fn-orc-rewrite-rows rows ctx fn-arena) fn-arena)
                  (fn-rclp-events (fn-orc-rows-octets (fn-sf-records (fn-sn-files s-now))
                                                      fn-arena)
                                  ctx)))
  :hints (("Goal" :use ((:instance fn-orcp-swap-only-over-the-capture)
                        (:instance fn-orc-rewrite-rows-is-the-offline-rewrite))
                  :in-theory (disable fn-orcp-swap-word fn-orc-rows-octets fn-orc-rewrite-rows
                                      fn-rclp-events))))

; -----------------------------------------------------------------------------
; 3. The pass's cuts: *fn-orcp-cuts*, books/reclaim-cuts.lisp (a leaf, so a
; holder declaration can name a cut of the pass: books/handle-holds.lisp).
; The host names each (FN_NATIVE_RECLAIM_FAULT=<cut>:kill on a developer
; image).  What a death at each leaves behind:

(defun fn-orcp-cut-outcome (cut)
  (declare (xargs :guard t))
  (cond ((member-eq cut '(:captured :rewritten :staged :interned :rebuilt)) :old)
        ((member-eq cut '(:installed :swapped :released)) :new)
        (t :unknown)))

(defthm fn-orcp-every-cut-is-old-or-new
  (implies (member-equal cut *fn-orcp-cuts*)
           (member-equal (fn-orcp-cut-outcome cut) '(:old :new))))

(defthm fn-orcp-new-exactly-from-the-install
  (implies (member-equal cut *fn-orcp-cuts*)
           (iff (equal (fn-orcp-cut-outcome cut) :new)
                (member-equal cut '(:installed :swapped :released)))))

; KEYSTONE.  A rerun after a death at a cut that left the new publication
; rewrites nothing more: the rewrite of the rewritten rows has the same
; octets (fn-rclp-events-idempotent through the rewrite's keystone), so the
; rerun's checkpoint is the one installed.  A death at a cut that left the
; old publication reruns the pass over the same history.
(defthm fn-orcp-rerun-rewrites-nothing
  (equal (fn-orc-rows-octets
          (fn-orc-rewrite-rows (fn-orc-rewrite-rows rows ctx fn-arena) ctx fn-arena)
          fn-arena)
         (fn-orc-rows-octets (fn-orc-rewrite-rows rows ctx fn-arena) fn-arena))
  :hints (("Goal" :use ((:instance fn-orc-rewrite-rows-is-the-offline-rewrite)
                        (:instance fn-orc-rewrite-rows-is-the-offline-rewrite
                                   (rows (fn-orc-rewrite-rows rows ctx fn-arena)))
                        (:instance fn-rclp-events-idempotent
                                   (events (fn-orc-rows-octets rows fn-arena))))
                  :in-theory (disable fn-orc-rows-octets fn-orc-rewrite-rows fn-rclp-events))))

; -----------------------------------------------------------------------------
; 4. The rebuild and the swapped owner.

; The rewritten rows interned: each tombstoned record (a plain record, the
; only rows the rewrite makes: fn-orc-record-is-not-held) interned into the
; live arena under the captured Store's keyring and generation
; (fn-intern-event, as the open interns), every other row kept by pointer.
; The host calls it a chunk at a time under the owner mutex (the arena is
; appended by the owner's quanta only); the fresh handles are above every
; count a reader captured, and no row the owner serves names them until
; the swap.  (mv ROWS FN-ARENA), ROWS :bad when a record does not intern.
; Executes by a loop (depth_check: a chunk of rewritten rows, data), as
; books/store-intern.lisp fn-intern-events does: the :logic is the recursion,
; the :exec the loop, equal by the bridge def-loop :fold generates, and the
; guards are verified, so the host's call runs the loop.
(def-loop fn-orcp-intern-rows (rows keyring generation fn-arena)
  :shape :fold :over rows :st fn-arena :done (atom rows) :elt r
  :row (if (fn-record-p r)
           (fn-intern-event r keyring generation fn-arena)
         (mv r fn-arena))
  :next (cdr rows)
  :guard (and (fn-prin-keyringp keyring) (natp generation)))

; The rebuild, off the mutex over the interned rewritten ROWS: the open's
; extension of the empty capture over them (fn-rii-sco-extend, the host's
; extension) and the owner the open installs from it.  (list E OC).
(defun fn-orcp-rebuild (rows configs frontier max-conns)
  (declare (xargs :guard t :verify-guards nil))
  (let ((e (fn-rii-sco-extend (fn-sco-capture configs nil) configs rows)))
    (list e (fn-ock-recover-extended e configs frontier max-conns))))

; KEYSTONE.  The rebuilt owner is the owner the full open of the rewritten
; history installs (fn-owner-recover-from-checkpoint-equals-full-recover over
; the empty prefix): the swap installs what a restart after the reclaim
; opens, over the same rows.  No hypothesis.
(defthm fn-orcp-rebuild-is-the-full-open
  (equal (cadr (fn-orcp-rebuild rows configs frontier max-conns))
         (fn-ock-recover-full configs frontier rows max-conns))
  :hints (("Goal" :use ((:instance fn-owner-recover-from-checkpoint-equals-full-recover
                                   (prefix nil) (suffix rows)))
                  :in-theory (union-theories '(fn-orcp-rebuild fn-rii-sco-extend-is-sco-extend
                                               car-cons cdr-cons binary-append
                                               (:executable-counterpart consp))
                                             (theory 'minimal-theory)))))

; One connection re-pinned to OWNER's live view, as GROUP moves a pin
; (books/served.lisp fn-served-repin): the connection served over OWNER,
; its pin moved, and taken back as fn-own-finish-read takes a read's pin
; back.  Its session, wire, configuration and observation are kept.
(defun fn-orcp-repin-conn (owner conn)
  (declare (xargs :guard t))
  (let* ((sconn (fn-served-repin
                 (fn-own-served-conn owner conn (fn-own-conn-live-session owner conn))))
         (pinned (fn-served-conn-pinned sconn)))
    (fn-own-conn-make-group-indexed (fn-own-conn-id conn)
                                    (fn-served-pinned-version pinned)
                                    (fn-served-pinned-frontier pinned)
                                    (fn-served-conn-wire sconn)
                                    (fn-served-conn-session sconn)
                                    (fn-served-conn-archive sconn)
                                    (fn-own-conn-config conn)
                                    (fn-own-conn-observation conn)
                                    (fn-served-conn-verdicts sconn)
                                    (fn-served-conn-index sconn)
                                    (fn-served-conn-group-index sconn)
                                    (fn-served-conn-control sconn))))

; Executes by a loop (depth_check: the live connections), guards verified so
; the host's call runs it; equal by fn-orcp-repin-conns-loop-is-rev-onto.
(def-loop fn-orcp-repin-conns (owner conns)
  :shape :map :over conns :elt c
  :body (fn-orcp-repin-conn owner c))

; The swapped owner: the rebuilt owner's Store and view; the live owner's
; connections (each re-pinned to the rebuilt view: O(connections)), next
; id, bounds, commit pipeline, ledger, clock, facts, posting
; configuration, feeds, key ring and refused-offer memory.
(defun fn-orcp-swap-base (live rebuilt)
  (declare (xargs :guard t))
  (fn-own-make (fn-own-store rebuilt) (fn-own-view rebuilt)
               nil (fn-own-next-id live) (fn-own-max-conns live)
               (fn-own-pending live) (fn-own-ledger-field live)
               (fn-own-clock live) (fn-own-facts live) (fn-own-config live)
               (fn-own-queue live) (fn-own-inflight live) (fn-own-feeds live)
               (fn-own-node-secret live) (fn-own-refused live) (fn-own-proc live)))

(defun fn-orcp-swapped-owner (live rebuilt)
  (declare (xargs :guard t :verify-guards nil))
  (let ((o (fn-orcp-swap-base live rebuilt)))
    (fn-own-set-conns o (fn-orcp-repin-conns o (fn-own-conns live)))))

; Every re-pinned connection's configuration pin moves to the rebuilt
; configuration, as fn-ocfg-advance moves the pin of the one connection it
; re-pins (books/owner-config.lisp): the connection now reads the rebuilt
; view, which is that configuration's.
(def-loop fn-orcp-pins-at (conns cfg)
  :shape :map :over conns :elt c
  :body (cons (fn-own-conn-id c) cfg))

; What the swap installs (host/owner-host.lisp fn-owner-orcp-swap): the
; swapped owner under the rebuilt configuration, every connection pinned
; to it, the live staged record kept.
(defun fn-orcp-swapped-ocfg (live-oc rebuilt-oc)
  (declare (xargs :guard t :verify-guards nil))
  (let ((o (fn-orcp-swapped-owner (fn-ocfg-owner live-oc) (fn-ocfg-owner rebuilt-oc))))
    (fn-ocfg-make o (fn-ocfg-config rebuilt-oc)
                  (fn-orcp-pins-at (fn-own-conns o) (fn-ocfg-config rebuilt-oc))
                  (fn-ocfg-staged live-oc))))

(defun fn-orcp-conns-boundedp (conns domain)
  (declare (xargs :guard t))
  (if (consp conns)
      (and (fn-own-conn-boundedp (car conns) domain)
           (fn-orcp-conns-boundedp (cdr conns) domain))
    t))

; The swap is admissible when the rebuild installed (not :fault), the live
; configuration is the rebuilt one
; (a live reconfiguration since the capture is a delta) and every
; re-pinned connection's session is bounded by the rebuilt configuration's
; domain (its selected group exists there) -- the runtime check
; fn-own-advance makes of the one connection it re-pins.  O(connections).
(defun fn-orcp-swap-admissiblep (live-oc rebuilt-oc)
  (declare (xargs :guard t :verify-guards nil))
  (and (not (equal rebuilt-oc :fault))
       (equal (fn-ocfg-config live-oc) (fn-ocfg-config rebuilt-oc))
       (fn-orcp-conns-boundedp
        (fn-own-conns (fn-orcp-swapped-owner (fn-ocfg-owner live-oc)
                                             (fn-ocfg-owner rebuilt-oc)))
        (fn-cnode-domain-of (fn-ocfg-config rebuilt-oc)))))

; The decision the host takes under the mutex (fn-owner-orcp-swap-word):
; fn-orcp-swap-word's :swap only when the swap is admissible, else
; :unbound by name -- decided before the install, so an inadmissible swap
; never leaves the new publication installed and the old state served.
(defun fn-orcp-swap-decision (word live-oc rebuilt-oc)
  (declare (xargs :guard t :verify-guards nil))
  (if (eq word :swap)
      (if (fn-orcp-swap-admissiblep live-oc rebuilt-oc) :swap :unbound)
    word))

; KEYSTONE.  The swapped owner serves exactly the Store the full open of the
; rewritten history installs, and keeps every live connection (the same
; ids, in order).
(defthm fn-orcp-swapped-store-is-the-full-open
  (equal (fn-own-store (fn-orcp-swapped-owner
                        live (fn-ocfg-owner (cadr (fn-orcp-rebuild rows configs frontier
                                                                   max-conns)))))
         (fn-own-store (fn-ocfg-owner (fn-ock-recover-full configs frontier rows max-conns))))
  :hints (("Goal" :in-theory (e/d (fn-orcp-swapped-owner fn-orcp-swap-base fn-own-set-conns)
                                  (fn-orcp-rebuild fn-ock-recover-full fn-orcp-repin-conns))
                  :use fn-orcp-rebuild-is-the-full-open)))
