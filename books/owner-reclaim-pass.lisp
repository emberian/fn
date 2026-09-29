; fn: the online reclaim pass that installs (Q16 (a), lane online-reclaim-3,
; 2026-09-29; the coordinator's decisions of 2026-09-29 in
; build/coordinator/lanedumps/online-reclaim.md).
;
; books/owner-reclaim.lisp decides the pass's row rewrite (its octets are
; the offline rewrite) and its decision.  This book decides what the pass
; does around them on a RUNNING owner (host/native/owner.lisp
; fnn-owner-reclaim-pass, through host/owner-host.lisp fn-owner-orcp-*):
;
;   1. Its memory.  The pass holds a second copy of the history (the
;      rewritten rows, the rebuilt Store and its catalog/history columns)
;      beside the served one.  Before it walks, it reserves that copy in the
;      run's credit ledger (books/owner-credits.lisp, PRF-380) under its own
;      key :reclaim, at the figure the offline verbs are sized by
;      (books/heap-figure.lisp: the compaction verbs' history copies less
;      the served ones, sixteen octets a list octet, over the history's
;      committed octets).  Past the budget it is refused by name
;      (:memory-budget-exhausted) and nothing else in the ledger moves;
;      the credit is released when the pass ends, whatever its end.
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
(include-book "owner-reclaim")
(include-book "owner-credits")
(include-book "owner-checkpoint-open")
(include-book "replay-identity-index")

; -----------------------------------------------------------------------------
; 1. The pass's memory.

(defconst *fn-orcp-credit-key* :reclaim)

; The pass's second copy of the history, in octets: the copies the offline
; compaction verbs hold beyond the ones serving already holds, at sixteen
; octets a list octet, over HISTORY-OCTETS (the committed record octets the
; owner carries, host/owner-host.lisp fn-owner-record-octets).
(defun fn-orcp-estimate (history-octets)
  (declare (xargs :guard t))
  (* *fn-heap-octets-per-list-octet*
     (- *fn-heap-compaction-history-copies* *fn-heap-serve-history-copies*)
     (nfix history-octets)))

; The reservation: (:ok CREDITS') holding the estimate under :reclaim, or
; (:refused :memory-budget-exhausted), CREDITS kept.
(defun fn-orcp-reserve (credits history-octets)
  (declare (xargs :guard t))
  (fn-mcr-resize credits *fn-orcp-credit-key* (fn-orcp-estimate history-octets)))

; The ledger after the reservation: the reserved one, or CREDITS unchanged.
(defun fn-orcp-reserved-credits (credits history-octets)
  (declare (xargs :guard t))
  (fn-mca-ok-or (fn-orcp-reserve credits history-octets) credits))

; The pass ended (installed, deferred, abandoned or failed): its credit back.
(defun fn-orcp-release (credits)
  (declare (xargs :guard t))
  (fn-mca-ok-or (fn-mcr-resize credits *fn-orcp-credit-key* 0) credits))

(defthm fn-orcp-credit-key-is-no-connection-or-commit-key
  (and (not (equal (fn-mca-conn-key id) *fn-orcp-credit-key*))
       (not (equal *fn-mca-open* *fn-orcp-credit-key*))
       (not (equal *fn-mca-sealed* *fn-orcp-credit-key*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-mca-conn-key))))

; KEYSTONE.  The reservation never over-commits the ledger, and when it is
; admitted the pass holds exactly its estimate while every other operation's
; credit is what it was.
(defthm fn-orcp-reserve-keeps-funded
  (implies (fn-mcr-fundedp credits)
           (fn-mcr-fundedp (fn-orcp-reserved-credits credits history-octets)))
  :hints (("Goal" :use ((:instance fn-mca-ok-or-of-resize-keeps-funded
                                   (l credits) (id *fn-orcp-credit-key*)
                                   (n (fn-orcp-estimate history-octets))))
                  :in-theory (e/d (fn-orcp-reserved-credits fn-orcp-reserve)
                                  (fn-mcr-resize fn-mcr-fundedp fn-orcp-estimate)))))

(defthm fn-orcp-reserve-holds-the-estimate
  (implies (equal (car (fn-orcp-reserve credits history-octets)) :ok)
           (and (equal (fn-mcr-credit-of *fn-orcp-credit-key*
                                         (fn-mcr-ops (fn-orcp-reserved-credits
                                                      credits history-octets)))
                       (fn-orcp-estimate history-octets))
                (implies (not (equal k *fn-orcp-credit-key*))
                         (equal (fn-mcr-credit-of k (fn-mcr-ops (fn-orcp-reserved-credits
                                                                 credits history-octets)))
                                (fn-mcr-credit-of k (fn-mcr-ops credits))))))
  :hints (("Goal" :use ((:instance fn-mcr-resize-sets-the-credit
                                   (l credits) (id *fn-orcp-credit-key*) (a k)
                                   (n (fn-orcp-estimate history-octets)))
                        (:instance fn-mca-ok-or-of-resize
                                   (l credits) (id *fn-orcp-credit-key*) (c credits)
                                   (n (fn-orcp-estimate history-octets))))
                  :in-theory (e/d (fn-orcp-reserved-credits fn-orcp-reserve)
                                  (fn-mcr-resize fn-mca-ok-or fn-orcp-estimate
                                   fn-mcr-resize-sets-the-credit fn-mca-ok-or-of-resize)))))

; A refusal is by name and leaves the ledger as it was.
(defthm fn-orcp-reserve-refused-by-name
  (implies (not (equal (car (fn-orcp-reserve credits history-octets)) :ok))
           (and (equal (fn-orcp-reserve credits history-octets)
                       '(:refused :memory-budget-exhausted))
                (equal (fn-orcp-reserved-credits credits history-octets) credits)))
  :hints (("Goal" :in-theory (e/d (fn-orcp-reserved-credits fn-orcp-reserve fn-mcr-resize
                                   fn-mca-ok-or)
                                  (fn-mcr-with fn-mcr-set fn-mcr-total fn-mcr-credit-of
                                   fn-orcp-estimate fn-mcr-resize-refuses-exactly-past-the-budget)))))

; The release always succeeds, keeps the ledger funded and leaves the pass
; holding nothing.
(defthm fn-orcp-release-frees-the-pass
  (and (implies (fn-mcr-fundedp credits)
                (fn-mcr-fundedp (fn-orcp-release credits)))
       (equal (fn-mcr-credit-of *fn-orcp-credit-key* (fn-mcr-ops (fn-orcp-release credits)))
              0))
  :hints (("Goal" :use ((:instance fn-mca-ok-or-of-resize-keeps-funded
                                   (l credits) (id *fn-orcp-credit-key*) (n 0))
                        (:instance fn-mcr-resize-sets-the-credit
                                   (l credits) (id *fn-orcp-credit-key*) (a *fn-orcp-credit-key*) (n 0))
                        (:instance fn-mca-ok-or-of-resize
                                   (l credits) (id *fn-orcp-credit-key*) (c credits) (n 0)))
                  :in-theory (e/d (fn-orcp-release)
                                  (fn-mcr-resize fn-mcr-fundedp fn-mca-ok-or
                                   fn-mcr-resize-sets-the-credit fn-mca-ok-or-of-resize
                                   fn-mca-ok-or-of-resize-keeps-funded)))))

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
; 3. The pass's cuts.
;
; The steps in order; each is a point a process death can fall at, and the
; host names it (FN_NATIVE_RECLAIM_FAULT=<cut>:kill on a developer image).
;   :captured   the capture under the mutex (the log rotated, the pass the
;               publication in flight, its credit reserved);
;   :rewritten  the walk over the captured rows off the mutex;
;   :staged     the reclaimed checkpoint written and fenced in staging/;
;   :interned   the tombstoned records interned into the live arena (fresh
;               handles no row names yet);
;   :rebuilt    the rebuilt Store, catalog and history columns off the mutex;
;   :installed  the staged checkpoint renamed into place (the commit point);
;   :swapped    the owner's state replaced by the rebuilt one;
;   :released   the covered segments dropped and their blocks given back
;               (books/extent-retire.lisp).
(defconst *fn-orcp-cuts*
  '(:captured :rewritten :staged :interned :rebuilt :installed :swapped :released))

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
(defun fn-orcp-intern-rows (rows keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-prin-keyringp keyring) (natp generation))
                  :verify-guards nil))
  (if (atom rows)
      (mv nil fn-arena)
    (mv-let (row fn-arena)
      (if (fn-record-p (car rows))
          (fn-intern-event (car rows) keyring generation fn-arena)
        (mv (car rows) fn-arena))
      (if (eq row :bad)
          (mv :bad fn-arena)
        (mv-let (rest fn-arena)
          (fn-orcp-intern-rows (cdr rows) keyring generation fn-arena)
          (if (eq rest :bad)
              (mv :bad fn-arena)
            (mv (cons row rest) fn-arena)))))))

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
  (declare (xargs :guard t :verify-guards nil))
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

(defun fn-orcp-repin-conns (owner conns)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp conns)
      (cons (fn-orcp-repin-conn owner (car conns))
            (fn-orcp-repin-conns owner (cdr conns)))
    nil))

; The swapped owner: the rebuilt owner's Store and view; the live owner's
; connections (each re-pinned to the rebuilt view: O(connections)), next
; id, bounds, commit pipeline, ledger, clock, facts, posting
; configuration, feeds, key ring and refused-offer memory.
(defun fn-orcp-swapped-owner (live rebuilt)
  (declare (xargs :guard t :verify-guards nil))
  (let ((o (fn-own-make (fn-own-store rebuilt) (fn-own-view rebuilt)
                        nil (fn-own-next-id live) (fn-own-max-conns live)
                        (fn-own-pending live) (fn-own-ledger-field live)
                        (fn-own-clock live) (fn-own-facts live) (fn-own-config live)
                        (fn-own-queue live) (fn-own-inflight live) (fn-own-feeds live)
                        (fn-own-node-secret live) (fn-own-refused live))))
    (fn-own-set-conns o (fn-orcp-repin-conns o (fn-own-conns live)))))

; KEYSTONE.  The swapped owner serves exactly the Store the full open of the
; rewritten history installs, and keeps every live connection (the same
; ids, in order).
(defthm fn-orcp-swapped-store-is-the-full-open
  (equal (fn-own-store (fn-orcp-swapped-owner
                        live (fn-ocfg-owner (cadr (fn-orcp-rebuild rows configs frontier
                                                                   max-conns)))))
         (fn-own-store (fn-ocfg-owner (fn-ock-recover-full configs frontier rows max-conns))))
  :hints (("Goal" :in-theory (e/d (fn-orcp-swapped-owner fn-own-set-conns)
                                  (fn-orcp-rebuild fn-ock-recover-full fn-orcp-repin-conns))
                  :use fn-orcp-rebuild-is-the-full-open)))
