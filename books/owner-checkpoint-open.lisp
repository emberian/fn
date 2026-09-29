; fn: the served owner opens from the Store checkpoint, and publishes the
; next one itself (design planning/design-2026-09-25-bounds.md section 3.1;
; planning/evidence/bounds-p3-2026-09-25.md findings 1 and 7; D27).
;
; host/owner-host.lisp opens the owner on both paths through one ACL2
; composition: it extends a checkpoint C over the records after it
; (`fn-sco-extend'), then installs the owner from the extended value E with
; `fn-ock-recover-extended'.  From a verified checkpoint C is the decoded
; file and the records are the suffix; on a full replay C is the capture of
; the empty prefix and the records are the whole history.  E is the capture
; of the whole history (fn-sco-extend-of-capture-when-history), and the
; owner keeps it as the base of its next publication.
;
; The keystone `fn-owner-recover-from-checkpoint-equals-full-recover' says
; the owner installed from the capture of any prefix P extended over any Q
; is the owner installed by the full open of P ++ Q, where the full open is
; the composition `fn-orec-recover-installs-ocl-relation' is about (the
; Store open fn-cpo-open-observed, the configuration replay fn-cpr-replay,
; fn-own-start, fn-own-configure, fn-ocfg-make).  The archive, the pinned
; views, the Message-ID trie, the group buckets and the ledger are all
; fn-own-start's refresh of the opened Store, so they are equal because the
; opened Store and the configuration are.  No hypothesis.
;
; The publication policy (`fn-ock-publication-duep') and the next checkpoint
; (`fn-ock-next-checkpoint') are ACL2's; the host asks and writes the octets
; through the byte program `fn-bs-scp-program', whose crash keystone
; `fn-bs-scp-program-crash-is-old-or-new' is the P3 one.

(in-package "ACL2")
(include-book "owner-recover-ocl")
(include-book "store-checkpoint-open")
(include-book "store-checkpoint-codec")

; -----------------------------------------------------------------------------
; The owner the host installs

; The host's checks before it installs, and the configured owner it
; installs (owner-host.lisp before this book: the checks at :183-194, the
; install at :195-201).  :fault is the refusal.
(defun fn-ock-install (replayed opened max-conns)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (natp max-conns)
           (equal (fn-sn-open-kind opened) :ok)
           (equal (fn-sf-phase (fn-sn-files (fn-sn-open-state opened)))
                  :recovering)
           (equal (fn-replay-result-kind replayed) :ok))
      (let ((cfg (fn-cnode-config (fn-replay-result-node replayed))))
        (fn-ocfg-make (fn-own-configure
                       (fn-own-start (fn-sn-open-state opened) max-conns)
                       (fn-oag-post-config cfg *fn-record-max-payload*))
                      cfg nil nil))
    :fault))

; The full open's owner: the composition fn-orec-recover-installs-ocl-relation
; is stated over, with the host's checks.
(defun fn-ock-recover-full (configs frontier events max-conns)
  (declare (xargs :guard t :verify-guards nil))
  (fn-ock-install (fn-cpr-replay configs events)
                  (fn-cpo-open-observed configs frontier events)
                  max-conns))

; The function the host calls (host/owner-host.lisp
; fn-owner-recover-extended), over the extended checkpoint E: the Store open
; finishes from E (fn-sco-finalize, the body of fn-sco-open) and the
; configuration is E's configuration fold, finished.
(defun fn-ock-recover-extended (extended configs frontier max-conns)
  (declare (xargs :guard t :verify-guards nil))
  (fn-ock-install (fn-sco-cpr-finish (fn-sco-cpr extended) configs)
                  (fn-sco-finalize extended configs frontier)
                  max-conns))

; An :ok open admitted its history (the first test of fn-cpo-open-observed).
(defthm fn-ock-open-ok-has-history
  (implies (equal (fn-sn-open-kind (fn-cpo-open-observed configs frontier events))
                  :ok)
           (fn-sn-observed-historyp frontier events))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-cpo-open-observed fn-sn-open-error
                                   fn-sn-open-kind)
                                  (fn-cpr-replay fn-sn-statep fn-cpo-install
                                   fn-sn-with-event-index fn-sn-with-topic
                                   fn-sn-with-consumer fn-sn-update-replayed
                                   fn-sn-observed-seed fn-replay-identity
                                   fn-cpe-projection-replay fn-th-prefix-project
                                   fn-replay-advance-txid fn-cei-build
                                   fn-cnode-statep fn-replay-advance-okp
                                   fn-sn-observed-historyp
                                   fn-stx-index-of-store fn-sn-open-ok)))))

; The Store open from the extended capture is the full open (the P3
; keystone; fn-sco-open is fn-sco-finalize after fn-sco-extend).
(defthm fn-ock-finalize-of-extended-capture
  (equal (fn-sco-finalize (fn-sco-extend (fn-sco-capture configs prefix)
                                         configs suffix)
                          configs frontier)
         (fn-cpo-open-observed configs frontier (append prefix suffix)))
  :hints (("Goal" :use fn-sn-recover-from-checkpoint-equals-full-recover
           :in-theory (union-theories (theory 'minimal-theory) '(fn-sco-open)))))

; KEYSTONE.  The owner installed from the capture of P extended over Q is
; the owner the full open of P ++ Q installs: the same configured owner
; (Store, archive, views, trie, ledger, connections, configuration) or
; :fault on both.  No hypothesis.
(defthm fn-owner-recover-from-checkpoint-equals-full-recover
  (equal (fn-ock-recover-extended
          (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
          configs frontier max-conns)
         (fn-ock-recover-full configs frontier (append prefix suffix) max-conns))
  :hints (("Goal"
           :cases ((equal (fn-sn-open-kind
                           (fn-cpo-open-observed configs frontier
                                                 (append prefix suffix)))
                          :ok))
           :use ((:instance fn-ock-open-ok-has-history
                            (events (append prefix suffix)))
                 fn-sco-extend-of-capture-when-history)
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-ock-recover-extended fn-ock-recover-full
                                        fn-ock-install
                                        fn-ock-finalize-of-extended-capture)))))

; The full path the host takes when no checkpoint verified: the capture of
; the empty prefix extended over the whole history.
(defthm fn-ock-recover-from-empty-capture-is-full
  (equal (fn-ock-recover-extended
          (fn-sco-extend (fn-sco-capture configs nil) configs events)
          configs frontier max-conns)
         (fn-ock-recover-full configs frontier events max-conns))
  :hints (("Goal" :use ((:instance fn-owner-recover-from-checkpoint-equals-full-recover
                                   (prefix nil) (suffix events)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(append (:executable-counterpart consp))))))

; What the carried served keystones need, of the owner the host installs on
; either path: fn-orec-recover-installs-ocl-relation transferred through the
; keystone.
(defthm fn-ock-recover-installs-ocl-relation
  (let ((oc (fn-ock-recover-extended
             (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
             configs frontier max-conns)))
    (implies (not (equal oc :fault))
             (and (fn-ocl-relation oc)
                  (fn-scar-view-indexedp (fn-ocfg-owner oc)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-owner-recover-from-checkpoint-equals-full-recover
                 (:instance fn-orec-recover-installs-ocl-relation
                            (events (append prefix suffix))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-ock-recover-full fn-ock-install)))))

; -----------------------------------------------------------------------------
; The owner's publication

; P is a prefix of R, without allocating.
(defun fn-ock-prefixp (p r)
  (declare (xargs :guard t))
  (if (consp p)
      (and (consp r) (equal (car p) (car r)) (fn-ock-prefixp (cdr p) (cdr r)))
    t))

(local
 (defthm fn-ock-prefixp-splits
   (implies (and (fn-ock-prefixp p r) (true-listp p))
            (equal (append p (nthcdr (len p) r)) r))
   :hints (("Goal" :induct (fn-ock-prefixp p r)))))

; The next checkpoint: BASE extended over the records after it when BASE's
; records are a prefix of the history, else the capture of the whole
; history.  The comparison is pointer-equal on the owner's shared spine in
; practice; it is linear, and so is the encoding that follows it.
(defun fn-ock-next-checkpoint (base configs records)
  (declare (xargs :guard t :verify-guards nil))
  (let ((prefix (fn-sco-records base)))
    (if (and (true-listp prefix) (true-listp records)
             (fn-ock-prefixp prefix records))
        (fn-sco-extend base configs (nthcdr (len prefix) records))
      (fn-sco-capture configs records))))

(local
 (defthm fn-ock-true-listp-of-nthcdr
   (implies (true-listp r) (true-listp (nthcdr n r)))))

(local
 (defthm fn-ock-append-true-list-fix
   (equal (append (true-list-fix p) s) (append p s))))

(local
 (defthm fn-ock-true-listp-true-list-fix
   (true-listp (true-list-fix x))))

(local
 (defthm fn-ock-sco-records-of-capture
   (equal (fn-sco-records (fn-sco-capture configs records))
          (true-list-fix records))
   :hints (("Goal" :in-theory (enable fn-sco-records fn-sco-capture fn-sco-make
                                      fn-sco-at)))))

(local
 (defthm fn-ock-capture-of-true-list-fix
   (equal (fn-sco-capture configs (true-list-fix p))
          (fn-sco-capture configs p))
   :hints (("Goal" :in-theory (e/d (fn-sco-capture)
                                   (fn-sco-cpr-prefix fn-replay-identity-loop
                                    fn-cpe-projection-replay fn-th-prefix-loop
                                    fn-cei-build-aux))))))

; KEYSTONE of the publication, no hypothesis.  From the capture of any
; record list, the owner publishes the capture of the whole history: when the
; base's records are a prefix of a true-list history the extension over the
; rest is that capture (a record that is not a Store event faults the
; identity fold stickily, so no history hypothesis is needed), and otherwise
; the definition captures the history afresh.  That is
; exactly the checkpoint the verb would capture, so a restart that opens it
; serves what a full replay serves (with the P3 keystone, for every later
; suffix).  The publication reads the owner and writes only the owner's
; checkpoint globals (host/owner-host.lisp fn-owner-sco-publish-octets), so
; it changes no served state.
(defthm fn-ock-next-checkpoint-is-the-capture
  (equal (fn-ock-next-checkpoint (fn-sco-capture configs prefix)
                                 configs records)
         (fn-sco-capture configs records))
  :hints (("Goal"
           :use ((:instance fn-sco-extend-of-capture
                            (prefix (true-list-fix prefix))
                            (suffix (nthcdr (len prefix) records)))
                 (:instance fn-ock-prefixp-splits
                            (p (true-list-fix prefix)) (r records)))
           :in-theory (e/d (fn-ock-next-checkpoint)
                           (fn-sco-extend fn-sco-capture fn-sco-store-eventsp
                            fn-ock-prefixp fn-ock-prefixp-splits
                            fn-sco-extend-of-capture)))))

; Opening what the owner published, over any records committed after it, is
; the full open of the whole history: a publication never changes the state
; a restart serves.
(defthm fn-ock-published-checkpoint-opens-to-the-full-open
  (implies (fn-sn-observed-historyp frontier0 records)
           (equal (fn-sco-open (fn-ock-next-checkpoint (fn-sco-capture configs prefix)
                                                       configs records)
                               configs frontier later)
                  (fn-cpo-open-observed configs frontier (append records later))))
  :hints (("Goal" :use (fn-ock-next-checkpoint-is-the-capture
                        (:instance fn-sn-recover-from-checkpoint-equals-full-recover
                                   (prefix records) (suffix later)))
           :in-theory (union-theories (theory 'minimal-theory) '()))))

; When the owner publishes: the suffix since the newest durable checkpoint
; (sequence DURABLE, or none: NIL) has reached half of K, the profile's
; max-open-suffix (twice the suffix is at least K), and at least one record; and COUNT differs from the count
; of the last attempt, so a failed publication is retried only after another
; commit.  Half of K leaves the owner the other half of K commits to finish
; the publication before a restart would fall back to full replay.
(defun fn-ock-publication-duep (durable count k attempted)
  (declare (xargs :guard t))
  (let ((s (if (natp durable) durable 0)))
    (and (natp count)
         (<= s count)
         (not (equal count attempted))
         (< s count)
         (<= (nfix k) (+ (- count s) (- count s))))))

; Until the owner is due, a restart opens from the durable checkpoint: the
; suffix it leaves is within K, so fn-sco-select serves the checkpoint.
(defthm fn-ock-not-due-keeps-the-checkpoint-open
  (implies (and (natp durable) (natp count) (<= durable count) (natp k)
                (not (equal count attempted))
                (not (fn-ock-publication-duep durable count k attempted)))
           (equal (car (fn-sco-select :ok durable count k)) :checkpoint))
  :hints (("Goal" :in-theory (enable fn-sco-select))))

; -----------------------------------------------------------------------------
; The recovery-lag policy (checkpoint-pipeline-5, PKT-583 (b); gpt-6's review
; of 2026-09-26 section 2).  ONE publication in flight: while one runs
; (INFLIGHT is the count it captured) the owner starts no other, builds no
; estimate and cancels nothing, and a due observation meanwhile is ONE
; coalesced request (:coalesce; the host records it once, for the status
; report, and nothing else happens).  When the publication finishes the
; owner decides again from the newest committed frontier by the same rule
; (`fn-ock-publication-duep' at the count then, against the durable S the
; finish bound to the prefix it captured, never to the count at the finish).
; K is a FAST-PATH THRESHOLD, not a guaranteed maximum suffix: a suffix
; within K at the next open is served from the checkpoint, a longer one is
; the full replay, the honest fallback to the same state
; (fn-sn-recover-from-checkpoint-equals-full-recover).  The suffix at a
; finish is about the commits during the publication (lambda * tau(S)),
; which no due rule can bound: when it exceeds K the remedies are a cheaper
; publication, reserved service or admission limiting (the record).
(defun fn-ock-publication-next (durable count k attempted inflight blockedp)
  (declare (xargs :guard t))
  (cond ((natp inflight)
         (if (fn-ock-publication-duep durable count k attempted) :coalesce :inflight))
        (blockedp :blocked)
        ((fn-ock-publication-duep durable count k attempted) :due)
        (t :idle)))

; Never two: while a publication is in flight the decision is never :due,
; and the request it coalesces is the rule's observation, one word.
(defthm fn-ock-one-publication-in-flight
  (implies (natp inflight)
           (and (not (equal (fn-ock-publication-next durable count k attempted inflight blockedp)
                            :due))
                (iff (equal (fn-ock-publication-next durable count k attempted inflight blockedp)
                            :coalesce)
                     (fn-ock-publication-duep durable count k attempted)))))

; With nothing in flight the decision is the rule's at the frontier it is
; given, unless a recorded deferral blocks.
(defthm fn-ock-publication-next-decides-by-the-rule
  (implies (not (natp inflight))
           (iff (equal (fn-ock-publication-next durable count k attempted inflight blockedp) :due)
                (and (not blockedp) (fn-ock-publication-duep durable count k attempted)))))

; The finish binds the durable S to the prefix the publication captured: the
; next checkpoint's sequence is the count of the records handed to the
; capture, whatever the count is when the write returns.
(defthm fn-ock-finish-binds-the-captured-prefix
  (implies (fn-sn-observed-historyp frontier records)
           (equal (fn-sco-sequence (fn-ock-next-checkpoint (fn-sco-capture configs prefix)
                                                           configs records))
                  (len records)))
  :hints (("Goal" :use fn-ock-next-checkpoint-is-the-capture
           :in-theory (e/d (fn-sco-sequence)
                           (fn-ock-next-checkpoint fn-ock-next-checkpoint-is-the-capture)))))

; K as the fast path's threshold, by the open's selection: the checkpoint a
; finish left at S is served at the next open exactly when the suffix
; committed since is within K; past K the open is the full replay.
(defthm fn-ock-fast-path-within-k-by-definition
  (implies (and (natp s) (natp count) (<= s count) (natp k))
           (and (iff (equal (car (fn-sco-select :ok s count k)) :checkpoint)
                     (<= (- count s) k))
                (implies (< k (- count s))
                         (equal (fn-sco-select :ok s count k)
                                (list :full-replay :suffix-exceeds-k)))))
  :hints (("Goal" :in-theory (enable fn-sco-select))))

; KEYSTONE of the one-pass Store open.  Over the capture of any prefix P
; extended over any Q (the checkpoint path; P = NIL is the full path), the
; open the host installs is the full open of P ++ Q, and when that open is
; :ok the configuration it serves is the full replay's.
(defthm fn-sco-store-open-of-extended-capture
  (let ((r (fn-sco-store-open (fn-sco-extend (fn-sco-capture configs prefix)
                                             configs suffix)
                              configs frontier)))
    (and (equal (cadr r)
                (fn-cpo-open-observed configs frontier (append prefix suffix)))
         (implies (equal (fn-sn-open-kind (cadr r)) :ok)
                  (equal (car r)
                         (fn-cpr-replay configs (append prefix suffix))))))
  :hints (("Goal"
           :use ((:instance fn-sn-recover-from-checkpoint-equals-full-recover)
                 (:instance fn-ock-open-ok-has-history
                            (events (append prefix suffix)))
                 (:instance fn-sco-extend-of-capture-when-history))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-sco-store-open fn-sco-open
                                        car-cons cdr-cons)))))

; -----------------------------------------------------------------------------
; The owner installs from the Store open (checkpoint-cost, PKT-141 finding 3)
;
; The host's Store open (host/store-node-host.lisp fn-store-sn-open-extended)
; computes E and (fn-sco-store-open E configs frontier) once and keeps them;
; the owner (host/owner-host.lisp fn-owner-recover-from-store-open) installs
; with fn-ock-install over that pair, without extending or finalizing again.
(defthm fn-ock-install-of-store-open-by-definition
  (equal (fn-ock-install (car (fn-sco-store-open e configs frontier))
                         (cadr (fn-sco-store-open e configs frontier))
                         max-conns)
         (fn-ock-recover-extended e configs frontier max-conns))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-sco-store-open fn-ock-recover-extended
                                               car-cons cdr-cons)))))

(verify-guards fn-ock-install)
(verify-guards fn-ock-recover-full)
(verify-guards fn-ock-recover-extended)
(verify-guards fn-ock-next-checkpoint)
