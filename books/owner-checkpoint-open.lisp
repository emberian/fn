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
 (defthm fn-ock-prefixp-append-nthcdr
   (implies (fn-ock-prefixp p r)
            (equal (append p (nthcdr (len p) r))
                   (append (true-list-fix p) (nthcdr (len p) r))))
   :hints (("Goal" :in-theory (enable true-list-fix)))))

(local
 (defthm fn-ock-prefixp-splits
   (implies (and (fn-ock-prefixp p r) (true-listp p))
            (equal (append p (nthcdr (len p) r)) r))))

; The next checkpoint: BASE extended over the records after it when BASE's
; records are a prefix of the history, else the capture of the whole
; history.  The comparison is pointer-equal on the owner's shared spine in
; practice; it is linear, and so is the encoding that follows it.
(defun fn-ock-next-checkpoint (base configs records)
  (declare (xargs :guard t :verify-guards nil))
  (let ((prefix (fn-sco-records base)))
    (if (and (true-listp prefix) (fn-ock-prefixp prefix records))
        (fn-sco-extend base configs (nthcdr (len prefix) records))
      (fn-sco-capture configs records))))

(local
 (defthm fn-ock-store-eventsp-of-append
   (implies (fn-sco-store-eventsp (append p s))
            (fn-sco-store-eventsp (true-list-fix p)))
   :hints (("Goal" :in-theory (disable fn-store-event-p)))))

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

; KEYSTONE of the publication.  From the capture of any prefix of an
; admitted history, the owner publishes the capture of the whole history:
; exactly the checkpoint the verb would capture, so a restart that opens it
; serves what a full replay serves (with the P3 keystone, for every later
; suffix).  The publication reads the owner and writes only the owner's
; checkpoint globals (host/owner-host.lisp fn-owner-sco-publish-octets), so
; it changes no served state.
(defthm fn-ock-next-checkpoint-is-the-capture
  (implies (fn-sn-observed-historyp frontier records)
           (equal (fn-ock-next-checkpoint (fn-sco-capture configs prefix)
                                          configs records)
                  (fn-sco-capture configs records)))
  :hints (("Goal"
           :use ((:instance fn-sco-record-listp-shape
                            (sequence 0) (lower 0))
                 (:instance fn-sco-extend-of-capture
                            (prefix (true-list-fix prefix))
                            (suffix (nthcdr (len prefix) records)))
                 (:instance fn-ock-prefixp-splits
                            (p (true-list-fix prefix)) (r records))
                 (:instance fn-ock-store-eventsp-of-append
                            (p prefix)
                            (s (nthcdr (len prefix) records))))
           :in-theory (e/d (fn-sn-observed-historyp fn-ock-next-checkpoint)
                           (fn-sco-extend fn-sco-capture fn-sco-store-eventsp
                            fn-sf-record-listp fn-ock-prefixp
                            fn-sco-record-listp-shape fn-ock-prefixp-splits
                            fn-sco-extend-of-capture fn-sco-records
                            fn-ock-store-eventsp-of-append)))))

; Opening what the owner published, over any records committed after it, is
; the full open of the whole history: a publication never changes the state
; a restart serves.
(defthm fn-ock-published-checkpoint-opens-to-the-full-open
  (implies (fn-sn-observed-historyp frontier0 records)
           (equal (fn-sco-open (fn-ock-next-checkpoint (fn-sco-capture configs prefix)
                                                       configs records)
                               configs frontier later)
                  (fn-cpo-open-observed configs frontier (append records later))))
  :hints (("Goal" :use ((:instance fn-ock-next-checkpoint-is-the-capture
                                   (frontier frontier0))
                        (:instance fn-sn-recover-from-checkpoint-equals-full-recover
                                   (prefix records) (suffix later)))
           :in-theory (union-theories (theory 'minimal-theory) '()))))

; When the owner publishes: the suffix since the newest durable checkpoint
; (sequence DURABLE, or none: NIL) has reached half of K, the profile's
; max-open-suffix, and at least one record; and COUNT differs from the count
; of the last attempt, so a failed publication is retried only after another
; commit.  Half of K leaves the owner the other half of K commits to finish
; the publication before a restart would fall back to full replay.
(defun fn-ock-publication-threshold (k)
  (declare (xargs :guard t))
  (max 1 (floor (nfix k) 2)))

(defun fn-ock-publication-duep (durable count k attempted)
  (declare (xargs :guard t))
  (let ((s (if (natp durable) durable 0)))
    (and (natp count)
         (<= s count)
         (not (equal count attempted))
         (<= (fn-ock-publication-threshold k) (- count s)))))

; Until the owner is due, a restart opens from the durable checkpoint: the
; suffix it leaves is within K, so fn-sco-select serves the checkpoint.
(defthm fn-ock-not-due-keeps-the-checkpoint-open
  (implies (and (natp durable) (natp count) (<= durable count) (natp k)
                (not (equal count attempted))
                (not (fn-ock-publication-duep durable count k attempted)))
           (equal (car (fn-sco-select :ok durable count k)) :checkpoint))
  :hints (("Goal" :in-theory (enable fn-sco-select))))

(verify-guards fn-ock-install)
(verify-guards fn-ock-recover-full)
(verify-guards fn-ock-recover-extended)
(verify-guards fn-ock-next-checkpoint)
