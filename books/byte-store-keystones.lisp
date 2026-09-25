; K3 and K4: the byte-level crash keystones that stand on K2.
;
; specs/crash-model-v2.md section 3.3.  K1 and K2 live in
; books/byte-store-scan.lisp, whose include-closure is the byte model and
; the file kernel.  K3 needs nothing more, but K4 is a statement about
; fn-sn-open-observed, the store-only reopen of books/store-observed, so it
; needs that book and the store-node closure under it.  The host's reopen
; entry is fn-cpo-open-observed (books/config-observed.lisp), which
; host/store-node-host.lisp:159 and host/owner-host.lisp:193 call at every
; process start; K4 does not name it (books/byte-store-k0-recovery.lisp
; states the host's reopen).  That is the seam this book exists at: no
; theorem here reasons about bytes, each is one kernel theorem applied to
; K2's conclusion.
;
; Every proof below runs in (theory 'minimal-theory) with each fact cited,
; and it is chosen rather than measured: the terms here are the same scan of
; the same image that books/byte-store-scan.lisp's last two forms are over,
; and in the ambient theory those reached the rewriter's call-depth limit of
; 1000 with no loop, no useful rule in the Rules list and no checkpoint.
; Nothing here was ever run in the ambient theory, so this is a precaution
; taken from that measurement and not one of its own.

(in-package "ACL2")
(include-book "byte-store-scan")
(include-book "byte-store-programs")
(include-book "store-observed")
(include-book "store-sweep")
(include-book "consumer-store-invariants")

; -----------------------------------------------------------------------------
; K3.  The constructor as a corollary: fn-sf-image-crash, applied to the
; image the scan reads, reproduces it exactly, and lands the kernel in
; :replaying -- which is the phase host/store-node-host.lisp:39 builds.
; fn-sf-recovery-crash-realizes-every-admissible-image is the work and
; covers all four arms (D14-b, D14-c); K3 is that theorem at K2's image.
(defthm fn-bs-store-recovery-is-a-kernel-crash
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image))
           (let* ((scan (fn-bs-scan-store image))
                  (crashed (fn-sf-image-crash ks (fn-bs-scan-frontier scan)
                                              (fn-bs-scan-records scan))))
             (and (equal (fn-sf-frontier crashed) (fn-bs-scan-frontier scan))
                  (equal (fn-sf-records crashed) (fn-bs-scan-records scan))
                  (equal (fn-sf-phase crashed) :replaying))))
  :hints (("Goal"
           :use (fn-bs-store-crash-image-is-kernel-admissible
                 (:instance fn-sf-recovery-crash-realizes-every-admissible-image
                            (s ks)
                            (frontier (fn-bs-scan-frontier
                                       (fn-bs-scan-store image)))
                            (records (fn-bs-scan-records
                                      (fn-bs-scan-store image)))))
           :in-theory (theory 'minimal-theory))))

; -----------------------------------------------------------------------------
; K4, first half, and the one with no vacuous instance: the host's reopen
; entry SUCCEEDS on a byte-level crash image of a related state whose
; observed identity and topic histories replay, in both windows and whatever
; the pending entry operation did.  This is the half
; the wider predicate made new (fn-sn-recovery-admissible-image-reopens,
; lane w11/bytestore-k2); over fn-sf-crash-imagep it could not be stated at
; all in the recovery window.
;
; The identity hypothesis is the kernel's own (commit 4857c648): since
; fn-sn-recover publishes :fault when the article replay succeeds and the
; identity replay does not, the kernel reopen guarantees carry
; fn-sn-observed-identity-okp beside the structural image predicate, and a
; history that fails it is reachable (tests/acl2/store-identity-traces-tests).
; This book stated K4 without it and went red at that commit; it carries the
; same condition over the scanned records, no weaker and no stronger.  E2's
; consumer condition is different: it follows from the maintained completed
; prefix relation and K2's exact crash-image scan, including the recovery
; rollback arm.  The byte theorem must carry that reachable relation rather
; than silently assuming that the observed record history will replay.
; Topic replay is a separate condition of the observed reopen theorem.
; The consumer relation does not establish it for an arbitrary byte crash
; image; a maintained topic/crash bridge is still needed to discharge it.
(defthm fn-bs-crash-image-consumer-replay-ok
  (implies (and (fn-csi-full-relationp s)
                (fn-bs-store-relation bs (fn-sn-files s))
                (fn-bs-crash-imagep bs image))
           (fn-sn-observed-consumer-okp
            (fn-bs-scan-records (fn-bs-scan-store image))))
  :hints (("Goal"
           :use ((:instance fn-bs-store-crash-image-is-kernel-admissible
                            (ks (fn-sn-files s)))
                 (:instance fn-csi-recovery-crash-image-strict-replay
                            (frontier (fn-bs-scan-frontier
                                       (fn-bs-scan-store image)))
                            (records (fn-bs-scan-records
                                      (fn-bs-scan-store image)))))
           :in-theory (theory 'minimal-theory))))

(defthm fn-bs-crash-image-reopens
  (implies (and (fn-csi-full-relationp s)
                (fn-bs-store-relation bs (fn-sn-files s))
                (fn-bs-crash-imagep bs image)
                (fn-sn-observed-identity-okp
                 (fn-bs-scan-records (fn-bs-scan-store image)))
                (fn-sn-observed-topic-okp
                 (fn-bs-scan-records (fn-bs-scan-store image))))
           (fn-sn-open-okp
            (fn-sn-open-observed
             (fn-sn-groups s) (fn-sn-capacity s)
             (fn-bs-scan-frontier (fn-bs-scan-store image))
             (fn-bs-scan-records (fn-bs-scan-store image)))))
  :hints (("Goal"
           :use (fn-bs-crash-image-consumer-replay-ok
                 (:instance fn-bs-store-crash-image-is-kernel-admissible
                            (ks (fn-sn-files s)))
                 (:instance fn-sn-recovery-admissible-image-reopens
                            (frontier (fn-bs-scan-frontier
                                       (fn-bs-scan-store image)))
                            (records (fn-bs-scan-records
                                      (fn-bs-scan-store image)))))
           :in-theory (union-theories '(fn-csi-full-relationp)
                                      (theory 'minimal-theory)))))

; K4.  Acknowledged retention across a BYTE crash: an outcome this store
; acknowledged before the crash names a record of the state the host reopens
; on.  The record half is clause 5 of fn-sf-recovery-admissible-image-facts
; carried through fn-sn-open-observed-success-exact-history, which says the
; reopened file state holds exactly the observed records.
;
; HONEST SCOPE.  Its recovery-window instances are vacuous and its publish
; window instances are not: fn-bs-replay-matches-scan carries (equal
; (fn-sf-successes ks) nil), so a state with an acknowledged outcome is
; outside the window and this theorem is a statement about the publish
; window alone.  That is not a defect of the statement but the physical
; fact D14-b records -- a process that is still recovering has acknowledged
; nothing of its own.  What covers the recovery window is
; fn-bs-crash-image-reopens above, which carries no success hypothesis.
; The kernel lane's judgement stands and is not reopened here: the
; acknowledged-record half is NOT restated over fn-sf-recovery-crash-imagep
; at the kernel, because there both rollback arms would be vacuous with
; nothing left; here the premise is the byte relation and the publish window
; is a live, non-degenerate instance.
(defthm fn-bs-acknowledged-record-survives-byte-crash
  (implies (and (fn-csi-full-relationp s)
                (fn-bs-store-relation bs (fn-sn-files s))
                (fn-bs-crash-imagep bs image)
                (fn-sn-observed-identity-okp
                 (fn-bs-scan-records (fn-bs-scan-store image)))
                (fn-sn-observed-topic-okp
                 (fn-bs-scan-records (fn-bs-scan-store image)))
                (member-equal pair (fn-sf-successes (fn-sn-files s))))
           (let ((opened (fn-sn-open-observed
                          (fn-sn-groups s) (fn-sn-capacity s)
                          (fn-bs-scan-frontier (fn-bs-scan-store image))
                          (fn-bs-scan-records (fn-bs-scan-store image)))))
             (and (fn-sn-open-okp opened)
                  (fn-sf-record-has-pairp
                   pair (fn-sf-records (fn-sn-files (fn-sn-open-state opened)))))))
  :hints (("Goal"
           :use (fn-bs-crash-image-reopens
                 (:instance fn-bs-store-crash-image-is-kernel-admissible
                            (ks (fn-sn-files s)))
                 (:instance fn-sf-recovery-admissible-image-facts
                            (s (fn-sn-files s))
                            (frontier (fn-bs-scan-frontier
                                       (fn-bs-scan-store image)))
                            (records (fn-bs-scan-records
                                      (fn-bs-scan-store image))))
                 (:instance fn-sn-open-observed-success-exact-history
                            (groups (fn-sn-groups s)) (capacity (fn-sn-capacity s))
                            (frontier (fn-bs-scan-frontier
                                       (fn-bs-scan-store image)))
                            (records (fn-bs-scan-records
                                      (fn-bs-scan-store image)))))
           :in-theory (union-theories '(fn-csi-full-relationp)
                                      (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; K-sweep.  The recovery sweep's unlinks are stutters of the byte relation.
;
; Finding F2 of planning/evidence/campaign-dabebb84-2026-09-22.md: a death
; between staging the allocator's next frontier and its rename leaves an
; .allocation- file that is not authority, because the rename is the commit.
; books/store-sweep.lisp now lists it (and every other staging prefix a host
; program uses) as sweepable.  What makes that sound is here and is not about
; prefixes at all: an unlink in :staging, at any name and with any outcome,
; leaves the byte relation to the SAME kernel state and leaves the recovery
; scan -- config, frontier, transaction namespace and records, everything
; fn-sn-open-observed replays and fn-sf-history-recoverablep is evaluated
; over -- exactly as it was.  Nothing in fn-bs-store-relation or
; fn-bs-scan-store reads :staging.
;
; So K1 to K4 cover every cut of the sweep: every pair of the sweep program's
; run is related to the unchanged kernel, and fn-bs-crash-image-reopens
; applies at each (fn-bs-sweep-round-keeps-every-cut-reopenable).  These
; proofs run in the ambient theory with the byte readers opened in hints; the
; terms are unlinks of one directory, not scans of an image.

(defun fn-bs-staging-del (bs name)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs)
              (append (fn-bs-pending bs) (list (list :del-entry :staging name)))
              (fn-bs-next-ino bs)))

(local
 (defthm fn-bs-staging-unlink-is-a-del-or-nothing
   (let ((bs1 (mv-nth 1 (fn-bs-unlink bs :staging name outcome))))
     (or (equal bs1 bs) (equal bs1 (fn-bs-staging-del bs name))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-bs-unlink)))))

(local
 (defthm fn-bs-staging-unlink-preserves-statep-as-del
   (implies (and (fn-bs-statep bs)
                 (not (equal (mv-nth 1 (fn-bs-unlink bs :staging name outcome)) bs)))
            (fn-bs-statep (fn-bs-staging-del bs name)))
   :rule-classes nil
   :hints (("Goal" :use (fn-bs-staging-unlink-is-a-del-or-nothing
                         (:instance fn-bs-unlink-preserves-statep
                                    (s bs) (dir :staging)))
            :in-theory (disable fn-bs-staging-del)))))

(local
 (defthm fn-bs-apply-entries-of-staging-del-other
   (implies (not (equal d :staging))
            (equal (assoc-equal d (fn-bs-apply-entries
                                   dirs (append ops (list (list :del-entry :staging name)))))
                   (assoc-equal d (fn-bs-apply-entries dirs ops))))
   :hints (("Goal" :in-theory (enable fn-bs-apply-entries)))))

(local
 (defthm fn-bs-apply-writes-of-staging-del
   (equal (fn-bs-apply-writes inodes (append ops (list (list :del-entry :staging name))))
          (fn-bs-apply-writes inodes ops))
   :hints (("Goal" :in-theory (enable fn-bs-apply-writes)))))

(defthm fn-bs-staging-del-lookup-elsewhere
  (implies (not (equal d :staging))
           (equal (fn-bs-lookup (fn-bs-staging-del bs name) d n)
                  (fn-bs-lookup bs d n)))
  :hints (("Goal" :in-theory (enable fn-bs-lookup fn-bs-view
                                     fn-bs-apply-ops-dirs-are-apply-entries))))

(defthm fn-bs-staging-del-names-elsewhere
  (implies (not (equal d :staging))
           (equal (fn-bs-names (fn-bs-staging-del bs name) d)
                  (fn-bs-names bs d)))
  :hints (("Goal" :in-theory (enable fn-bs-names fn-bs-view
                                     fn-bs-apply-ops-dirs-are-apply-entries))))

(defthm fn-bs-staging-del-content
  (equal (fn-bs-content (fn-bs-staging-del bs name) ino)
         (fn-bs-content bs ino))
  :hints (("Goal" :in-theory (enable fn-bs-content fn-bs-view
                                     fn-bs-apply-ops-inodes-are-apply-writes))))

(local
 (defthm fn-bs-staging-del-agrees-on-transactions
   (fn-bs-txn-prefix-agreesp (fn-bs-staging-del bs name) bs n count)
   :hints (("Goal" :induct (fn-bs-txn-prefix-agreesp bs bs n count)
            :in-theory (e/d (fn-bs-txn-prefix-agreesp) (fn-bs-staging-del))))))

(defthm fn-bs-staging-del-keeps-the-scan
  (equal (fn-bs-scan-store (fn-bs-staging-del bs name))
         (fn-bs-scan-store bs))
  :hints (("Goal" :in-theory (e/d (fn-bs-scan-store) (fn-bs-staging-del))
           :use ((:instance fn-bs-read-records-under-agreement
                            (a (fn-bs-staging-del bs name)) (b bs) (n 0)
                            (count (len (fn-bs-names bs :transactions))))))))

(local (in-theory (enable fn-bs-ops-for-ino-of-append fn-bs-ops-for-dir-of-append)))

(local
 (defthm fn-bs-append-of-nil-on-a-true-list
   (implies (true-listp x) (equal (append x nil) x))))

(local
 (defthm fn-bs-ops-for-ino-is-a-true-list
   (true-listp (fn-bs-ops-for-ino ops ino))
   :rule-classes :type-prescription))

(local
 (defthm fn-bs-ops-for-dir-is-a-true-list
   (true-listp (fn-bs-ops-for-dir ops dir))
   :rule-classes :type-prescription))

(local
 (defthm fn-bs-ops-for-dir-of-staging-del
   (implies (not (equal d :staging))
            (equal (fn-bs-ops-for-dir (list (list :del-entry :staging name)) d) nil))))

(local
 (defthm fn-bs-ops-for-ino-of-staging-del
   (equal (fn-bs-ops-for-ino (list (list :del-entry :staging name)) ino) nil)))

(local
 (defthm fn-bs-pending-entry-targets-of-append
   (equal (fn-bs-pending-entry-targets (append a b))
          (append (fn-bs-pending-entry-targets a) (fn-bs-pending-entry-targets b)))
   :hints (("Goal" :in-theory (enable fn-bs-pending-entry-targets)))))

(local
 (defthm fn-bs-pending-entry-targets-of-staging-del
   (equal (fn-bs-pending-entry-targets (list (list :del-entry :staging name))) nil)
   :hints (("Goal" :in-theory (enable fn-bs-pending-entry-targets)))))

(local
 (defthm fn-bs-pending-entry-targets-is-a-true-list
   (true-listp (fn-bs-pending-entry-targets ops))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-bs-pending-entry-targets)))))

(local
 (defthm fn-bs-staging-del-accessors
   (and (equal (fn-bs-unit (fn-bs-staging-del bs name)) (fn-bs-unit bs))
        (equal (fn-bs-inodes (fn-bs-staging-del bs name)) (fn-bs-inodes bs))
        (equal (fn-bs-dirs (fn-bs-staging-del bs name)) (fn-bs-dirs bs))
        (equal (fn-bs-next-ino (fn-bs-staging-del bs name)) (fn-bs-next-ino bs))
        (equal (fn-bs-pending (fn-bs-staging-del bs name))
               (append (fn-bs-pending bs) (list (list :del-entry :staging name)))))))

(local
 (defthm fn-bs-staging-del-durable
   (equal (fn-bs-durable (fn-bs-staging-del bs name)) (fn-bs-durable bs))
   :hints (("Goal" :in-theory (enable fn-bs-durable)))))

(local
 (defthm fn-bs-staging-del-fencedp
   (equal (fn-bs-fencedp (fn-bs-staging-del bs name) ino) (fn-bs-fencedp bs ino))
   :hints (("Goal" :in-theory (e/d (fn-bs-fencedp) (fn-bs-staging-del))))))

(local
 (defthm fn-bs-staging-del-all-fencedp
   (equal (fn-bs-all-fencedp (fn-bs-staging-del bs name) inos) (fn-bs-all-fencedp bs inos))
   :hints (("Goal" :in-theory (e/d (fn-bs-all-fencedp) (fn-bs-staging-del))))))

(local
 (defthm fn-bs-staging-del-knownp
   (equal (fn-bs-inode-list-knownp (fn-bs-staging-del bs name) inos)
          (fn-bs-inode-list-knownp bs inos))
   :hints (("Goal" :in-theory (e/d (fn-bs-inode-list-knownp) (fn-bs-staging-del))))))

(local
 (defthm fn-bs-staging-del-durable-readers
   (and (equal (fn-bs-durable-entry (fn-bs-staging-del bs name) d n)
               (fn-bs-durable-entry bs d n))
        (equal (fn-bs-durable-content (fn-bs-staging-del bs name) ino)
               (fn-bs-durable-content bs ino))
        (equal (fn-bs-durable-names (fn-bs-staging-del bs name) d)
               (fn-bs-durable-names bs d))
        (equal (fn-bs-durable-frontier (fn-bs-staging-del bs name))
               (fn-bs-durable-frontier bs))
        (equal (fn-bs-authority-inode-list (fn-bs-staging-del bs name))
               (fn-bs-authority-inode-list bs)))
   :hints (("Goal" :in-theory (e/d (fn-bs-durable-entry fn-bs-durable-content
                                    fn-bs-durable-names fn-bs-durable-frontier
                                    fn-bs-authority-inode-list)
                                   (fn-bs-staging-del))))))

(local
 (defthm fn-bs-staging-del-durable-records
   (equal (fn-bs-durable-records (fn-bs-staging-del bs name))
          (fn-bs-durable-records bs))
   :hints (("Goal" :in-theory (e/d (fn-bs-durable-records) (fn-bs-staging-del))))))

(local
 (defthm fn-bs-staging-del-keeps-the-window-predicates
   (and (equal (fn-bs-pending-shape-okp (fn-bs-staging-del bs name))
               (fn-bs-pending-shape-okp bs))
        (equal (fn-bs-pending-matches-phase (fn-bs-staging-del bs name) ks)
               (fn-bs-pending-matches-phase bs ks))
        (equal (fn-bs-replay-matches-scan (fn-bs-staging-del bs name) ks)
               (fn-bs-replay-matches-scan bs ks))
        (equal (fn-bs-authority-fencedp (fn-bs-staging-del bs name))
               (fn-bs-authority-fencedp bs))
        (equal (fn-bs-authority-knownp (fn-bs-staging-del bs name))
               (fn-bs-authority-knownp bs)))
   :hints (("Goal" :in-theory (e/d (fn-bs-pending-shape-okp fn-bs-pending-matches-phase
                                    fn-bs-replay-matches-scan fn-bs-authority-fencedp
                                    fn-bs-authority-knownp)
                                   (fn-bs-staging-del))))))

; The step: an unlink in :staging, whatever its outcome, keeps the relation
; to the same kernel state and keeps the scan.
(defthm fn-bs-staging-unlink-keeps-relation-and-scan
  (implies (fn-bs-store-relation bs ks)
           (let ((bs1 (mv-nth 1 (fn-bs-unlink bs :staging name outcome))))
             (and (fn-bs-store-relation bs1 ks)
                  (equal (fn-bs-scan-store bs1) (fn-bs-scan-store bs)))))
  :hints (("Goal"
           :use (fn-bs-staging-unlink-is-a-del-or-nothing
                 fn-bs-staging-unlink-preserves-statep-as-del)
           :in-theory (e/d (fn-bs-store-relation) (fn-bs-staging-del fn-bs-unlink)))))

; The program: every pair of the sweep's run, at every cut, is the unchanged
; kernel state and a byte state related to it with the original scan.
(defun fn-bs-sweep-run-okp (pairs ks scan)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pairs)
      (and (consp (car pairs))
           (equal (cdr (car pairs)) ks)
           (fn-bs-store-relation (car (car pairs)) ks)
           (equal (fn-bs-scan-store (car (car pairs))) scan)
           (fn-bs-sweep-run-okp (cdr pairs) ks scan))
    t))

(defun fn-bs-staging-cleanup-stepsp (steps)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp steps)
      (and (consp (car steps))
           (or (and (equal (car (car steps)) :unlink)
                    (equal (nth 1 (car steps)) :staging))
               (equal (car (car steps)) :cut))
           (fn-bs-staging-cleanup-stepsp (cdr steps)))
    t))

(local
 (defthm fn-bs-sweep-program-is-cleanup-steps
   (fn-bs-staging-cleanup-stepsp (fn-bs-recover-sweep-program names))))

(local
 (defthm fn-bs-cleanup-steps-keep-the-run
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-staging-cleanup-stepsp steps))
            (fn-bs-sweep-run-okp (fn-bs-run bs ks steps outcomes groups capacity)
                                 ks (fn-bs-scan-store bs)))
   :hints (("Goal" :induct (fn-bs-run bs ks steps outcomes groups capacity)
            :in-theory (e/d (fn-bs-step fn-bs-run)
                            (fn-bs-unlink fn-bs-store-relation fn-bs-scan-store))))))

(defthm fn-bs-recover-sweep-keeps-relation-at-every-cut
  (implies (fn-bs-store-relation bs ks)
           (fn-bs-sweep-run-okp
            (fn-bs-run bs ks (fn-bs-recover-sweep-program names) outcomes groups capacity)
            ks (fn-bs-scan-store bs))))

(local
 (defthm fn-bs-sweep-run-okp-member
   (implies (and (fn-bs-sweep-run-okp pairs ks scan) (member-equal pair pairs))
            (and (equal (cdr pair) ks)
                 (fn-bs-store-relation (car pair) ks)
                 (equal (fn-bs-scan-store (car pair)) scan)))))

; The host subject.  host/native/io.lisp fnn-sweep-staging unlinks, round by
; round, exactly the names fn-sn-sweep-round returns (through
; fn-store-sn-sweep-round, host/store-node-host.lisp); its death point after
; each unlink is recovery-stage-unlinked, the :cut of the program.  At every
; such cut, with any syscall outcomes, every crash image of the byte store
; whose identity and topic histories replay (the kernel reopen theorems' own
; conditions) reopens through the host's reopen entry, and the kernel state --
; hence the recoverable history and frontier -- is the one before the sweep.
(defthm fn-bs-sweep-round-keeps-every-cut-reopenable
  (implies (and (fn-csi-full-relationp s)
                (fn-bs-store-relation bs (fn-sn-files s))
                (member-equal pair
                              (fn-bs-run bs (fn-sn-files s)
                                         (fn-bs-recover-sweep-program
                                          (cadr (fn-sn-sweep-round s observed overp held)))
                                         outcomes groups capacity))
                (fn-bs-crash-imagep (car pair) image)
                (fn-sn-observed-identity-okp
                 (fn-bs-scan-records (fn-bs-scan-store image)))
                (fn-sn-observed-topic-okp
                 (fn-bs-scan-records (fn-bs-scan-store image))))
           (and (equal (cdr pair) (fn-sn-files s))
                (equal (fn-bs-scan-store (car pair)) (fn-bs-scan-store bs))
                (fn-sn-open-okp
                 (fn-sn-open-observed
                  (fn-sn-groups s) (fn-sn-capacity s)
                  (fn-bs-scan-frontier (fn-bs-scan-store image))
                  (fn-bs-scan-records (fn-bs-scan-store image))))))
  :hints (("Goal"
           :use ((:instance fn-bs-recover-sweep-keeps-relation-at-every-cut
                            (ks (fn-sn-files s))
                            (names (cadr (fn-sn-sweep-round s observed overp held))))
                 (:instance fn-bs-sweep-run-okp-member
                            (ks (fn-sn-files s)) (scan (fn-bs-scan-store bs))
                            (pairs (fn-bs-run bs (fn-sn-files s)
                                              (fn-bs-recover-sweep-program
                                               (cadr (fn-sn-sweep-round s observed overp held)))
                                              outcomes groups capacity)))
                 (:instance fn-bs-crash-image-reopens (bs (car pair))))
           :in-theory (theory 'minimal-theory))))
