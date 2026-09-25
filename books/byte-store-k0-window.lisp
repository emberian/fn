;; fn: K0 inside the recovery window (P-RECOVER, lane k0-recovery).
;;
;; fn-bs-k0w-step-preserves-relation: from a byte state related to a kernel
;; in the recovery window ((fn-bs-replay-visiblep ks): :replaying,
;; :recovering or :fenced-recovery, where the relation is
;; fn-bs-replay-matches-scan and the pending list may still hold the one
;; un-fenced :root rename or :transactions link a dead process left behind),
;; every step of the recovery program with the precondition
;; fn-bs-k0w-step-inputp leaves a related pair, and a syscall leaves the
;; kernel as it was.  The step kinds and what each needs:
;;   :cut         nothing.
;;   :fsync-file  the target is fenced (every authority inode is, by the
;;                relation); any outcome: the step is the identity
;;                (fn-bs-k0w-fenced-fsync-file-is-identity).
;;   :fsync-dir   :ok on any directory (fn-bs-k0w-fence-preserves-relation:
;;                the fence keeps the VIEW, so the scan, and it moves the one
;;                pending authority entry into the durable directory); an
;;                error outcome only on a directory with nothing pending,
;;                where the step is the identity.
;;   :observe     (:recover), (:recovery-barrier :ok) and
;;                (:recovery-barrier :uncertain).  Each keeps the kernel's
;;                frontier, records and successes.  One that leaves the
;;                window ((:recover) to :fault, the fifth barrier to :ready)
;;                needs :root and :transactions quiet
;;                (fn-bs-k0w-authority-quietp): outside the window the
;;                relation reads the DURABLE frontier and records.
;; NOT covered, named: an error outcome of a directory barrier with an entry
;; pending in that directory.  A dropped authority entry changes the view,
;; so the scan no longer matches the kernel; the host reports
;; (:recovery-barrier :uncertain) and StoreIndeterminate.  Also (:recover)
;; from :replaying with an authority entry pending: its :fault arm leaves the
;; window with the entry still pending.  The host's own reopen reaches the
;; program at :recovering (fn-bs-host-reopened-kernel-is-the-recovered-kernel),
;; where (:recover) stutters.
(in-package "ACL2")
(include-book "byte-store-k0-authority-error")

;; ---------------------------------------------------------------------------
;; 1. A directory fence keeps the view, hence the scan.
(defthm fn-bs-k0w-lookup-is-entry-after
  (implies (and x name)
           (equal (fn-bs-lookup s x name)
                  (fn-bs-entry-after (fn-bs-ops-for-dir (fn-bs-pending s) x)
                                     (fn-bs-durable-entry s x name) x name)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bs-apply-entries-entry-is-entry-after
                            (dirs (fn-bs-dirs s)) (ops (fn-bs-pending s)) (dir x))
                 (:instance fn-bs-k8-entry-after-through-directory-ops
                            (ops (fn-bs-pending s)) (dir x)
                            (old (fn-bs-durable-entry s x name))))
           :in-theory (e/d (fn-bs-lookup fn-bs-view fn-bs-durable-entry fn-bs-apply-ops-dirs-are-apply-entries)
                           (fn-bs-apply-entries-entry-is-entry-after fn-bs-k8-entry-after-through-directory-ops
                            fn-bs-entry-after fn-bs-apply-ops fn-bs-apply-entries fn-bs-ops-for-dir)))))
(defthm fn-bs-k0w-fence-keeps-lookup
  (implies (and x name)
           (equal (fn-bs-lookup (fn-bs-fence-dir bs d) x name) (fn-bs-lookup bs x name)))
  :hints (("Goal" :cases ((equal x d)))
          ("Subgoal 2"
           :use ((:instance fn-bs-k0w-lookup-is-entry-after (s bs))
                 (:instance fn-bs-k0w-lookup-is-entry-after (s (fn-bs-fence-dir bs d)))
                 (:instance fn-bs-fence-dir-touches-only-its-directory (s bs) (dir d) (other x))
                 (:instance fn-bs-k8-other-directory-ops-survive-filter (ops (fn-bs-pending bs)) (removed d) (kept x)))
           :in-theory (e/d (fn-bs-durable-entry fn-bs-k8-fence-pending-is-filtered)
                           (fn-bs-lookup fn-bs-fence-dir fn-bs-entry-after fn-bs-ops-for-dir fn-bs-ops-not-for-dir
                            fn-bs-fence-dir-touches-only-its-directory fn-bs-k8-other-directory-ops-survive-filter fn-bs-k8-entry-after-through-directory-ops)))
          ("Subgoal 1" :use ((:instance fn-bs-k8-fence-keeps-view-lookup (dir d)))
           :in-theory (disable fn-bs-k8-fence-keeps-view-lookup fn-bs-lookup fn-bs-fence-dir))))
(defthm fn-bs-k0w-names-through-dir-ops
  (implies (and x (fn-bs-statep s))
           (equal (fn-bs-names s x)
                  (fn-bs-names-after (fn-bs-ops-for-dir (fn-bs-pending s) x)
                                     (fn-bs-durable-names s x) x)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-names-is-names-after-the-pending-list (dir x))
                        (:instance fn-bs-names-after-through-ops-for-dir (ops (fn-bs-pending s))
                                   (old (fn-bs-durable-names s x)) (dir x)))
           :in-theory (e/d (fn-bs-statep) (fn-bs-names fn-bs-names-after fn-bs-durable-names fn-bs-ops-for-dir
                                           fn-bs-names-is-names-after-the-pending-list)))))
(defthm fn-bs-k0w-fence-keeps-names
  (implies (and x (fn-bs-statep bs))
           (equal (fn-bs-names (fn-bs-fence-dir bs d) x) (fn-bs-names bs x)))
  :hints (("Goal" :cases ((equal x d))
           :use ((:instance fn-bs-k0w-names-through-dir-ops (s bs))
                 (:instance fn-bs-k0w-names-through-dir-ops (s (fn-bs-fence-dir bs d)))
                 (:instance fn-bs-fence-dir-preserves-statep (s bs) (dir d))
                 (:instance fn-bs-fence-dir-touches-only-its-directory (s bs) (dir d) (other x))
                 (:instance fn-bs-k8-other-directory-ops-survive-filter (ops (fn-bs-pending bs)) (removed d) (kept x))
                 (:instance fn-bs-apply-entries-names-is-names-after (dirs (fn-bs-dirs bs))
                            (ops (fn-bs-ops-for-dir (fn-bs-pending bs) d)) (dir d))
                 (:instance fn-bs-op-listp-of-ops-for-dir (ops (fn-bs-pending bs)) (dir d)))
           :in-theory (e/d (fn-bs-durable-names fn-bs-k8-fence-pending-is-filtered)
                           (fn-bs-names fn-bs-fence-dir fn-bs-names-after fn-bs-ops-for-dir fn-bs-ops-not-for-dir
                            fn-bs-statep fn-bs-fence-dir-preserves-statep fn-bs-apply-entries-names-is-names-after
                            fn-bs-fence-dir-touches-only-its-directory fn-bs-k8-other-directory-ops-survive-filter
                            fn-bs-op-listp-of-ops-for-dir fn-bs-apply-entries)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (fn-bs-durable-names fn-bs-k8-fence-pending-is-filtered fn-bs-fence-dir fn-bs-names-after
                                  fn-bs-apply-ops-dirs-are-apply-entries fn-bs-statep)
                                 (fn-bs-names fn-bs-ops-for-dir fn-bs-ops-not-for-dir fn-bs-apply-entries fn-bs-apply-ops))))))
(defthm fn-bs-k0w-fence-keeps-txn-lookup
  (equal (fn-bs-lookup (fn-bs-fence-dir bs d) :transactions (fn-bs-txn-name n))
         (fn-bs-lookup bs :transactions (fn-bs-txn-name n)))
  :hints (("Goal" :use ((:instance fn-bs-txn-name-is-a-name (n n))
                        (:instance fn-bs-k0w-fence-keeps-lookup (x :transactions) (name (fn-bs-txn-name n))))
           :in-theory (e/d (fn-bs-namep) (fn-bs-k0w-fence-keeps-lookup fn-bs-fence-dir fn-bs-lookup)))))
(defthm fn-bs-k0w-fence-agrees-on-transaction-read
  (fn-bs-txn-prefix-agreesp (fn-bs-fence-dir bs d) bs n count)
  :hints (("Goal" :induct (fn-bs-txn-prefix-agreesp (fn-bs-fence-dir bs d) bs n count)
           :in-theory (e/d (fn-bs-txn-prefix-agreesp) (fn-bs-fence-dir fn-bs-lookup fn-bs-content)))
))
(defthm fn-bs-k0w-fence-keeps-read-records
  (equal (fn-bs-read-records (fn-bs-fence-dir bs d) n count) (fn-bs-read-records bs n count))
  :hints (("Goal" :use ((:instance fn-bs-read-records-under-agreement (a (fn-bs-fence-dir bs d)) (b bs)))
           :in-theory (disable fn-bs-read-records-under-agreement fn-bs-read-records fn-bs-fence-dir))))
(defthm fn-bs-k0w-fence-keeps-scan
  (implies (fn-bs-statep bs)
           (equal (fn-bs-scan-store (fn-bs-fence-dir bs d)) (fn-bs-scan-store bs)))
  :hints (("Goal" :in-theory (e/d (fn-bs-scan-store) (fn-bs-fence-dir fn-bs-lookup fn-bs-content fn-bs-names fn-bs-read-records
                                                      fn-bs-contiguous-namesp)))))
(defthm fn-bs-k0w-quiet-fence-is-identity
  (implies (and (fn-bs-statep b) (not (fn-bs-ops-for-dir (fn-bs-pending b) d)))
           (equal (fn-bs-fence-dir b d) b))
  :hints (("Goal" :use ((:instance fn-bs-k0s-make-of-parts)
                        (:instance fn-bs-op-listp-implies-true-listp (x (fn-bs-pending b))))
           :in-theory (e/d (fn-bs-fence-dir fn-bs-statep fn-bs-apply-ops)
                           (fn-bs-k0s-make-of-parts fn-bs-op-listp-implies-true-listp)))))
(defthm fn-bs-k0w-targets-of-other-dir-filter
  (implies (not (member-equal d '(:root :transactions)))
           (equal (fn-bs-pending-entry-targets (fn-bs-ops-not-for-dir ops d))
                  (fn-bs-pending-entry-targets ops)))
  :hints (("Goal" :in-theory (enable fn-bs-pending-entry-targets fn-bs-ops-not-for-dir))))
(defthm fn-bs-k0w-other-fence-keeps-authority-dirs
  (implies (not (member-equal d '(:root :transactions)))
           (and (equal (assoc-equal :root (fn-bs-dirs (fn-bs-fence-dir b d))) (assoc-equal :root (fn-bs-dirs b)))
                (equal (assoc-equal :transactions (fn-bs-dirs (fn-bs-fence-dir b d))) (assoc-equal :transactions (fn-bs-dirs b)))))
  :hints (("Goal" :use ((:instance fn-bs-fence-dir-touches-only-its-directory (s b) (dir d) (other :root))
                        (:instance fn-bs-fence-dir-touches-only-its-directory (s b) (dir d) (other :transactions)))
           :in-theory (disable fn-bs-fence-dir-touches-only-its-directory fn-bs-fence-dir))))
(defthm fn-bs-k0w-other-fence-keeps-durable-records
  (implies (not (equal d :transactions))
           (equal (fn-bs-durable-records (fn-bs-fence-dir b d)) (fn-bs-durable-records b)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-fence-dir-touches-only-its-directory (s b) (dir d) (other :transactions))
                 (:instance fn-bs-k0-same-transaction-dir-agreement
                  (u (fn-bs-unit (fn-bs-fence-dir b d))) (i (fn-bs-inodes b))
                  (d1 (fn-bs-dirs (fn-bs-fence-dir b d))) (d2 (fn-bs-dirs b))
                  (m (fn-bs-next-ino (fn-bs-fence-dir b d))) (m2 (fn-bs-next-ino b))
                  (n 0) (count (len (fn-bs-durable-names b :transactions))))
                 (:instance fn-bs-read-records-under-agreement
                  (a (fn-bs-durable (fn-bs-fence-dir b d)))
                  (b (fn-bs-make (fn-bs-unit (fn-bs-fence-dir b d)) (fn-bs-inodes b) (fn-bs-dirs b)
                                 nil (fn-bs-next-ino b)))
                  (n 0) (count (len (fn-bs-durable-names b :transactions)))))
           :in-theory (e/d (fn-bs-durable-records fn-bs-durable fn-bs-durable-names)
                           (fn-bs-read-records fn-bs-txn-prefix-agreesp
                            fn-bs-read-records-under-agreement fn-bs-fence-dir fn-bs-fence-dir-touches-only-its-directory)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (fn-bs-durable-records fn-bs-durable fn-bs-durable-names fn-bs-fence-dir)
                                 (fn-bs-read-records fn-bs-txn-prefix-agreesp fn-bs-apply-ops
                                  fn-bs-read-records-under-agreement fn-bs-fence-dir-touches-only-its-directory))))))
(defthm fn-bs-k0w-other-fence-preserves-relation
  (implies (and (fn-bs-store-relation bs ks) (not (member-equal d '(:root :transactions))))
           (fn-bs-store-relation (fn-bs-fence-dir bs d) ks))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-fence-dir-preserves-statep (s bs) (dir d))
                 (:instance fn-bs-k8-other-directory-ops-survive-filter (ops (fn-bs-pending bs)) (removed d) (kept :root))
                 (:instance fn-bs-k8-other-directory-ops-survive-filter (ops (fn-bs-pending bs)) (removed d) (kept :transactions)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-replay-matches-scan fn-bs-pending-shape-okp fn-bs-pending-matches-phase
                            fn-bs-durable-entry fn-bs-durable-names fn-bs-durable-frontier fn-bs-authority-inode-list
                            fn-bs-authority-fencedp fn-bs-authority-knownp fn-bs-k8-fence-pending-is-filtered)
                           (fn-bs-fence-dir fn-bs-statep fn-sf-statep fn-bs-scan-store fn-bs-durable-records fn-bs-durable-content
                            fn-bs-fencedp fn-bs-all-fencedp fn-bs-inode-list-knownp
                            fn-bs-contiguous-namesp fn-bs-ops-for-dir fn-bs-ops-not-for-dir fn-bs-pending-entry-targets
                            fn-sf-crash-imagep fn-bs-replay-visiblep fn-sf-frontier-rollback-visiblep fn-bs-scan-okp
                            fn-bs-scan-frontier fn-bs-scan-records fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                            fn-bs-record-of fn-bs-durable fn-bs-fence-dir-preserves-statep fn-bs-k8-other-directory-ops-survive-filter)))))
(defthm fn-bs-k0w-pending-link-fence-durable-entries
  (implies (and (fn-bs-store-relation bs ks)
                (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))
           (equal (cdr (assoc-equal :transactions (fn-bs-dirs (fn-bs-fence-dir bs :transactions))))
                  (fn-bs-put-assoc
                   (fn-bs-txn-name (len (fn-bs-durable-names bs :transactions)))
                   (nth 3 (car (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))
                   (cdr (assoc-equal :transactions (fn-bs-dirs bs))))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-store-relation-implies-the-pending-shape
                 (:instance fn-bs-assoc-of-put-assoc-same
                            (k :transactions)
                            (v (fn-bs-put-assoc
                                (fn-bs-txn-name (len (fn-bs-durable-names bs :transactions)))
                                (nth 3 (car (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))
                                (cdr (assoc-equal :transactions (fn-bs-dirs bs)))))
                            (a (fn-bs-dirs bs))))
           :in-theory (enable fn-bs-fence-dir fn-bs-pending-shape-okp fn-bs-apply-ops fn-bs-apply-op))))
(defthm fn-bs-k0w-pending-link-fence-keeps-authority-list
  (implies (and (fn-bs-store-relation bs ks)
                (not (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
                (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))
           (equal (fn-bs-authority-inode-list (fn-bs-fence-dir bs :transactions))
                  (fn-bs-authority-inode-list bs)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-store-relation-implies-the-pending-shape
                 fn-bs-k0w-pending-link-fence-durable-entries
                 (:instance fn-bs-k8-single-transaction-target (ops (fn-bs-pending bs)))
                 (:instance fn-bs-k8-no-root-targets-after-transaction-filter (ops (fn-bs-pending bs)))
                 (:instance fn-bs-k8-strip-cdrs-of-new-assoc
                            (key (fn-bs-txn-name (len (fn-bs-durable-names bs :transactions))))
                            (val (nth 3 (car (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions))))
                            (alist (cdr (assoc-equal :transactions (fn-bs-dirs bs)))))
                 (:instance fn-bs-alistp-of-dir-entries (dirs (fn-bs-dirs bs)) (dir :transactions))
                 (:instance fn-bs-txn-name-not-in-txn-names
                            (i (len (fn-bs-durable-names bs :transactions)))
                            (n (len (fn-bs-durable-names bs :transactions)))))
           :in-theory (enable fn-bs-authority-inode-list fn-bs-pending-shape-okp fn-bs-durable-names fn-bs-statep))))
(defthm fn-bs-k0w-transactions-fence-preserves-relation
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-replay-visiblep ks)
                (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))
           (fn-bs-store-relation (fn-bs-fence-dir bs :transactions) ks))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds fn-bs-store-relation-window-unfolds
                 (:instance fn-bs-replay-matches-scan-unfolds)
                 (:instance fn-bs-scan-okp-unfolds (s bs))
                 fn-bs-k8-fence-materializes-names
                 fn-bs-k8-fenced-durable-records-are-pre-fence-view-read
                 fn-bs-k0w-pending-link-fence-keeps-authority-list
                 (:instance fn-bs-fence-dir-preserves-statep (s bs) (dir :transactions))
                 (:instance fn-bs-ops-for-dir-of-ops-not-for-dir (ops (fn-bs-pending bs)) (dir :transactions)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-replay-matches-scan fn-bs-pending-shape-okp
                            fn-bs-authority-fencedp fn-bs-authority-knownp fn-bs-contiguous-namesp
                            fn-bs-k8-fence-pending-is-filtered)
                           (fn-bs-fence-dir fn-bs-statep fn-sf-statep fn-bs-scan-store fn-bs-durable-records fn-bs-durable-content
                            fn-bs-durable-names fn-bs-names fn-bs-read-records fn-bs-durable-entry fn-bs-durable-frontier
                            fn-bs-fencedp fn-bs-all-fencedp fn-bs-inode-list-knownp fn-bs-authority-inode-list
                            fn-bs-ops-for-dir fn-bs-ops-not-for-dir fn-bs-pending-entry-targets fn-bs-lookup fn-bs-content
                            fn-sf-crash-imagep fn-bs-replay-visiblep fn-sf-frontier-rollback-visiblep fn-bs-scan-okp
                            fn-bs-scan-frontier fn-bs-scan-records fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                            fn-bs-record-of fn-bs-durable fn-bs-fence-dir-preserves-statep fn-bs-ops-for-dir-of-ops-not-for-dir
                            fn-bs-txn-names)))))
(defthm fn-bs-k0w-root-fence-preserves-relation
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-replay-visiblep ks)
                (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :root)))
           (fn-bs-store-relation (fn-bs-fence-dir bs :root) ks))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds fn-bs-store-relation-window-unfolds
                 fn-bs-store-relation-implies-the-pending-shape
                 (:instance fn-bs-replay-matches-scan-unfolds)
                 (:instance fn-bs-k0r-root-fence-durable-entries (b bs))
                 (:instance fn-bs-k0r-root-fence-authority-list (b bs))
                 (:instance fn-bs-fence-dir-preserves-statep (s bs) (dir :root))
                 (:instance fn-bs-ops-for-dir-of-ops-not-for-dir (ops (fn-bs-pending bs)) (dir :root))
                 (:instance fn-bs-k8-other-directory-ops-survive-filter (ops (fn-bs-pending bs)) (removed :root) (kept :transactions)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-replay-matches-scan fn-bs-pending-shape-okp
                            fn-bs-authority-fencedp fn-bs-authority-knownp fn-bs-all-fencedp fn-bs-inode-list-knownp
                            fn-bs-k8-fence-pending-is-filtered)
                           (fn-bs-fence-dir fn-bs-statep fn-sf-statep fn-bs-scan-store fn-bs-durable-records fn-bs-durable-content
                            fn-bs-durable-names fn-bs-names fn-bs-read-records fn-bs-durable-entry fn-bs-durable-frontier
                            fn-bs-fencedp fn-bs-authority-inode-list fn-bs-contiguous-namesp
                            fn-bs-ops-for-dir fn-bs-ops-not-for-dir fn-bs-pending-entry-targets fn-bs-lookup fn-bs-content
                            fn-sf-crash-imagep fn-bs-replay-visiblep fn-sf-frontier-rollback-visiblep fn-bs-scan-okp
                            fn-bs-scan-frontier fn-bs-scan-records fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                            fn-bs-record-of fn-bs-durable fn-bs-fence-dir-preserves-statep fn-bs-ops-for-dir-of-ops-not-for-dir
                            fn-bs-k8-other-directory-ops-survive-filter fn-bs-txn-names fn-bs-inop)))))
(defthm fn-bs-k0w-fence-preserves-relation
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-replay-visiblep ks))
           (fn-bs-store-relation (fn-bs-fence-dir bs d) ks))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((not (consp (fn-bs-ops-for-dir (fn-bs-pending bs) d))) (equal d :root) (equal d :transactions))
           :use (fn-bs-store-relation-unfolds
                 (:instance fn-bs-k0w-quiet-fence-is-identity (b bs))
                 fn-bs-k0w-root-fence-preserves-relation fn-bs-k0w-transactions-fence-preserves-relation
                 fn-bs-k0w-other-fence-preserves-relation)
           :in-theory (e/d () (fn-bs-store-relation fn-bs-fence-dir fn-bs-statep fn-bs-ops-for-dir fn-bs-replay-visiblep
                               fn-bs-k0w-quiet-fence-is-identity)))))
(defthm fn-bs-k0w-not-for-fenced-ino-is-identity
  (implies (and (true-listp ops) (not (fn-bs-ops-for-ino ops ino)))
           (equal (fn-bs-ops-not-for-ino ops ino) ops))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-ino fn-bs-ops-not-for-ino))))
(defthm fn-bs-k0w-fenced-fsync-file-is-identity
  (implies (and (fn-bs-statep bs) (fn-bs-fencedp bs ino))
           (equal (mv-nth 1 (fn-bs-fsync-file bs ino outcome)) bs))
  :hints (("Goal" :use ((:instance fn-bs-k0s-make-of-parts (b bs))
                        (:instance fn-bs-op-listp-implies-true-listp (x (fn-bs-pending bs))))
           :in-theory (e/d (fn-bs-fsync-file fn-bs-fence-file fn-bs-fencedp fn-bs-statep fn-bs-apply-ops
                            fn-bs-crash-select)
                           (fn-bs-k0s-make-of-parts fn-bs-op-listp-implies-true-listp fn-bs-ops-not-for-ino fn-bs-ops-for-ino)))))
(defthm fn-bs-k0w-quiet-fsync-dir-is-identity
  (implies (and (fn-bs-statep bs) (not (fn-bs-ops-for-dir (fn-bs-pending bs) d)))
           (equal (mv-nth 1 (fn-bs-fsync-dir bs d outcome)) bs))
  :hints (("Goal" :use ((:instance fn-bs-k0s-make-of-parts (b bs))
                        (:instance fn-bs-k0w-quiet-fence-is-identity (b bs))
                        (:instance fn-bs-op-listp-implies-true-listp (x (fn-bs-pending bs))))
           :in-theory (e/d (fn-bs-fsync-dir fn-bs-statep fn-bs-apply-ops fn-bs-crash-select fn-bs-k0r-not-for-quiet-dir-is-identity)
                           (fn-bs-k0s-make-of-parts fn-bs-op-listp-implies-true-listp fn-bs-k0w-quiet-fence-is-identity
                            fn-bs-fence-dir fn-bs-ops-for-dir fn-bs-ops-not-for-dir)))))
(defthm fn-bs-k0w-window-kernel-swap
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-replay-visiblep ks)
                (fn-sf-statep ks1) (fn-bs-replay-visiblep ks1)
                (equal (fn-sf-frontier ks1) (fn-sf-frontier ks))
                (equal (fn-sf-records ks1) (fn-sf-records ks))
                (equal (fn-sf-successes ks1) (fn-sf-successes ks)))
           (fn-bs-store-relation bs ks1))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bs-store-relation fn-bs-replay-matches-scan fn-sf-frontier-rollback-visiblep
                                   fn-sf-recovery-visiblep fn-bs-replay-visiblep)
                                  (fn-bs-statep fn-sf-statep fn-bs-scan-store fn-bs-pending-shape-okp fn-bs-durable-records
                                   fn-bs-authority-fencedp fn-bs-authority-knownp fn-bs-durable-frontier fn-sf-record-listp
                                   fn-bs-ops-for-dir fn-bs-durable-content fn-bs-durable-entry fn-bs-contiguous-namesp)))))
(defthm fn-bs-k0w-quiet-window-exit
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-replay-visiblep ks)
                (not (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
                (not (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions))
                (fn-sf-statep ks1) (not (fn-bs-replay-visiblep ks1))
                (equal (fn-sf-frontier ks1) (fn-sf-frontier ks))
                (equal (fn-sf-records ks1) (fn-sf-records ks)))
           (fn-bs-store-relation bs ks1))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds fn-bs-store-relation-window-unfolds
                 fn-bs-replay-matches-scan-unfolds
                 (:instance fn-bs-scan-okp-unfolds (s bs))
                 fn-bs-store-relation-view-frontier-content
                 fn-bs-store-relation-view-namespace-without-a-pending-link
                 fn-bs-view-reads-the-durable-records)
           :in-theory (e/d (fn-bs-store-relation fn-bs-pending-matches-phase fn-sf-crash-imagep fn-bs-durable-frontier)
                           (fn-bs-statep fn-sf-statep fn-bs-scan-store fn-bs-pending-shape-okp fn-bs-durable-records
                            fn-bs-authority-fencedp fn-bs-authority-knownp fn-sf-record-listp fn-bs-replay-matches-scan
                            fn-bs-ops-for-dir fn-bs-durable-content fn-bs-durable-entry fn-bs-contiguous-namesp
                            fn-bs-read-records fn-bs-names fn-bs-durable-names fn-bs-lookup fn-bs-content fn-bs-scan-okp
                            fn-bs-scan-frontier fn-bs-scan-records fn-bs-replay-visiblep)))))
(defun fn-bs-k0w-authority-quietp (bs)
  (declare (xargs :guard t :verify-guards nil))
  (and (not (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
       (not (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions))))
(defun fn-bs-k0w-observation-inputp (bs ks event)
  (declare (xargs :guard t :verify-guards nil))
  (and (member-equal event '((:recover) (:recovery-barrier :ok) (:recovery-barrier :uncertain)))
       (or (fn-bs-k0w-authority-quietp bs)
           (equal event '(:recovery-barrier :uncertain))
           (and (equal event '(:recovery-barrier :ok))
                (or (not (equal (fn-sf-phase ks) :recovering))
                    (< (1+ (fn-sf-barriers ks)) *fn-sf-recovery-barrier-count*)))
           (and (equal event '(:recover)) (not (equal (fn-sf-phase ks) :replaying))))))
(defthm fn-bs-k0w-recovery-observation-kernel-facts
  (implies (and (fn-sf-statep ks)
                (member-equal event '((:recover) (:recovery-barrier :ok) (:recovery-barrier :uncertain))))
           (let ((ks1 (fn-sf-dispatch ks event g c)))
             (and (fn-sf-statep ks1)
                  (equal (fn-sf-frontier ks1) (fn-sf-frontier ks))
                  (equal (fn-sf-records ks1) (fn-sf-records ks))
                  (equal (fn-sf-successes ks1) (fn-sf-successes ks)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-sf-recover-preserves-state (s ks) (groups g) (capacity c))
                        (:instance fn-sf-recovery-barrier-preserves-state (s ks) (result (cadr event))))
           :in-theory (e/d (fn-sf-dispatch fn-sf-recover fn-sf-recovery-barrier)
                                  (fn-sf-statep fn-sf-history-recoverablep fn-sf-recover-preserves-state
                                   fn-sf-recovery-barrier-preserves-state)))))
(defthm fn-bs-k0w-recovery-observation-stays-in-window
  (implies (and (fn-sf-statep ks) (fn-bs-replay-visiblep ks)
                (fn-bs-k0w-observation-inputp bs ks event)
                (not (fn-bs-k0w-authority-quietp bs)))
           (fn-bs-replay-visiblep (fn-sf-dispatch ks event g c)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sf-dispatch fn-sf-recover fn-sf-recovery-barrier fn-bs-replay-visiblep)
                                  (fn-sf-statep fn-sf-history-recoverablep fn-bs-k0w-authority-quietp)))))
(defthm fn-bs-k0w-observation-inputp-events
  (implies (fn-bs-k0w-observation-inputp bs ks event)
           (member-equal event '((:recover) (:recovery-barrier :ok) (:recovery-barrier :uncertain))))
  :rule-classes nil)
(defthm fn-bs-k0w-observation-preserves-relation
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-replay-visiblep ks)
                (fn-bs-k0w-observation-inputp bs ks event))
           (fn-bs-store-relation bs (fn-sf-dispatch ks event g c)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((fn-bs-replay-visiblep (fn-sf-dispatch ks event g c)))
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0w-recovery-observation-kernel-facts
                 fn-bs-k0w-recovery-observation-stays-in-window fn-bs-k0w-observation-inputp-events
                 (:instance fn-bs-k0w-window-kernel-swap (ks1 (fn-sf-dispatch ks event g c)))
                 (:instance fn-bs-k0w-quiet-window-exit (ks1 (fn-sf-dispatch ks event g c))))
           :in-theory (e/d (fn-bs-k0w-authority-quietp)
                           (fn-bs-store-relation fn-sf-dispatch fn-bs-replay-visiblep fn-sf-statep fn-bs-statep
                            fn-bs-k0w-observation-inputp fn-bs-ops-for-dir)))))
(defun fn-bs-k0w-step-inputp (bs ks step outcome)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bs-replay-visiblep ks)
       (fn-bs-store-relation bs ks)
       (case (car step)
         (:cut t)
         (:observe (fn-bs-k0w-observation-inputp bs ks (nth 1 step)))
         (:fsync-file (fn-bs-fencedp bs (fn-bs-lookup bs (nth 1 step) (nth 2 step))))
         (:fsync-dir (or (equal outcome :ok)
                         (not (fn-bs-ops-for-dir (fn-bs-pending bs) (nth 1 step)))))
         (otherwise nil))))
(defthm fn-bs-k0w-step-preserves-relation
  (implies (fn-bs-k0w-step-inputp bs ks step outcome)
           (let ((bs1 (mv-nth 1 (fn-bs-step bs ks step outcome groups capacity)))
                 (ks1 (mv-nth 2 (fn-bs-step bs ks step outcome groups capacity))))
             (and (fn-bs-store-relation bs1 ks1)
                  (or (equal ks1 ks) (equal (car step) :observe)))))
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 (:instance fn-bs-k0w-observation-preserves-relation (event (nth 1 step)) (g groups) (c capacity))
                 (:instance fn-bs-k0w-fence-preserves-relation (d (nth 1 step)))
                 (:instance fn-bs-k0w-fenced-fsync-file-is-identity (ino (fn-bs-lookup bs (nth 1 step) (nth 2 step))))
                 (:instance fn-bs-k0w-quiet-fsync-dir-is-identity (d (nth 1 step))))
           :in-theory (e/d (fn-bs-step fn-bs-k0w-step-inputp fn-bs-k0s-fsync-dir-ok-is-fence)
                           (fn-bs-store-relation fn-bs-fsync-file fn-bs-fsync-dir fn-bs-fence-dir fn-sf-dispatch
                            fn-bs-k0w-observation-inputp fn-bs-lookup fn-bs-fencedp fn-bs-statep fn-bs-ops-for-dir
                            fn-bs-replay-visiblep fn-bs-create fn-bs-write fn-bs-link fn-bs-rename fn-bs-unlink fn-bs-mkdir
                            fn-bs-k0w-fenced-fsync-file-is-identity fn-bs-k0w-quiet-fsync-dir-is-identity)))))
