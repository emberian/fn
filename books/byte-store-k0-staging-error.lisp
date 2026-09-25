; K0 for the staging barrier's error outcome (PKT-086).
;
; fsync(2) of the staging directory can fail.  fn-bs-fsync-dir then lands a
; crash selection of the staging directory's pending entry operations and
; discards the rest (byte-store.lisp).  The staging directory is not
; authority: those operations touch neither the root nor the transactions
; directory, and carry no write, so the durable projections the relation
; reads are those of the state before, and the relation holds after any
; well-formed selection.  byte-store-k0-staging proves the :ok arm
; (fn-bs-k0-staging-fence-preserves-relation); this is the error arm.
(in-package "ACL2")
(include-book "byte-store-k0-staging")


; The staging directory's pending operations are entry operations on it.
(defun fn-bs-k0e-dir-opsp (ops dir)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (and (consp (car ops))
           (member-equal (car (car ops)) '(:set-entry :del-entry))
           (equal (nth 1 (car ops)) dir)
           (fn-bs-k0e-dir-opsp (cdr ops) dir))
    t))
(defthm fn-bs-k0e-dir-opsp-of-ops-for-dir
  (fn-bs-k0e-dir-opsp (fn-bs-ops-for-dir ops dir) dir)
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-dir))))
(defthm fn-bs-k0e-dir-opsp-of-crash-select
  (implies (fn-bs-k0e-dir-opsp ops dir)
           (fn-bs-k0e-dir-opsp (fn-bs-crash-select ops choices unit) dir))
  :hints (("Goal" :in-theory (enable fn-bs-crash-select))))
(defthm fn-bs-k0e-dir-ops-apply-no-writes
  (implies (fn-bs-k0e-dir-opsp ops dir)
           (equal (fn-bs-apply-writes inodes ops) inodes))
  :hints (("Goal" :in-theory (enable fn-bs-apply-writes))))
(defthm fn-bs-k0e-dir-ops-not-for-other
  (implies (and (fn-bs-k0e-dir-opsp ops dir) (not (equal other dir)))
           (not (fn-bs-ops-for-dir ops other)))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-dir))))

; What the error outcome leaves: the fence's projections, with the landed
; selection in place of every staging operation.
(local (defthm fn-bs-k0e-targets-of-not-staging
  (equal (fn-bs-pending-entry-targets (fn-bs-ops-not-for-dir ops :staging))
         (fn-bs-pending-entry-targets ops))
  :hints (("Goal" :induct (fn-bs-ops-not-for-dir ops :staging)
           :in-theory (enable fn-bs-ops-not-for-dir fn-bs-pending-entry-targets)))))
(local (defthm fn-bs-k0e-car-apply-ops
  (and (equal (car (fn-bs-apply-ops inodes dirs ops)) (fn-bs-apply-writes inodes ops))
       (equal (cadr (fn-bs-apply-ops inodes dirs ops)) (fn-bs-apply-entries dirs ops)))
  :hints (("Goal" :use (fn-bs-apply-ops-inodes-are-apply-writes fn-bs-apply-ops-dirs-are-apply-entries)
           :in-theory (disable fn-bs-apply-ops-inodes-are-apply-writes fn-bs-apply-ops-dirs-are-apply-entries
                               fn-bs-apply-ops)))))
(defthm fn-bs-k0e-staging-error-projections
  (implies (not (equal outcome :ok))
           (let ((b1 (mv-nth 1 (fn-bs-fsync-dir b :staging outcome))))
             (and (equal (fn-bs-unit b1) (fn-bs-unit b))
                  (equal (fn-bs-next-ino b1) (fn-bs-next-ino b))
                  (equal (fn-bs-inodes b1) (fn-bs-inodes b))
                  (equal (fn-bs-pending b1) (fn-bs-ops-not-for-dir (fn-bs-pending b) :staging))
                  (equal (assoc-equal :root (fn-bs-dirs b1)) (assoc-equal :root (fn-bs-dirs b)))
                  (equal (assoc-equal :transactions (fn-bs-dirs b1))
                         (assoc-equal :transactions (fn-bs-dirs b)))
                  (equal (fn-bs-durable-entry b1 :root name) (fn-bs-durable-entry b :root name))
                  (equal (fn-bs-durable-content b1 x) (fn-bs-durable-content b x))
                  (equal (fn-bs-durable-names b1 :transactions) (fn-bs-durable-names b :transactions))
                  (equal (fn-bs-durable-frontier b1) (fn-bs-durable-frontier b))
                  (equal (fn-bs-authority-inode-list b1) (fn-bs-authority-inode-list b))
                  (equal (fn-bs-ops-for-dir (fn-bs-pending b1) :root) (fn-bs-ops-for-dir (fn-bs-pending b) :root))
                  (equal (fn-bs-ops-for-dir (fn-bs-pending b1) :transactions)
                         (fn-bs-ops-for-dir (fn-bs-pending b) :transactions)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-k0e-dir-ops-apply-no-writes (dir :staging)
                            (inodes (fn-bs-inodes b))
                            (ops (fn-bs-crash-select (fn-bs-ops-for-dir (fn-bs-pending b) :staging)
                                                     (cdr outcome) (fn-bs-unit b))))
                        (:instance fn-bs-k0e-dir-opsp-of-crash-select (dir :staging)
                            (ops (fn-bs-ops-for-dir (fn-bs-pending b) :staging))
                            (choices (cdr outcome)) (unit (fn-bs-unit b)))
                        (:instance fn-bs-k0e-dir-ops-not-for-other (dir :staging) (other :root)
                            (ops (fn-bs-crash-select (fn-bs-ops-for-dir (fn-bs-pending b) :staging)
                                                     (cdr outcome) (fn-bs-unit b))))
                        (:instance fn-bs-k0e-dir-ops-not-for-other (dir :staging) (other :transactions)
                            (ops (fn-bs-crash-select (fn-bs-ops-for-dir (fn-bs-pending b) :staging)
                                                     (cdr outcome) (fn-bs-unit b)))))
           :in-theory (e/d (fn-bs-fsync-dir fn-bs-durable-entry fn-bs-durable-content
                            fn-bs-durable-names fn-bs-durable-frontier fn-bs-authority-inode-list fn-bs-apply-ops-dirs-are-apply-entries fn-bs-apply-ops-inodes-are-apply-writes fn-bs-apply-entries-keeps-quiet-dir)
                           (fn-bs-k0e-dir-ops-apply-no-writes fn-bs-k0e-dir-opsp-of-crash-select
                            fn-bs-k0e-dir-ops-not-for-other fn-bs-crash-select)))))

; KEYSTONE.  Any well-formed selection of the staging entry operations.
(defthm fn-bs-k0e-staging-error-keeps-durable-records
  (implies (not (equal outcome :ok))
           (equal (fn-bs-durable-records (mv-nth 1 (fn-bs-fsync-dir b :staging outcome)))
                  (fn-bs-durable-records b)))
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0e-staging-error-projections
                 (:instance fn-bs-k0-same-transaction-dir-agreement
                  (u (fn-bs-unit b)) (i (fn-bs-inodes b))
                  (d1 (fn-bs-dirs (mv-nth 1 (fn-bs-fsync-dir b :staging outcome)))) (d2 (fn-bs-dirs b))
                  (m (fn-bs-next-ino b)) (m2 (fn-bs-next-ino b))
                  (n 0) (count (len (fn-bs-durable-names b :transactions))))
                 (:instance fn-bs-read-records-under-agreement
                  (a (fn-bs-durable (mv-nth 1 (fn-bs-fsync-dir b :staging outcome))))
                  (b (fn-bs-make (fn-bs-unit b) (fn-bs-inodes b) (fn-bs-dirs b)
                                 nil (fn-bs-next-ino b)))
                  (n 0) (count (len (fn-bs-durable-names b :transactions)))))
           :in-theory (e/d (fn-bs-durable-records fn-bs-durable)
                           (fn-bs-read-records fn-bs-txn-prefix-agreesp fn-bs-durable-names
                            fn-bs-read-records-under-agreement fn-bs-fsync-dir)))))
(local (defthm fn-bs-k0e-ops-for-ino-of-not-for-dir
  (equal (fn-bs-ops-for-ino (fn-bs-ops-not-for-dir ops d) ino) (fn-bs-ops-for-ino ops ino))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-ino fn-bs-ops-not-for-dir)))))
(local (defthm fn-bs-k0e-error-fencedp
  (implies (not (equal outcome :ok))
           (equal (fn-bs-fencedp (mv-nth 1 (fn-bs-fsync-dir b :staging outcome)) x)
                  (fn-bs-fencedp b x)))
  :hints (("Goal" :use fn-bs-k0e-staging-error-projections
           :in-theory (e/d (fn-bs-fencedp) (fn-bs-fsync-dir))))))
(local (defthm fn-bs-k0e-error-all-fencedp
  (implies (not (equal outcome :ok))
           (equal (fn-bs-all-fencedp (mv-nth 1 (fn-bs-fsync-dir b :staging outcome)) xs)
                  (fn-bs-all-fencedp b xs)))
  :hints (("Goal" :induct (len xs) :in-theory (e/d (fn-bs-all-fencedp) (fn-bs-fsync-dir fn-bs-fencedp))))))
(local (defthm fn-bs-k0e-error-inodes
  (implies (not (equal outcome :ok))
           (equal (fn-bs-inodes (mv-nth 1 (fn-bs-fsync-dir b :staging outcome)))
                  (fn-bs-inodes b)))
  :hints (("Goal" :use fn-bs-k0e-staging-error-projections :in-theory (disable fn-bs-fsync-dir)))))
(local (defthm fn-bs-k0e-error-durable-content
  (implies (not (equal outcome :ok))
           (equal (fn-bs-durable-content (mv-nth 1 (fn-bs-fsync-dir b :staging outcome)) x)
                  (fn-bs-durable-content b x)))
  :hints (("Goal" :use fn-bs-k0e-staging-error-projections
           :in-theory (disable fn-bs-fsync-dir fn-bs-durable-content)))))
(local (defthm fn-bs-k0e-error-known
  (implies (not (equal outcome :ok))
           (equal (fn-bs-inode-list-knownp (mv-nth 1 (fn-bs-fsync-dir b :staging outcome)) xs)
                  (fn-bs-inode-list-knownp b xs)))
  :hints (("Goal" :induct (len xs)
           :in-theory (e/d (fn-bs-inode-list-knownp) (fn-bs-fsync-dir))))))
(defthm fn-bs-k0-staging-fsync-error-preserves-relation
  (implies (and (fn-bs-store-relation b k)
                (not (fn-bs-replay-visiblep k))
                (not (equal outcome :ok))
                (fn-bs-crash-choicesp (cdr outcome)
                                      (fn-bs-ops-for-dir (fn-bs-pending b) :staging)
                                      (fn-bs-unit b)))
           (fn-bs-store-relation (mv-nth 1 (fn-bs-fsync-dir b :staging outcome)) k))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0e-staging-error-projections (name *fn-bs-scan-config-name*))
                 (:instance fn-bs-k0e-staging-error-projections (name *fn-bs-scan-frontier-name*)
                  (x (fn-bs-durable-entry b :root *fn-bs-scan-config-name*)))
                 (:instance fn-bs-store-relation-unfolds (bs b) (ks k))
                 (:instance fn-bs-store-relation-window-unfolds (bs b) (ks k))
                 (:instance fn-bs-fsync-dir-preserves-statep (s b) (dir :staging)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-authority-fencedp fn-bs-authority-knownp
                            fn-bs-pending-matches-phase fn-bs-pending-shape-okp
                            fn-bs-k8-record-of-durable-is-durable-content)
                           (fn-bs-durable fn-bs-durable-names fn-bs-statep fn-bs-fsync-dir
                            fn-bs-durable-records fn-bs-durable-frontier fn-bs-durable-entry
                            fn-bs-durable-content fn-bs-authority-inode-list fn-bs-record-of
                            fn-bs-replay-matches-scan fn-sf-crash-imagep fn-sf-statep
                            fn-bs-contiguous-namesp fn-bs-replay-visiblep fn-bs-fsync-dir-preserves-statep
                            fn-bs-all-fencedp fn-bs-inode-list-knownp fn-bs-fencedp
                            fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep)))))
