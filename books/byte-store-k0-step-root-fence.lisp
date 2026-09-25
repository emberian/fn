;; fn: the root barrier from any related state (lane k0-cuts, PKT-083).
;;
;; fn-bs-k0s-root-fence-preserves-relation: outside the recovery window, a
;; successful fsync of the root directory (fn-bs-fence-dir bs :root) keeps
;; the relation with the same kernel, whatever is pending on :root.  With
;; nothing pending there the fence is the identity
;; (fn-bs-k0r-quiet-root-fence-is-identity).  Otherwise the relation's
;; pending shape says the one root operation is the frontier rename's
;; set-entry onto a fenced inode whose content decodes to the kernel's
;; frontier candidate, in a frontier-new-visible phase, with no transaction
;; link pending (fn-bs-k0r-related-root-pending-facts); the fence makes that
;; entry durable, which the frontier arm of the kernel's crash images
;; admits, and leaves the config entry, the transaction table and every
;; inode as they were.  This is the fence the frontier program issues at
;; its pair 12 (run_store.py:891), stated for any related state, as
;; fn-bs-k8-pending-link-fence-preserves-relation is for the transaction
;; barrier.  byte-store-k0-step admits it as the :ok arm of the root barrier.
(in-package "ACL2")
(include-book "byte-store-k0-step-lemmas")

(defthm fn-bs-k0r-ops-for-dir-car-is-dir
  (implies (consp (fn-bs-ops-for-dir ops d))
           (and (equal (nth 1 (car (fn-bs-ops-for-dir ops d))) d)
                (member-equal (car (car (fn-bs-ops-for-dir ops d))) '(:set-entry :del-entry))))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-dir))))
(defthm fn-bs-k0r-no-targets-after-root-filter
  (implies (not (fn-bs-ops-for-dir ops :transactions))
           (equal (fn-bs-pending-entry-targets (fn-bs-ops-not-for-dir ops :root)) nil))
  :hints (("Goal" :in-theory (enable fn-bs-ops-not-for-dir fn-bs-ops-for-dir fn-bs-pending-entry-targets))))
(defthm fn-bs-k0r-single-root-target
  (implies (and (not (fn-bs-ops-for-dir ops :transactions))
                (consp (fn-bs-ops-for-dir ops :root))
                (not (consp (cdr (fn-bs-ops-for-dir ops :root))))
                (equal (car (car (fn-bs-ops-for-dir ops :root))) :set-entry))
           (equal (fn-bs-pending-entry-targets ops)
                  (list (nth 3 (car (fn-bs-ops-for-dir ops :root))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bs-pending-entry-targets fn-bs-ops-for-dir))))
(defthm fn-bs-k0r-not-for-quiet-dir-is-identity
  (implies (and (true-listp ops) (not (fn-bs-ops-for-dir ops d)))
           (equal (fn-bs-ops-not-for-dir ops d) ops))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-dir fn-bs-ops-not-for-dir))))
(defthm fn-bs-k0r-quiet-root-fence-is-identity
  (implies (and (fn-bs-statep b) (not (fn-bs-ops-for-dir (fn-bs-pending b) :root)))
           (equal (fn-bs-fence-dir b :root) b))
  :hints (("Goal" :use ((:instance fn-bs-k0s-make-of-parts)
                        (:instance fn-bs-op-listp-implies-true-listp (x (fn-bs-pending b))))
           :in-theory (e/d (fn-bs-fence-dir fn-bs-statep fn-bs-apply-ops)
                           (fn-bs-k0s-make-of-parts fn-bs-op-listp-implies-true-listp)))))
(defthm fn-bs-k0r-related-root-pending-facts
  (implies (and (fn-bs-store-relation bs ks) (not (fn-bs-replay-visiblep ks))
                (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :root)))
           (let* ((r (fn-bs-ops-for-dir (fn-bs-pending bs) :root)) (ino (nth 3 (car r))))
             (and (not (consp (cdr r)))
                  (equal (car (car r)) :set-entry)
                  (equal (nth 2 (car r)) *fn-bs-scan-frontier-name*)
                  (fn-bs-inop ino)
                  (fn-bs-fencedp bs ino)
                  (fn-sf-frontier-new-visiblep ks)
                  (equal (fn-bs-frontier-decode (fn-bs-durable-content bs ino)) (fn-sf-frontier-candidate ks))
                  (not (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))))
  :rule-classes nil
  :hints (("Goal" :use (fn-bs-store-relation-window-unfolds fn-bs-pending-matches-phase-unfolds)
           :in-theory (e/d (fn-bs-pending-shape-okp fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep)
                           (fn-bs-store-relation fn-bs-pending-matches-phase fn-sf-crash-imagep
                            fn-bs-fencedp fn-bs-inop fn-bs-durable-records fn-bs-durable-content)))))
(defthm fn-bs-k0r-single-set-entry-lookups
  (implies (and (consp r) (not (consp (cdr r)))
                (equal (car (car r)) :set-entry) (equal (nth 1 (car r)) :root)
                (equal (nth 2 (car r)) *fn-bs-scan-frontier-name*))
           (and (equal (cdr (assoc-equal *fn-bs-scan-config-name* (cdr (assoc-equal :root (fn-bs-apply-entries dirs r)))))
                       (cdr (assoc-equal *fn-bs-scan-config-name* (cdr (assoc-equal :root dirs)))))
                (equal (cdr (assoc-equal *fn-bs-scan-frontier-name* (cdr (assoc-equal :root (fn-bs-apply-entries dirs r)))))
                       (nth 3 (car r)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-apply-entries-entry-is-entry-after (ops r) (dir :root) (name *fn-bs-scan-config-name*))
                 (:instance fn-bs-apply-entries-entry-is-entry-after (ops r) (dir :root) (name *fn-bs-scan-frontier-name*)))
           :expand ((:free (o d n) (fn-bs-entry-after r o d n))
                    (:free (o d n) (fn-bs-entry-after (cdr r) o d n)))
           :in-theory (e/d () (fn-bs-apply-entries-entry-is-entry-after fn-bs-apply-entries fn-bs-entry-after)))))
(defthm fn-bs-k0r-root-fence-durable-entries
  (implies (and (consp (fn-bs-ops-for-dir (fn-bs-pending b) :root))
                (not (consp (cdr (fn-bs-ops-for-dir (fn-bs-pending b) :root))))
                (equal (car (car (fn-bs-ops-for-dir (fn-bs-pending b) :root))) :set-entry)
                (equal (nth 2 (car (fn-bs-ops-for-dir (fn-bs-pending b) :root))) *fn-bs-scan-frontier-name*))
           (and (equal (fn-bs-durable-entry (fn-bs-fence-dir b :root) :root *fn-bs-scan-config-name*)
                       (fn-bs-durable-entry b :root *fn-bs-scan-config-name*))
                (equal (fn-bs-durable-entry (fn-bs-fence-dir b :root) :root *fn-bs-scan-frontier-name*)
                       (nth 3 (car (fn-bs-ops-for-dir (fn-bs-pending b) :root))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0r-single-set-entry-lookups (dirs (fn-bs-dirs b)) (r (fn-bs-ops-for-dir (fn-bs-pending b) :root)))
                 (:instance fn-bs-k0r-ops-for-dir-car-is-dir (ops (fn-bs-pending b)) (d :root)))
           :in-theory (e/d (fn-bs-fence-dir fn-bs-durable-entry fn-bs-apply-ops-dirs-are-apply-entries)
                           (fn-bs-apply-entries-entry-is-entry-after fn-bs-apply-ops fn-bs-apply-entries
                            fn-bs-entry-after fn-bs-k0r-ops-for-dir-car-is-dir)))))
(defthm fn-bs-k0r-root-fence-keeps-transactions
  (and (equal (assoc-equal :transactions (fn-bs-dirs (fn-bs-fence-dir b :root)))
              (assoc-equal :transactions (fn-bs-dirs b)))
       (equal (fn-bs-durable-names (fn-bs-fence-dir b :root) :transactions)
              (fn-bs-durable-names b :transactions)))
  :hints (("Goal" :use ((:instance fn-bs-fence-dir-touches-only-its-directory (s b) (dir :root) (other :transactions)))
           :in-theory (e/d (fn-bs-durable-names) (fn-bs-fence-dir-touches-only-its-directory fn-bs-fence-dir)))))
(defthm fn-bs-k0r-root-fence-keeps-durable-records
  (equal (fn-bs-durable-records (fn-bs-fence-dir b :root))
         (fn-bs-durable-records b))
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0r-root-fence-keeps-transactions
                 (:instance fn-bs-k0-same-transaction-dir-agreement
                  (u (fn-bs-unit (fn-bs-fence-dir b :root))) (i (fn-bs-inodes b))
                  (d1 (fn-bs-dirs (fn-bs-fence-dir b :root))) (d2 (fn-bs-dirs b))
                  (m (fn-bs-next-ino (fn-bs-fence-dir b :root))) (m2 (fn-bs-next-ino b))
                  (n 0) (count (len (fn-bs-durable-names b :transactions))))
                 (:instance fn-bs-read-records-under-agreement
                  (a (fn-bs-durable (fn-bs-fence-dir b :root)))
                  (b (fn-bs-make (fn-bs-unit (fn-bs-fence-dir b :root)) (fn-bs-inodes b) (fn-bs-dirs b)
                                 nil (fn-bs-next-ino b)))
                  (n 0) (count (len (fn-bs-durable-names b :transactions)))))
           :in-theory (e/d (fn-bs-durable-records fn-bs-durable)
                           (fn-bs-read-records fn-bs-txn-prefix-agreesp fn-bs-durable-names
                            fn-bs-read-records-under-agreement fn-bs-fence-dir fn-bs-k0r-root-fence-keeps-transactions)))))
(defthm fn-bs-k0r-root-fence-matches-phase
  (implies (not (fn-bs-ops-for-dir (fn-bs-pending b) :transactions))
           (fn-bs-pending-matches-phase (fn-bs-fence-dir b :root) ks))
  :hints (("Goal" :use ((:instance fn-bs-ops-for-dir-of-ops-not-for-dir (ops (fn-bs-pending b)) (dir :root))
                        (:instance fn-bs-k8-other-directory-ops-survive-filter (ops (fn-bs-pending b)) (removed :root) (kept :transactions)))
           :in-theory (e/d (fn-bs-pending-matches-phase fn-bs-pending-shape-okp fn-bs-fence-dir)
                                  (fn-bs-fencedp fn-bs-durable-records fn-bs-apply-ops fn-bs-ops-for-dir fn-bs-ops-not-for-dir
                                   fn-bs-ops-for-dir-of-ops-not-for-dir fn-bs-k8-other-directory-ops-survive-filter)))))
(defthm fn-bs-k0r-root-fence-authority-list
  (implies (and (not (fn-bs-ops-for-dir (fn-bs-pending b) :transactions))
                (consp (fn-bs-ops-for-dir (fn-bs-pending b) :root))
                (not (consp (cdr (fn-bs-ops-for-dir (fn-bs-pending b) :root))))
                (equal (car (car (fn-bs-ops-for-dir (fn-bs-pending b) :root))) :set-entry)
                (equal (nth 2 (car (fn-bs-ops-for-dir (fn-bs-pending b) :root))) *fn-bs-scan-frontier-name*))
           (let ((ino (nth 3 (car (fn-bs-ops-for-dir (fn-bs-pending b) :root)))))
             (and (equal (fn-bs-authority-inode-list (fn-bs-fence-dir b :root))
                         (list* (fn-bs-durable-entry b :root *fn-bs-scan-config-name*) ino
                                (strip-cdrs (cdr (assoc-equal :transactions (fn-bs-dirs b))))))
                  (equal (fn-bs-authority-inode-list b)
                         (list* (fn-bs-durable-entry b :root *fn-bs-scan-config-name*)
                                (fn-bs-durable-entry b :root *fn-bs-scan-frontier-name*)
                                (append (strip-cdrs (cdr (assoc-equal :transactions (fn-bs-dirs b))))
                                        (list ino)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0r-root-fence-durable-entries
                 (:instance fn-bs-k0r-single-root-target (ops (fn-bs-pending b))))
           :in-theory (e/d (fn-bs-authority-inode-list)
                           (fn-bs-fence-dir fn-bs-durable-entry)))
          (and stable-under-simplificationp '(:in-theory (e/d (fn-bs-authority-inode-list fn-bs-fence-dir) (fn-bs-durable-entry fn-bs-apply-ops))))))
(defthm fn-bs-k0s-root-fence-preserves-relation
  (implies (and (fn-bs-store-relation bs ks) (not (fn-bs-replay-visiblep ks)))
           (fn-bs-store-relation (fn-bs-fence-dir bs :root) ks))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((consp (fn-bs-ops-for-dir (fn-bs-pending bs) :root))))
          ("Subgoal 2" :use (fn-bs-store-relation-unfolds (:instance fn-bs-k0r-quiet-root-fence-is-identity (b bs)))
           :in-theory (e/d () (fn-bs-store-relation fn-bs-fence-dir fn-bs-statep fn-bs-k0r-quiet-root-fence-is-identity)))
          ("Subgoal 1" :use (fn-bs-store-relation-unfolds fn-bs-store-relation-window-unfolds
                             fn-bs-k0r-related-root-pending-facts
                             (:instance fn-bs-k0r-root-fence-durable-entries (b bs))
                             (:instance fn-bs-k0r-root-fence-authority-list (b bs))
                             (:instance fn-bs-k0r-root-fence-matches-phase (b bs))
                             (:instance fn-bs-fence-dir-preserves-statep (s bs) (dir :root)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-authority-fencedp fn-bs-authority-knownp
                            fn-sf-crash-imagep fn-bs-durable-frontier fn-bs-all-fencedp fn-bs-inode-list-knownp)
                           (fn-bs-durable fn-bs-durable-names fn-bs-statep fn-bs-fence-dir
                            fn-bs-durable-records fn-bs-durable-entry fn-bs-fencedp
                            fn-bs-durable-content fn-bs-authority-inode-list fn-bs-record-of
                            fn-bs-replay-matches-scan fn-sf-statep fn-bs-pending-matches-phase
                            fn-bs-contiguous-namesp fn-bs-replay-visiblep fn-bs-fence-dir-preserves-statep
                            fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep fn-bs-inop
                            )))))
