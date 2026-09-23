; The transaction directory fence is a real byte-state transition.  These
; projections are preparation for K8: they do not, by themselves, establish
; that the related candidate is the newly durable record.
(in-package "ACL2")
(include-book "byte-store-stable-prefix")

(defthm fn-bs-k8-other-directory-ops-survive-filter
  (implies (not (equal kept removed))
           (equal (fn-bs-ops-for-dir (fn-bs-ops-not-for-dir ops removed) kept)
                  (fn-bs-ops-for-dir ops kept)))
  :hints (("Goal" :induct (fn-bs-ops-not-for-dir ops removed)
           :in-theory (enable fn-bs-ops-for-dir fn-bs-ops-not-for-dir))))

(defthm fn-bs-k8-fence-pending-is-filtered
  (equal (fn-bs-pending (fn-bs-fence-dir bs dir))
         (fn-bs-ops-not-for-dir (fn-bs-pending bs) dir))
  :hints (("Goal" :in-theory (enable fn-bs-fence-dir))))

(defthm fn-bs-k8-fence-keeps-root-pending-ops
  (equal (fn-bs-ops-for-dir (fn-bs-pending (fn-bs-fence-dir bs :transactions))
                            :root)
         (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
  :hints (("Goal" :in-theory (enable fn-bs-fence-dir))))

(defthm fn-bs-k8-fence-keeps-root-authority
  (and (equal (fn-bs-durable-entry (fn-bs-fence-dir bs :transactions) :root name)
              (fn-bs-durable-entry bs :root name))
       (equal (fn-bs-durable-content (fn-bs-fence-dir bs :transactions) ino)
              (fn-bs-durable-content bs ino)))
  :hints (("Goal" :use ((:instance fn-bs-fence-dir-touches-only-its-directory
                                   (s bs) (dir :transactions) (other :root)))
           :in-theory (enable fn-bs-durable-content fn-bs-durable-entry))))

(defthm fn-bs-k8-fence-keeps-durable-frontier
  (equal (fn-bs-durable-frontier (fn-bs-fence-dir bs :transactions))
         (fn-bs-durable-frontier bs))
  :hints (("Goal" :use ((:instance fn-bs-fence-dir-touches-only-its-directory
                                   (s bs) (dir :transactions) (other :root)))
           :in-theory (enable fn-bs-durable-frontier fn-bs-durable-content
                              fn-bs-durable-entry))))

(defthm fn-bs-k8-fence-materializes-names
  (implies (fn-bs-statep bs)
           (equal (fn-bs-durable-names (fn-bs-fence-dir bs :transactions)
                                       :transactions)
                  (fn-bs-names bs :transactions)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bs-names-is-names-after-the-pending-list
                            (s bs) (dir :transactions))
                 (:instance fn-bs-apply-entries-names-is-names-after
                            (dirs (fn-bs-dirs bs))
                            (ops (fn-bs-ops-for-dir (fn-bs-pending bs)
                                                    :transactions))
                            (dir :transactions))
                 (:instance fn-bs-names-after-through-ops-for-dir
                            (ops (fn-bs-pending bs))
                            (old (fn-bs-durable-names bs :transactions))
                            (dir :transactions))
                 (:instance fn-bs-op-listp-of-ops-for-dir
                            (ops (fn-bs-pending bs)) (dir :transactions))
                 (:instance fn-bs-apply-ops-dirs-are-apply-entries
                            (inodes (fn-bs-inodes bs)) (dirs (fn-bs-dirs bs))
                            (ops (fn-bs-ops-for-dir (fn-bs-pending bs)
                                                    :transactions))))
           :in-theory (enable fn-bs-statep fn-bs-fence-dir fn-bs-durable-names))))

(defthm fn-bs-k8-entry-after-through-directory-ops
  (equal (fn-bs-entry-after (fn-bs-ops-for-dir ops dir) old dir name)
         (fn-bs-entry-after ops old dir name))
  :hints (("Goal" :induct (fn-bs-entry-after ops old dir name)
           :in-theory (enable fn-bs-entry-after fn-bs-ops-for-dir))))

(defthm fn-bs-k8-fence-materializes-entry
  (implies (and dir name)
           (equal (fn-bs-durable-entry (fn-bs-fence-dir bs dir) dir name)
                  (fn-bs-lookup bs dir name)))
  :hints (("Goal"
           :use ((:instance fn-bs-apply-ops-dirs-are-apply-entries
                            (inodes (fn-bs-inodes bs)) (dirs (fn-bs-dirs bs))
                            (ops (fn-bs-ops-for-dir (fn-bs-pending bs) dir)))
                 (:instance fn-bs-apply-ops-dirs-are-apply-entries
                            (inodes (fn-bs-inodes bs)) (dirs (fn-bs-dirs bs))
                            (ops (fn-bs-pending bs)))
                 (:instance fn-bs-apply-entries-entry-is-entry-after
                            (dirs (fn-bs-dirs bs))
                            (ops (fn-bs-ops-for-dir (fn-bs-pending bs) dir)))
                 (:instance fn-bs-apply-entries-entry-is-entry-after
                            (dirs (fn-bs-dirs bs)) (ops (fn-bs-pending bs)))
                 (:instance fn-bs-k8-entry-after-through-directory-ops
                            (ops (fn-bs-pending bs))
                            (old (fn-bs-durable-entry bs dir name))))
           :in-theory (enable fn-bs-fence-dir fn-bs-durable-entry
                              fn-bs-lookup fn-bs-view))))

(defthm fn-bs-k8-directory-filter-keeps-inode-writes
  (equal (fn-bs-apply-writes inodes (fn-bs-ops-not-for-dir ops dir))
         (fn-bs-apply-writes inodes ops))
  :hints (("Goal" :induct (fn-bs-apply-writes inodes ops)
           :in-theory (enable fn-bs-apply-writes fn-bs-ops-not-for-dir))))

(defthm fn-bs-k8-fence-keeps-view-content
  (equal (fn-bs-content (fn-bs-fence-dir bs dir) ino)
         (fn-bs-content bs ino))
  :hints (("Goal"
           :use ((:instance fn-bs-apply-ops-inodes-are-apply-writes
                            (inodes (fn-bs-inodes bs)) (dirs (fn-bs-dirs bs))
                            (ops (fn-bs-pending bs)))
                 (:instance fn-bs-apply-ops-inodes-are-apply-writes
                            (inodes (fn-bs-inodes (fn-bs-fence-dir bs dir)))
                            (dirs (fn-bs-dirs (fn-bs-fence-dir bs dir)))
                            (ops (fn-bs-pending (fn-bs-fence-dir bs dir)))))
           :in-theory (enable fn-bs-content fn-bs-view))))

(defthm fn-bs-k8-fence-keeps-view-lookup
  (implies (and dir name)
           (equal (fn-bs-lookup (fn-bs-fence-dir bs dir) dir name)
                  (fn-bs-lookup bs dir name)))
  :hints (("Goal"
           :use ((:instance fn-bs-lookup-of-an-untouched-name
                            (s (fn-bs-fence-dir bs dir)))
                 (:instance fn-bs-ops-for-name-through-ops-for-dir
                            (ops (fn-bs-pending (fn-bs-fence-dir bs dir))))
                 (:instance fn-bs-ops-for-dir-of-ops-not-for-dir
                            (ops (fn-bs-pending bs))))
           :in-theory (disable fn-bs-lookup-of-an-untouched-name))))

(defthm fn-bs-k8-fence-agrees-on-transaction-read
  (fn-bs-txn-prefix-agreesp (fn-bs-fence-dir bs :transactions) bs n count)
  :hints (("Goal"
           :induct (fn-bs-txn-prefix-agreesp
                    (fn-bs-fence-dir bs :transactions) bs n count)
           :in-theory (enable fn-bs-txn-prefix-agreesp))
          ("Subgoal *1/4"
           :use ((:instance fn-bs-k8-fence-keeps-view-lookup
                            (dir :transactions) (name (fn-bs-txn-name n)))
                 (:instance fn-bs-txn-name-is-a-name (n n)))
           :in-theory (enable fn-bs-namep))))

(defthm fn-bs-k8-fence-keeps-transaction-read
  (equal (fn-bs-read-records (fn-bs-fence-dir bs :transactions) n count)
         (fn-bs-read-records bs n count))
  :hints (("Goal"
           :use ((:instance fn-bs-read-records-under-agreement
                            (a (fn-bs-fence-dir bs :transactions)) (b bs)))
           :in-theory (disable fn-bs-read-records))))
