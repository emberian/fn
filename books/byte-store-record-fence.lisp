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

; A fence changes the durable directory, not the live name/content read.
; The next lemmas make that statement at the decoder's exact input range.
(defthm fn-bs-k8-directory-filter-keeps-inode-ops
  (equal (fn-bs-ops-for-ino (fn-bs-ops-not-for-dir ops dir) ino)
         (fn-bs-ops-for-ino ops ino))
  :hints (("Goal" :induct (fn-bs-ops-not-for-dir ops dir)
           :in-theory (enable fn-bs-ops-not-for-dir fn-bs-ops-for-ino))))

(defthm fn-bs-k8-fence-preserves-fencedp
  (equal (fn-bs-fencedp (fn-bs-fence-dir bs dir) ino)
         (fn-bs-fencedp bs ino))
  :hints (("Goal" :in-theory (enable fn-bs-fencedp))))

(defthm fn-bs-k8-name-absent-from-list-has-no-entry
  (implies (not (member-equal name (strip-cars alist)))
           (equal (assoc-equal name alist) nil))
  :hints (("Goal" :induct (assoc-equal name alist))))

(defthm fn-bs-k8-op-list-does-not-write-nil
  (implies (fn-bs-op-listp ops)
           (equal (fn-bs-ops-for-ino ops nil) nil))
  :hints (("Goal" :induct (fn-bs-ops-for-ino ops nil)
           :in-theory (enable fn-bs-op-listp fn-bs-opp fn-bs-ops-for-ino))))

(defthm fn-bs-k8-state-nil-inode-is-fenced
  (implies (fn-bs-statep bs) (fn-bs-fencedp bs nil))
  :hints (("Goal" :in-theory (enable fn-bs-statep fn-bs-fencedp))))

(defthm fn-bs-k8-related-view-transaction-lookup-is-fenced
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-namep name))
           (fn-bs-fencedp bs (fn-bs-lookup bs :transactions name)))
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-store-relation-implies-the-pending-shape
                 fn-bs-store-relation-fences-the-transaction-inodes
                 (:instance fn-bs-lookup-of-an-untouched-name
                            (s bs) (dir :transactions))
                 (:instance fn-bs-lookup-of-a-pending-target
                            (s bs) (dir :transactions))
                 (:instance fn-bs-ops-for-name-through-ops-for-dir
                            (ops (fn-bs-pending bs)) (dir :transactions))
                 (:instance fn-bs-all-fencedp-member
                            (bs bs) (inos (fn-bs-authority-inode-list bs))
                            (ino (fn-bs-lookup bs :transactions name))))
           :in-theory (enable fn-bs-authority-fencedp fn-bs-authority-inode-list
                              fn-bs-pending-shape-okp fn-bs-durable-entry
                              fn-bs-durable-names fn-bs-pending-entry-targets
                              fn-bs-dir-idp fn-bs-namep))))

(defthm fn-bs-k8-fence-durable-lookup-is-view
  (implies (and dir name)
           (equal (fn-bs-lookup (fn-bs-durable (fn-bs-fence-dir bs dir)) dir name)
                  (fn-bs-lookup (fn-bs-fence-dir bs dir) dir name)))
  :hints (("Goal"
           :use ((:instance fn-bs-lookup-of-an-untouched-name
                            (s (fn-bs-fence-dir bs dir)))
                 (:instance fn-bs-ops-for-name-through-ops-for-dir
                            (ops (fn-bs-pending (fn-bs-fence-dir bs dir))))
                 (:instance fn-bs-ops-for-dir-of-ops-not-for-dir
                            (ops (fn-bs-pending bs))))
           :in-theory (enable fn-bs-durable fn-bs-durable-entry
                              fn-bs-lookup fn-bs-view))))

(defthm fn-bs-k8-fence-durable-content-is-view-when-fenced
  (implies (fn-bs-fencedp bs ino)
           (equal (fn-bs-content (fn-bs-durable (fn-bs-fence-dir bs dir)) ino)
                  (fn-bs-content (fn-bs-fence-dir bs dir) ino)))
  :hints (("Goal"
           :use ((:instance fn-bs-content-of-a-fenced-inode
                            (s (fn-bs-fence-dir bs dir))))
           :in-theory (enable fn-bs-durable fn-bs-content fn-bs-view
                              fn-bs-durable-content))))

(defthm fn-bs-k8-fenced-durable-agrees-with-view
  (implies (and (fn-bs-store-relation bs ks) (natp n))
           (fn-bs-txn-prefix-agreesp
            (fn-bs-durable (fn-bs-fence-dir bs :transactions))
            (fn-bs-fence-dir bs :transactions) n
            (len (fn-bs-durable-names
                  (fn-bs-fence-dir bs :transactions) :transactions))))
  :rule-classes nil
  :hints (("Goal"
           :induct (fn-bs-txn-prefix-agreesp
                    (fn-bs-durable (fn-bs-fence-dir bs :transactions))
                    (fn-bs-fence-dir bs :transactions) n
                    (len (fn-bs-durable-names
                          (fn-bs-fence-dir bs :transactions) :transactions)))
           :in-theory (enable fn-bs-txn-prefix-agreesp))
          ("Subgoal *1/4"
           :use ((:instance fn-bs-k8-fence-durable-lookup-is-view
                            (bs bs) (dir :transactions) (name (fn-bs-txn-name n)))
                 (:instance fn-bs-txn-name-is-a-name (n n)))
           :in-theory (enable fn-bs-namep))
          ("Subgoal *1/3"
           :use ((:instance fn-bs-k8-fence-durable-content-is-view-when-fenced
                            (bs bs) (dir :transactions)
                            (ino (fn-bs-lookup (fn-bs-fence-dir bs :transactions)
                                                   :transactions (fn-bs-txn-name n))))
                 (:instance fn-bs-k8-related-view-transaction-lookup-is-fenced
                            (bs bs) (ks ks) (name (fn-bs-txn-name n)))
                 (:instance fn-bs-k8-fence-keeps-view-lookup
                            (bs bs) (dir :transactions) (name (fn-bs-txn-name n)))
                 (:instance fn-bs-txn-name-is-a-name (n n)))
           :in-theory (enable fn-bs-namep))))

(defthm fn-bs-k8-fenced-durable-records-are-pre-fence-view-read
  (implies (fn-bs-store-relation bs ks)
           (equal (fn-bs-durable-records (fn-bs-fence-dir bs :transactions))
                  (fn-bs-read-records bs 0
                                      (len (fn-bs-names bs :transactions)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 (:instance fn-bs-k8-fenced-durable-agrees-with-view (n 0))
                 (:instance fn-bs-read-records-under-agreement
                            (a (fn-bs-durable (fn-bs-fence-dir bs :transactions)))
                            (b (fn-bs-fence-dir bs :transactions)) (n 0)
                            (count (len (fn-bs-durable-names
                                         (fn-bs-fence-dir bs :transactions)
                                         :transactions))))
                 fn-bs-k8-fence-materializes-names)
           :in-theory (enable fn-bs-durable-records))))

; At an issued P-RECORD link the candidate's framed octets have already
; passed fsync(file).  The relation binds that exact decoder result to the
; kernel candidate; the fence therefore makes the *record*, not merely its
; pathname, durable.  The issued-link premise matters: phase alone does not
; say that the physical link operation took place (see the negative fixture).
(defthm fn-bs-k8-record-of-durable-is-durable-content
  (equal (fn-bs-record-of (fn-bs-durable bs) ino)
         (fn-bs-record-of-octets (fn-bs-durable-content bs ino)))
  :hints (("Goal" :in-theory (enable fn-bs-record-of fn-bs-durable
                                    fn-bs-content fn-bs-view
                                    fn-bs-durable-content))))

(defthm fn-bs-k8-pending-link-view-record-is-candidate
  (implies (and (fn-bs-store-relation bs ks)
                (equal (fn-sf-phase ks) :record-attempted)
                (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))
           (equal (fn-bs-record-of
                   bs (fn-bs-lookup
                       bs :transactions
                       (fn-bs-txn-name
                        (len (fn-bs-durable-names bs :transactions)))))
                  (fn-sf-record-candidate ks)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-window-unfolds
                 fn-bs-pending-matches-phase-unfolds
                 fn-bs-store-relation-implies-the-pending-shape
                 fn-bs-shape-at-the-pending-link-name
                 (:instance fn-bs-lookup-of-a-pending-target
                            (s bs) (dir :transactions)
                            (name (fn-bs-txn-name
                                   (len (fn-bs-durable-names bs :transactions)))))
                 (:instance fn-bs-content-of-a-fenced-inode
                            (s bs)
                            (ino (nth 3 (car (fn-bs-ops-for-dir
                                              (fn-bs-pending bs) :transactions))))))
           :in-theory (enable fn-bs-replay-visiblep fn-bs-pending-shape-okp
                              fn-bs-record-of))))

(defthm fn-bs-k8-one-record-read
  (implies (and (natp n)
                (fn-bs-inop (fn-bs-lookup s :transactions (fn-bs-txn-name n)))
                (fn-store-event-p
                 (fn-bs-record-of s
                                  (fn-bs-lookup s :transactions
                                                (fn-bs-txn-name n))))
                (equal (fn-store-event-sequence
                        (fn-bs-record-of s
                                         (fn-bs-lookup s :transactions
                                                       (fn-bs-txn-name n))))
                       n))
           (equal (fn-bs-read-records s n (1+ n))
                  (list (fn-bs-record-of
                         s (fn-bs-lookup s :transactions
                                         (fn-bs-txn-name n))))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-bs-read-records s n (1+ n))
                           (fn-bs-read-records s (1+ n) (1+ n))))))

(defthm fn-bs-k8-pending-link-view-read-is-one-candidate
  (implies (and (fn-bs-store-relation bs ks)
                (equal (fn-sf-phase ks) :record-attempted)
                (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))
           (equal (fn-bs-read-records
                   bs (len (fn-bs-durable-names bs :transactions))
                   (1+ (len (fn-bs-durable-names bs :transactions))))
                  (list (fn-sf-record-candidate ks))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-k8-pending-link-view-record-is-candidate
                 fn-bs-store-relation-unfolds
                 fn-bs-store-relation-window-unfolds
                 fn-bs-pending-matches-phase-unfolds
                 fn-bs-store-relation-implies-the-pending-shape
                 fn-bs-kernel-candidates-are-typed
                 fn-bs-durable-records-length
                 fn-bs-shape-at-the-pending-link-name
                 (:instance fn-bs-k8-one-record-read
                            (s bs) (n (len (fn-bs-durable-names bs :transactions))))
                 (:instance fn-bs-lookup-of-a-pending-target
                            (s bs) (dir :transactions)
                            (name (fn-bs-txn-name
                                   (len (fn-bs-durable-names bs :transactions)))))
                 (:instance fn-bs-ops-for-name-through-ops-for-dir
                            (ops (fn-bs-pending bs)) (dir :transactions)
                            (name (fn-bs-txn-name
                                   (len (fn-bs-durable-names bs :transactions))))))
           :in-theory (enable fn-bs-pending-shape-okp fn-bs-replay-visiblep))))

(defthm fn-bs-k8-pending-link-view-record-list
  (implies (and (fn-bs-store-relation bs ks)
                (equal (fn-sf-phase ks) :record-attempted)
                (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))
           (equal (fn-bs-read-records
                   bs 0 (len (fn-bs-names bs :transactions)))
                  (append (fn-bs-durable-records bs)
                          (list (fn-sf-record-candidate ks)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-view-reads-the-durable-records
                 fn-bs-store-relation-view-namespace-with-a-pending-link
                 fn-bs-k8-pending-link-view-read-is-one-candidate
                 fn-bs-store-relation-unfolds
                 (:instance fn-bs-txn-names-length
                            (n (1+ (len (fn-bs-durable-names bs :transactions)))))
                 (:instance fn-bs-read-records-of-one-more
                            (s bs) (n 0)
                            (count (len (fn-bs-durable-names bs :transactions)))))
           :in-theory (disable fn-bs-read-records fn-bs-durable-records
                               fn-bs-names fn-bs-txn-names))))

(defthm fn-bs-k8-pending-link-fence-durable-records
  (implies (and (fn-bs-store-relation bs ks)
                (equal (fn-sf-phase ks) :record-attempted)
                (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))
           (equal (fn-bs-durable-records
                   (fn-bs-fence-dir bs :transactions))
                  (append (fn-bs-durable-records bs)
                          (list (fn-sf-record-candidate ks)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-k8-fenced-durable-records-are-pre-fence-view-read
                 fn-bs-k8-pending-link-view-record-list)
           :in-theory (disable fn-bs-read-records fn-bs-durable-records
                               fn-bs-fence-dir))))
