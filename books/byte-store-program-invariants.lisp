; K0 continuation: phase and allocation separation for arbitrary related
; stores, including retained transaction histories.  No empty-history premise.
(in-package "ACL2")
(include-book "byte-store-relation")

(defthm fn-bs-known-inode-list-member-is-known
  (implies (and (fn-bs-inode-list-knownp bs inos) (member-equal ino inos))
           (consp (assoc-equal ino (fn-bs-inodes bs))))
  :hints (("Goal" :in-theory (enable fn-bs-inode-list-knownp))))

(defthm fn-bs-related-allocation-is-fresh
  (implies (fn-bs-store-relation bs ks)
           (not (member-equal (fn-bs-next-ino bs) (fn-bs-authority-inode-list bs))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bs-known-inode-list-member-is-known
                           (ino (fn-bs-next-ino bs))
                           (inos (fn-bs-authority-inode-list bs)))
                 (:instance fn-bs-keys-belowp-excludes-bound
                            (x (fn-bs-inodes bs)) (n (fn-bs-next-ino bs))))
           :in-theory (e/d (fn-bs-store-relation fn-bs-authority-knownp fn-bs-statep)
                           (fn-bs-authority-inode-list fn-bs-inode-list-knownp)))))

(defthm fn-bs-ready-relation-authority-is-quiet
  (implies (and (fn-bs-store-relation bs ks)
                (equal (fn-sf-phase ks) :ready))
           (and (equal (fn-bs-ops-for-dir (fn-bs-pending bs) :root) nil)
                (equal (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions) nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bs-store-relation
                                    fn-bs-replay-visiblep fn-bs-pending-matches-phase
                                    fn-sf-frontier-new-visiblep
                                    fn-sf-record-present-visiblep)
                                   (fn-bs-statep fn-sf-statep fn-bs-ops-for-dir)))))

(defthm fn-bs-start-frontier-preserves-relation
  (implies (fn-bs-store-relation bs ks)
           (fn-bs-store-relation bs (fn-sf-start-frontier ks)))
  :rule-classes nil
  :hints (("Goal"
           :cases ((equal (fn-sf-phase ks) :ready))
           :use (fn-bs-ready-relation-authority-is-quiet
                 (:instance fn-sf-start-frontier-preserves-state (s ks)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-pending-matches-phase
                             fn-bs-replay-visiblep fn-sf-crash-imagep
                             fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                             fn-sf-start-frontier)
                            (fn-bs-statep fn-sf-statep fn-bs-pending-shape-okp
                             fn-bs-authority-fencedp fn-bs-authority-knownp
                             fn-bs-ops-for-dir)))))


(defthm fn-bs-frontier-file-result-preserves-relation
  (implies (fn-bs-store-relation bs ks)
           (fn-bs-store-relation bs (fn-sf-frontier-file-result ks result)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-sf-frontier-file-result-preserves-state (s ks)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-pending-matches-phase
                             fn-bs-replay-visiblep fn-sf-crash-imagep
                             fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                             fn-sf-frontier-file-result)
                            (fn-bs-statep fn-sf-statep fn-bs-pending-shape-okp
                             fn-bs-authority-fencedp fn-bs-authority-knownp
                             fn-bs-ops-for-dir)))))

(defthm fn-bs-frontier-replace-result-preserves-relation
  (implies (fn-bs-store-relation bs ks)
           (fn-bs-store-relation bs (fn-sf-frontier-replace-result ks result)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-sf-frontier-replace-result-preserves-state (s ks)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-pending-matches-phase
                             fn-bs-replay-visiblep fn-sf-crash-imagep
                             fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                             fn-sf-frontier-replace-result)
                            (fn-bs-statep fn-sf-statep fn-bs-pending-shape-okp
                             fn-bs-authority-fencedp fn-bs-authority-knownp
                             fn-bs-ops-for-dir)))))

(defthm fn-bs-frontier-dir-error-preserves-relation
  (implies (fn-bs-store-relation bs ks)
           (fn-bs-store-relation bs (fn-sf-frontier-dir-result ks :error)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-sf-frontier-dir-result-preserves-state (s ks)
                           (result :error)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-pending-matches-phase
                             fn-bs-replay-visiblep fn-sf-crash-imagep
                             fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                             fn-sf-frontier-dir-result)
                            (fn-bs-statep fn-sf-statep fn-bs-pending-shape-okp
                             fn-bs-authority-fencedp fn-bs-authority-knownp
                             fn-bs-ops-for-dir)))))

; These observations do not claim the directory commit.  In particular,
; :known-fail releases a staging attempt and :error fences a possibly issued
; rename.  The successful :frontier-dir observation is deliberately absent:
; its byte fence must first discharge the candidate-durable obligation.
(defun fn-bs-frontier-noncommit-observationp (event)
  (declare (xargs :guard t :verify-guards nil))
  (member-equal event
                '((:start-frontier) (:frontier-file :ok)
                  (:frontier-file :known-fail) (:frontier-replace :ok)
                  (:frontier-replace :error) (:frontier-dir :error))))

(defthm fn-bs-frontier-noncommit-observation-preserves-relation
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-noncommit-observationp event))
           (fn-bs-store-relation
            (mv-nth 1 (fn-bs-step bs ks (list :observe event) outcome groups capacity))
            (mv-nth 2 (fn-bs-step bs ks (list :observe event) outcome groups capacity))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-start-frontier-preserves-relation
                 (:instance fn-bs-frontier-file-result-preserves-relation (result :ok))
                 (:instance fn-bs-frontier-file-result-preserves-relation
                            (result :known-fail))
                 (:instance fn-bs-frontier-replace-result-preserves-relation (result :ok))
                 (:instance fn-bs-frontier-replace-result-preserves-relation (result :error))
                 fn-bs-frontier-dir-error-preserves-relation)
           :in-theory (e/d (fn-bs-step fn-sf-dispatch)
                            (fn-bs-store-relation fn-sf-start-frontier
                             fn-sf-frontier-file-result fn-sf-frontier-replace-result
                             fn-sf-frontier-dir-result)))))

(defun fn-bs-frontier-directory-committedp (bs ks)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bs-dir-quietp bs :root)
       (equal (fn-bs-durable-frontier bs) (fn-sf-frontier-candidate ks))))

(defthm fn-bs-frontier-directory-commit-observation-preserves-relation
  (implies (and (fn-bs-store-relation bs ks)
                (equal (fn-sf-phase ks) :frontier-attempted)
                (fn-bs-frontier-directory-committedp bs ks))
           (and (fn-bs-store-relation bs (fn-sf-frontier-dir-result ks :ok))
                (equal (fn-sf-phase (fn-sf-frontier-dir-result ks :ok)) :reserved)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-sf-frontier-dir-result-preserves-state
                           (s ks) (result :ok)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-pending-matches-phase
                             fn-bs-replay-visiblep fn-bs-dir-quietp fn-sf-crash-imagep
                             fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                             fn-sf-frontier-dir-result)
                            (fn-bs-statep fn-sf-statep fn-bs-pending-shape-okp
                             fn-bs-authority-fencedp fn-bs-authority-knownp
                             fn-bs-ops-for-dir)))))

; Named correspondence from the interpreted program step to the keystone's
; kernel subject.  This is a by-definition bridge, not a registry event.
(defthm fn-bs-frontier-directory-step-is-kernel-observation-by-definition
  (equal (fn-bs-step bs ks '(:observe (:frontier-dir :ok)) outcome groups capacity)
         (list :ok bs (fn-sf-frontier-dir-result ks :ok)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bs-step fn-sf-dispatch)
                                   (fn-sf-frontier-dir-result)))))

; The fresh inode is separate from every transaction pathname, not only the
; configuration/frontier pair. This is the retained-history side of staging
; isolation; it does not iterate through or revalidate records on a served path.
(defthm fn-bs-related-allocation-is-not-a-transaction-target
  (implies (fn-bs-store-relation bs ks)
           (not (equal (fn-bs-next-ino bs)
                       (fn-bs-durable-entry bs :transactions name))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-related-allocation-is-fresh
                 (:instance fn-bs-assoc-value-is-in-strip-cdrs
                            (k name)
                            (alist (cdr (assoc-equal :transactions (fn-bs-dirs bs))))))
           :in-theory (e/d (fn-bs-store-relation fn-bs-statep
                             fn-bs-authority-inode-list fn-bs-durable-entry
                             fn-bs-member-of-append)
                            (fn-bs-inode-list-knownp fn-bs-authority-knownp
                             fn-bs-authority-fencedp)))))
