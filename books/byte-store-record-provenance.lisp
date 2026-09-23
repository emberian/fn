; K6: the actual P-RECORD program must publish exactly the whole frame it
; wrote and fenced, not merely a record with matching decoded fields.
(in-package "ACL2")
(include-book "byte-store-relation")

(local (defthm fn-bs-k6-take-all
         (implies (true-listp xs)
                  (equal (fn-bs-take (len xs) xs) xs))
         :hints (("Goal" :induct (fn-bs-take (len xs) xs)
                  :in-theory (enable fn-bs-take)))))
(local (defthm fn-bs-k6-splice-empty-file
         (implies (true-listp octets)
                  (equal (fn-bs-splice nil 0 octets) octets))
         :hints (("Goal" :in-theory (e/d (fn-bs-splice) (fn-bs-take))))))
(local (defthm fn-bs-k6-empty-true-list
         (implies (true-listp xs)
                  (equal (equal (len xs) 0) (equal xs nil)))))

; A successful write to a previously empty, allocated inode is the exact
; supplied octet list after fsync(fd).  This is about the raw bytes, before
; any record decoder or kernel-level membership argument.
(defthm fn-bs-k6-write-then-fence-keeps-exact-octets
  (implies (and (fn-bs-statep bs)
                (fn-bs-inop ino)
                (assoc-equal ino (fn-bs-inodes bs))
                (fn-bs-fencedp bs ino)
                (equal (fn-bs-durable-content bs ino) nil)
                (true-listp octets))
           (equal (fn-bs-durable-content
                   (fn-bs-fence-file
                    (mv-nth 1 (fn-bs-write bs ino 0 octets :ok)) ino)
                   ino)
                  octets))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k6-take-all (xs octets))
                 (:instance fn-bs-k6-splice-empty-file (octets octets))
                 (:instance fn-bs-ops-for-ino-of-append
                            (a (fn-bs-pending bs))
                            (b (list (list :write ino 0 octets))))
                 (:instance fn-bs-assoc-of-put-assoc-same
                            (k ino) (v octets) (a (fn-bs-inodes bs))))
           :in-theory (e/d (fn-bs-write fn-bs-fence-file
                             fn-bs-durable-content fn-bs-fencedp
                             fn-bs-ops-for-ino fn-bs-apply-ops fn-bs-apply-op)
                           (fn-bs-splice fn-bs-take fn-bs-statep
                            fn-cbor-octet-listp)))))

(local
 (defthm fn-bs-k6-unknown-inode-has-no-pending-write
   (implies (and (fn-bs-writes-knownp ops inodes)
                 (not (assoc-equal ino inodes)))
            (equal (fn-bs-ops-for-ino ops ino) nil))
   :rule-classes nil
   :hints (("Goal" :induct (fn-bs-ops-for-ino ops ino)
            :in-theory (enable fn-bs-writes-knownp fn-bs-ops-for-ino)))))
(local
 (defthm fn-bs-k6-state-next-ino-is-fenced
   (implies (fn-bs-statep bs)
            (and (not (assoc-equal (fn-bs-next-ino bs)
                                   (fn-bs-inodes bs)))
                  (fn-bs-fencedp bs (fn-bs-next-ino bs))))
   :hints (("Goal"
            :use ((:instance fn-bs-keys-belowp-excludes-bound
                             (x (fn-bs-inodes bs))
                             (n (fn-bs-next-ino bs)))
                  (:instance fn-bs-k6-unknown-inode-has-no-pending-write
                             (ops (fn-bs-pending bs))
                             (inodes (fn-bs-inodes bs))
                             (ino (fn-bs-next-ino bs))))
            :in-theory (enable fn-bs-statep fn-bs-fencedp)))))

(defthm fn-bs-k6-create-fresh-inode-is-empty-and-fenced
  (implies (and (fn-bs-statep bs)
                (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage)))
           (let* ((ino (fn-bs-next-ino bs))
                  (created (mv-nth 1 (fn-bs-create bs :staging stage :ok))))
             (and (fn-bs-statep created)
                  (assoc-equal ino (fn-bs-inodes created))
                  (equal (fn-bs-durable-content created ino) nil)
                  (fn-bs-fencedp created ino))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bs-k6-state-next-ino-is-fenced)
                 (:instance fn-bs-create-preserves-statep
                            (s bs) (dir :staging) (name stage)
                            (outcome :ok))
                 (:instance fn-bs-ops-for-ino-of-append
                            (a (fn-bs-pending bs))
                            (b (list (list :set-entry :staging stage
                                           (fn-bs-next-ino bs))))
                            (ino (fn-bs-next-ino bs))))
           :in-theory (enable fn-bs-create fn-bs-durable-content
                              fn-bs-fencedp))))

(defthm fn-bs-k6-create-write-fence-exact-frame
  (implies (and (fn-bs-statep bs)
                (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage))
                (true-listp frame))
           (let* ((ino (fn-bs-next-ino bs))
                  (created (mv-nth 1 (fn-bs-create bs :staging stage :ok)))
                  (written (mv-nth 1 (fn-bs-write created ino 0 frame :ok)))
                  (fenced (fn-bs-fence-file written ino)))
             (equal (fn-bs-durable-content fenced ino) frame)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k6-create-fresh-inode-is-empty-and-fenced)
                 (:instance fn-bs-k6-write-then-fence-keeps-exact-octets
                            (bs (mv-nth 1
                                  (fn-bs-create bs :staging stage :ok)))
                            (ino (fn-bs-next-ino bs))
                            (octets frame)))
           :in-theory (e/d (fn-bs-statep)
                           (fn-bs-create fn-bs-write fn-bs-fence-file
                            fn-bs-durable-content true-listp)))))

(local
 (defthm fn-bs-k6-fresh-create-returns-ok
   (implies (not (fn-bs-lookup bs :staging stage))
            (equal (mv-nth 0 (fn-bs-create bs :staging stage :ok)) :ok))
   :hints (("Goal" :in-theory (enable fn-bs-create)))))
(local
 (defthm fn-bs-k6-entry-after-last-set
   (implies (and dir name)
            (equal (fn-bs-entry-after
                    (append ops (list (list :set-entry dir name ino)))
                    old dir name)
                   ino))
   :hints (("Goal"
            :use ((:instance fn-bs-entry-after-of-append
                             (a ops)
                             (b (list (list :set-entry dir name ino)))))
            :in-theory (e/d (fn-bs-entry-after)
                            (fn-bs-entry-after-of-append))))))
(local
 (defthm fn-bs-k6-lookup-after-pending-set
   (implies (and dir name)
            (equal (fn-bs-lookup
                    (fn-bs-make unit inodes dirs
                                (append pending
                                        (list (list :set-entry dir name ino)))
                                next)
                    dir name)
                   ino))
   :hints (("Goal"
            :use ((:instance fn-bs-apply-entries-entry-is-entry-after
                             (dirs dirs)
                             (ops (append pending
                                          (list (list :set-entry dir name ino))))))
            :in-theory (e/d (fn-bs-lookup fn-bs-view
                             fn-bs-apply-ops-dirs-are-apply-entries)
                            (fn-bs-apply-ops fn-bs-apply-entries
                             fn-bs-entry-after))))))
(local
 (defthm fn-bs-k6-created-stage-lookup
   (implies (and (fn-bs-statep bs)
                 (fn-bs-namep stage)
                 (not (fn-bs-lookup bs :staging stage)))
            (equal (fn-bs-lookup
                    (mv-nth 1 (fn-bs-create bs :staging stage :ok))
                    :staging stage)
                   (fn-bs-next-ino bs)))
   :hints (("Goal" :in-theory (e/d (fn-bs-create)
                                   (fn-bs-statep fn-bs-lookup))))))
(local
 (defthm fn-bs-k6-write-created-inode-returns-ok
   (implies (and (fn-bs-statep bs)
                 (fn-bs-namep stage)
                 (not (fn-bs-lookup bs :staging stage)))
            (equal (mv-nth 0
                            (fn-bs-write
                             (mv-nth 1
                                     (fn-bs-create bs :staging stage :ok))
                             (fn-bs-next-ino bs) 0 frame :ok))
                   :ok))
   :hints (("Goal"
            :use ((:instance
                   fn-bs-k6-create-fresh-inode-is-empty-and-fenced))
            :in-theory (e/d (fn-bs-write) (fn-bs-create))))))
(local
 (defthm fn-bs-k6-write-keeps-lookup
   (equal (fn-bs-lookup
           (mv-nth 1 (fn-bs-write bs ino offset octets :ok)) dir name)
          (fn-bs-lookup bs dir name))
   :hints (("Goal"
            :in-theory (e/d (fn-bs-write fn-bs-lookup fn-bs-view
                             fn-bs-apply-ops-dirs-are-apply-entries
                             fn-bs-apply-entries-of-append
                             fn-bs-apply-entries)
                            (fn-bs-apply-ops fn-bs-take))))))

; This equality follows the actual interpreter and its stop-on-error rule.
; A nil outcomes list means successful syscall returns.  The sixth pair is
; after P-RECORD's successful file fence and kernel observation.
(defthm fn-bs-k6-interpreted-record-fence-is-write-fence
  (implies (and (fn-bs-statep bs)
                (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage))
                (true-listp frame))
           (equal
            (car (nth 5 (fn-bs-run bs ks
                                   (fn-bs-record-program stage name frame)
                                   nil groups capacity)))
            (let* ((ino (fn-bs-next-ino bs))
                   (created
                    (mv-nth 1 (fn-bs-create bs :staging stage :ok)))
                   (written
                    (mv-nth 1 (fn-bs-write created ino 0 frame :ok))))
              (fn-bs-fence-file written ino))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-record-program fn-bs-run fn-bs-step
                             fn-bs-fsync-file)
                           (fn-bs-statep fn-bs-create fn-bs-write
                            fn-bs-fence-file fn-bs-lookup fn-bs-namep
                            fn-bs-durable-content)))))

(defthm fn-bs-k6-typed-stage-record-file-cut-has-exact-frame
  (implies (and (fn-bs-statep bs)
                (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage))
                (true-listp frame))
           (equal
            (fn-bs-durable-content
             (car (nth 5 (fn-bs-run bs ks
                                    (fn-bs-record-program stage name frame)
                                    nil groups capacity)))
             (fn-bs-next-ino bs))
            frame))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bs-k6-interpreted-record-fence-is-write-fence)
                 (:instance fn-bs-k6-create-write-fence-exact-frame))
           :in-theory (disable fn-bs-run fn-bs-record-program
                               fn-bs-durable-content fn-bs-create
                               fn-bs-write fn-bs-fence-file))))

; The raw byte conclusion does not depend on stage name grammar.  In
; particular a NIL name works in the byte interpreter.  The grammar guard
; belongs to fn-bs-record-inputp at the host boundary, not to this theorem.
(local
 (defthm fn-bs-k6-write-then-fence-without-statep
   (implies (and (fn-bs-inop ino)
                 (assoc-equal ino (fn-bs-inodes bs))
                 (fn-bs-fencedp bs ino)
                 (equal (fn-bs-durable-content bs ino) nil)
                 (true-listp octets))
            (equal (fn-bs-durable-content
                    (fn-bs-fence-file
                     (mv-nth 1 (fn-bs-write bs ino 0 octets :ok)) ino)
                    ino)
                   octets))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-k6-take-all (xs octets))
                  (:instance fn-bs-k6-splice-empty-file (octets octets))
                  (:instance fn-bs-ops-for-ino-of-append
                             (a (fn-bs-pending bs))
                             (b (list (list :write ino 0 octets))))
                  (:instance fn-bs-assoc-of-put-assoc-same
                             (k ino) (v octets) (a (fn-bs-inodes bs))))
            :in-theory (e/d (fn-bs-write fn-bs-fence-file
                              fn-bs-durable-content fn-bs-fencedp
                              fn-bs-ops-for-ino fn-bs-apply-ops fn-bs-apply-op)
                            (fn-bs-splice fn-bs-take fn-bs-statep
                             fn-cbor-octet-listp))))))
(local
 (defthm fn-bs-k6-create-fresh-inode-without-namep
   (implies (and (fn-bs-statep bs)
                 (not (fn-bs-lookup bs :staging stage)))
            (let* ((ino (fn-bs-next-ino bs))
                   (created
                    (mv-nth 1 (fn-bs-create bs :staging stage :ok))))
              (and (assoc-equal ino (fn-bs-inodes created))
                   (equal (fn-bs-durable-content created ino) nil)
                   (fn-bs-fencedp created ino))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance fn-bs-k6-state-next-ino-is-fenced)
                  (:instance fn-bs-ops-for-ino-of-append
                             (a (fn-bs-pending bs))
                             (b (list (list :set-entry :staging stage
                                            (fn-bs-next-ino bs))))
                             (ino (fn-bs-next-ino bs))))
            :in-theory (enable fn-bs-create fn-bs-durable-content
                               fn-bs-fencedp)))))
(local
 (defthm fn-bs-k6-create-write-fence-without-namep
   (implies (and (fn-bs-statep bs)
                 (not (fn-bs-lookup bs :staging stage))
                 (true-listp frame))
            (let* ((ino (fn-bs-next-ino bs))
                   (created
                    (mv-nth 1 (fn-bs-create bs :staging stage :ok)))
                   (written
                    (mv-nth 1 (fn-bs-write created ino 0 frame :ok)))
                   (fenced (fn-bs-fence-file written ino)))
              (equal (fn-bs-durable-content fenced ino) frame)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-k6-create-fresh-inode-without-namep)
                  (:instance fn-bs-k6-write-then-fence-without-statep
                             (bs (mv-nth 1
                                   (fn-bs-create bs :staging stage :ok)))
                             (ino (fn-bs-next-ino bs))
                             (octets frame)))
            :in-theory (e/d (fn-bs-statep)
                            (fn-bs-create fn-bs-write fn-bs-fence-file
                             fn-bs-durable-content true-listp))))))

; FN-BS-PUT-ASSOC can update NIL keys as well, provided its input is an
; alist.  The existing generic same-key lemma requires non-NIL keys because
; malformed alists may contain bare NIL elements.
(local
 (defthm fn-bs-k6-assoc-put-same-with-alist
   (implies (alistp a)
            (equal (assoc-equal k (fn-bs-put-assoc k v a))
                   (cons k v)))
   :hints (("Goal" :induct (fn-bs-put-assoc k v a)
            :in-theory (enable fn-bs-put-assoc alistp)))))
(local
 (defthm fn-bs-k6-view-staging-alists
   (implies (fn-bs-statep bs)
            (let ((dirs (fn-bs-apply-entries
                         (fn-bs-dirs bs) (fn-bs-pending bs))))
              (and (alistp dirs)
                   (alistp (cdr (assoc-equal :staging dirs))))))
   :hints (("Goal"
            :use ((:instance fn-bs-apply-entries-preserves-dir-tablep
                             (dirs (fn-bs-dirs bs))
                             (ops (fn-bs-pending bs)))
                  (:instance fn-bs-dir-tablep-entries-are-entries
                             (x (fn-bs-apply-entries
                                 (fn-bs-dirs bs) (fn-bs-pending bs)))
                             (k :staging)))
            :in-theory (enable fn-bs-statep)))))
(local
 (defthm fn-bs-k6-staging-lookup-after-set-any-inodes
   (implies (fn-bs-statep bs)
            (equal
             (fn-bs-lookup
              (fn-bs-make unit inodes (fn-bs-dirs bs)
                          (append (fn-bs-pending bs)
                                  (list (list :set-entry :staging stage ino)))
                          next)
              :staging stage)
             ino))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-k6-view-staging-alists)
                  (:instance fn-bs-k6-assoc-put-same-with-alist
                             (k stage) (v ino)
                             (a (cdr (assoc-equal
                                      :staging
                                      (fn-bs-apply-entries
                                       (fn-bs-dirs bs)
                                       (fn-bs-pending bs))))))
                  (:instance fn-bs-k6-assoc-put-same-with-alist
                             (k :staging)
                             (v (fn-bs-put-assoc
                                 stage ino
                                 (cdr (assoc-equal
                                       :staging
                                       (fn-bs-apply-entries
                                        (fn-bs-dirs bs)
                                        (fn-bs-pending bs))))))
                             (a (fn-bs-apply-entries
                                 (fn-bs-dirs bs) (fn-bs-pending bs)))))
            :in-theory (e/d (fn-bs-lookup fn-bs-view
                             fn-bs-apply-ops-dirs-are-apply-entries
                             fn-bs-apply-entries-of-append
                             fn-bs-apply-entries)
                            (fn-bs-apply-ops
                             fn-bs-k6-assoc-put-same-with-alist))))))
(local
 (defthm fn-bs-k6-created-stage-lookup-without-namep
   (implies (and (fn-bs-statep bs)
                 (not (fn-bs-lookup bs :staging stage)))
            (equal (fn-bs-lookup
                    (mv-nth 1 (fn-bs-create bs :staging stage :ok))
                    :staging stage)
                   (fn-bs-next-ino bs)))
   :hints (("Goal" :in-theory (e/d (fn-bs-create)
                                   (fn-bs-lookup fn-bs-statep))))))
(local
 (defthm fn-bs-k6-write-created-inode-returns-ok-without-namep
   (implies (and (fn-bs-statep bs)
                 (not (fn-bs-lookup bs :staging stage)))
            (equal (mv-nth 0
                            (fn-bs-write
                             (mv-nth 1
                                     (fn-bs-create bs :staging stage :ok))
                             (fn-bs-next-ino bs) 0 frame :ok))
                   :ok))
   :hints (("Goal"
            :use ((:instance fn-bs-k6-create-fresh-inode-without-namep))
            :in-theory (e/d (fn-bs-write) (fn-bs-create))))))

(defthm fn-bs-k6-interpreted-record-fence-without-namep
  (implies (and (fn-bs-statep bs)
                (not (fn-bs-lookup bs :staging stage))
                (true-listp frame))
           (equal
            (car (nth 5 (fn-bs-run bs ks
                                   (fn-bs-record-program stage name frame)
                                   nil groups capacity)))
            (let* ((ino (fn-bs-next-ino bs))
                   (created
                    (mv-nth 1 (fn-bs-create bs :staging stage :ok)))
                   (written
                    (mv-nth 1 (fn-bs-write created ino 0 frame :ok))))
              (fn-bs-fence-file written ino))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-record-program fn-bs-run fn-bs-step
                             fn-bs-fsync-file)
                           (fn-bs-statep fn-bs-create fn-bs-write
                            fn-bs-fence-file fn-bs-lookup fn-bs-namep
                            fn-bs-durable-content)))))

(defthm fn-bs-k6-actual-record-file-cut-has-exact-frame
  (implies (and (fn-bs-statep bs)
                (not (fn-bs-lookup bs :staging stage))
                (true-listp frame))
           (equal
            (fn-bs-durable-content
             (car (nth 5 (fn-bs-run bs ks
                                    (fn-bs-record-program stage name frame)
                                    nil groups capacity)))
             (fn-bs-next-ino bs))
            frame))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bs-k6-interpreted-record-fence-without-namep)
                 (:instance fn-bs-k6-create-write-fence-without-namep))
           :in-theory (disable fn-bs-run fn-bs-record-program
                               fn-bs-durable-content fn-bs-create
                               fn-bs-write fn-bs-fence-file))))

; File fsync drains writes but cannot remove the pending staging entry.
(local
 (defthm fn-bs-k6-filter-writes-keeps-name-ops
   (equal (fn-bs-ops-for-name (fn-bs-ops-not-for-ino ops ino) dir name)
          (fn-bs-ops-for-name ops dir name))
   :hints (("Goal" :induct (fn-bs-ops-not-for-ino ops ino)
            :in-theory (enable fn-bs-ops-not-for-ino
                               fn-bs-ops-for-name)))))
(local
 (defthm fn-bs-k6-filter-writes-keeps-entry-after
   (equal (fn-bs-entry-after (fn-bs-ops-not-for-ino ops ino)
                             old dir name)
          (fn-bs-entry-after ops old dir name))
   :hints (("Goal"
            :use ((:instance fn-bs-entry-after-through-ops-for-name
                             (ops (fn-bs-ops-not-for-ino ops ino)))
                  (:instance fn-bs-entry-after-through-ops-for-name
                             (ops ops)))
            :in-theory (disable fn-bs-entry-after fn-bs-ops-for-name)))))
(local
 (defthm fn-bs-k6-lookup-is-entry-after
   (implies (and dir name)
            (equal (fn-bs-lookup bs dir name)
                   (fn-bs-entry-after
                    (fn-bs-pending bs)
                    (fn-bs-durable-entry bs dir name) dir name)))
   :hints (("Goal"
            :use ((:instance fn-bs-apply-entries-entry-is-entry-after
                             (dirs (fn-bs-dirs bs))
                             (ops (fn-bs-pending bs))))
            :in-theory (e/d (fn-bs-lookup fn-bs-view
                             fn-bs-durable-entry
                             fn-bs-apply-ops-dirs-are-apply-entries)
                            (fn-bs-apply-ops fn-bs-apply-entries
                             fn-bs-entry-after))))))
(local
 (defthm fn-bs-k6-file-fence-pending-is-filter
   (equal (fn-bs-pending (fn-bs-fence-file bs ino))
          (fn-bs-ops-not-for-ino (fn-bs-pending bs) ino))
   :hints (("Goal" :in-theory (enable fn-bs-fence-file)))))
(local
 (defthm fn-bs-k6-file-fence-keeps-valid-name-lookup
   (implies (and dir name)
            (equal (fn-bs-lookup (fn-bs-fence-file bs ino) dir name)
                   (fn-bs-lookup bs dir name)))
   :hints (("Goal"
            :use ((:instance fn-bs-k6-lookup-is-entry-after
                             (bs (fn-bs-fence-file bs ino)))
                  (:instance fn-bs-k6-lookup-is-entry-after (bs bs)))
            :in-theory (e/d (fn-bs-durable-entry)
                            (fn-bs-lookup fn-bs-entry-after
                             fn-bs-fence-file))))))

(defthm fn-bs-k6-file-cut-source-is-fenced-frame
  (implies (and (fn-bs-statep bs) (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage))
                (true-listp frame))
           (let* ((cut (car (nth 5
                                  (fn-bs-run
                                   bs ks
                                   (fn-bs-record-program stage name frame)
                                   nil groups capacity))))
                  (ino (fn-bs-next-ino bs)))
             (and (equal (fn-bs-lookup cut :staging stage) ino)
                  (fn-bs-fencedp cut ino)
                  (equal (fn-bs-durable-content cut ino) frame))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance
                  fn-bs-k6-interpreted-record-fence-is-write-fence)
                 (:instance fn-bs-k6-created-stage-lookup)
                 (:instance fn-bs-k6-actual-record-file-cut-has-exact-frame)
                 (:instance fn-bs-fence-file-drains-exactly-its-inode
                            (s (mv-nth 1
                                       (fn-bs-write
                                        (mv-nth 1
                                                (fn-bs-create
                                                 bs :staging stage :ok))
                                        (fn-bs-next-ino bs) 0 frame :ok)))
                            (ino (fn-bs-next-ino bs))))
           :in-theory (e/d (fn-bs-fencedp)
                           (fn-bs-run fn-bs-record-program fn-bs-create
                            fn-bs-write fn-bs-fence-file fn-bs-lookup
                            fn-bs-durable-content
                            fn-bs-k6-lookup-is-entry-after)))))

; Immutable link adds one pending destination entry.  It cannot alter a
; fenced source inode's durable bytes or resurrect a pending write to it.
(defthm fn-bs-k6-link-keeps-fenced-source
  (implies (and (fn-bs-inop (fn-bs-lookup bs :staging stage))
                (fn-bs-namep name)
                (not (fn-bs-lookup bs :transactions name))
                (fn-bs-fencedp bs (fn-bs-lookup bs :staging stage))
                (equal (fn-bs-durable-content
                        bs (fn-bs-lookup bs :staging stage)) frame))
           (let* ((ino (fn-bs-lookup bs :staging stage))
                  (linked (mv-nth 1
                                  (fn-bs-link bs :staging stage
                                              :transactions name :ok))))
             (and (equal (fn-bs-lookup linked :transactions name) ino)
                  (fn-bs-fencedp linked ino)
                  (equal (fn-bs-durable-content linked ino) frame))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bs-k6-lookup-after-pending-set
                            (dir :transactions) (name name)
                            (ino (fn-bs-lookup bs :staging stage))))
           :in-theory (e/d (fn-bs-link fn-bs-fencedp
                             fn-bs-durable-content
                             fn-bs-ops-for-ino-of-append
                             fn-bs-ops-for-ino)
                           (fn-bs-lookup)))))
(local
 (defthm fn-bs-k6-link-returns-ok
   (implies (and (fn-bs-inop (fn-bs-lookup bs :staging stage))
                 (not (fn-bs-lookup bs :transactions name)))
            (equal (mv-nth 0
                            (fn-bs-link bs :staging stage
                                        :transactions name :ok))
                   :ok))
   :hints (("Goal" :in-theory (enable fn-bs-link)))))

; This is the interpreter join: pair 8 is the cut following the actual
; successful immutable link, with the same byte state as linking pair 5.
(defthm fn-bs-k6-actual-link-cut-is-file-cut-link
  (implies
   (and (fn-bs-statep bs) (fn-bs-namep stage) (fn-bs-namep name)
        (not (fn-bs-lookup bs :staging stage)) (true-listp frame)
        (not (fn-bs-lookup
              (car (nth 5
                        (fn-bs-run bs ks
                                   (fn-bs-record-program stage name frame)
                                   nil groups capacity)))
              :transactions name)))
   (equal
    (car (nth 8 (fn-bs-run bs ks
                           (fn-bs-record-program stage name frame)
                           nil groups capacity)))
    (mv-nth 1
            (fn-bs-link
             (car (nth 5
                       (fn-bs-run bs ks
                                  (fn-bs-record-program stage name frame)
                                  nil groups capacity)))
             :staging stage :transactions name :ok))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k6-file-cut-source-is-fenced-frame)
                 (:instance fn-bs-k6-link-returns-ok
                            (bs (car (nth 5
                                          (fn-bs-run
                                           bs ks
                                           (fn-bs-record-program
                                            stage name frame)
                                           nil groups capacity)))))
                 (:instance
                  fn-bs-k6-interpreted-record-fence-is-write-fence))
           :in-theory (e/d (fn-bs-record-program fn-bs-run fn-bs-step
                             fn-bs-fsync-file fn-bs-statep)
                           (fn-bs-create fn-bs-write fn-bs-fence-file
                            fn-bs-link fn-bs-lookup fn-bs-durable-content
                            fn-bs-k6-lookup-is-entry-after)))))

(defthm fn-bs-k6-actual-record-linked-cut-has-exact-frame
  (implies
   (and (fn-bs-statep bs) (fn-bs-namep stage) (fn-bs-namep name)
        (not (fn-bs-lookup bs :staging stage)) (true-listp frame)
        (not (fn-bs-lookup
              (car (nth 5
                        (fn-bs-run bs ks
                                   (fn-bs-record-program stage name frame)
                                   nil groups capacity)))
              :transactions name)))
   (let ((cut (car (nth 8
                        (fn-bs-run bs ks
                                   (fn-bs-record-program stage name frame)
                                   nil groups capacity)))))
     (and (equal (fn-bs-lookup cut :transactions name)
                 (fn-bs-next-ino bs))
          (fn-bs-fencedp cut (fn-bs-next-ino bs))
          (equal (fn-bs-durable-content cut (fn-bs-next-ino bs)) frame))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k6-file-cut-source-is-fenced-frame)
                 (:instance fn-bs-k6-actual-link-cut-is-file-cut-link)
                 (:instance fn-bs-k6-link-keeps-fenced-source
                            (bs (car (nth 5
                                          (fn-bs-run
                                           bs ks
                                           (fn-bs-record-program
                                            stage name frame)
                                           nil groups capacity))))))
           :in-theory (e/d (fn-bs-statep fn-bs-inop)
                           (fn-bs-run fn-bs-record-program fn-bs-link
                            fn-bs-lookup fn-bs-durable-content
                            fn-bs-fencedp
                            fn-bs-k6-lookup-is-entry-after)))))

; The public input contract binds the frame to ACL2's candidate and the
; final transaction name to its sequence.  The raw-byte conclusion still
; comes from the actual program trace, independent of decoder membership.
(defthm fn-bs-k6-actual-record-linked-input-has-exact-frame
  (implies
   (and (fn-bs-statep bs)
        (fn-bs-record-inputp ks stage name frame)
        (not (fn-bs-lookup bs :staging stage))
        (not (fn-bs-lookup
              (car (nth 5
                        (fn-bs-run bs ks
                                   (fn-bs-record-program stage name frame)
                                   nil groups capacity)))
              :transactions name)))
   (let ((cut (car (nth 8
                        (fn-bs-run bs ks
                                   (fn-bs-record-program stage name frame)
                                   nil groups capacity)))))
     (and (equal (fn-bs-lookup cut :transactions name)
                 (fn-bs-next-ino bs))
          (fn-bs-fencedp cut (fn-bs-next-ino bs))
          (equal (fn-bs-durable-content cut (fn-bs-next-ino bs)) frame))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bs-k6-actual-record-linked-cut-has-exact-frame)
                 (:instance fn-bs-txn-name-is-a-name
                            (n (fn-store-event-sequence
                                (fn-sf-record-candidate ks)))))
           :in-theory (e/d (fn-bs-record-inputp)
                           (fn-bs-run fn-bs-record-program
                            fn-bs-durable-content fn-bs-lookup fn-bs-fencedp
                            fn-bs-k6-lookup-is-entry-after)))))

; When the final name is the sole pending operation at that name, a model
; crash may drop it or keep it.  In the keep arm, a non-NIL recovered lookup
; must be this target, and the fenced octets cannot tear.
(defthm fn-bs-k6-sole-link-survival-has-exact-octets
  (implies
   (and (fn-bs-namep name) (fn-bs-crash-imagep linked image)
        (equal (fn-bs-durable-entry linked :transactions name) nil)
        (equal (fn-bs-ops-for-name
                (fn-bs-pending linked) :transactions name)
               (list (list :set-entry :transactions name ino)))
        (fn-bs-inop ino) (fn-bs-fencedp linked ino)
        (equal (fn-bs-durable-content linked ino) frame)
        (fn-bs-lookup image :transactions name))
   (and (equal (fn-bs-lookup image :transactions name) ino)
        (equal (fn-bs-durable-content
                image (fn-bs-lookup image :transactions name))
               frame)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  fn-bs-crash-entry-is-the-durable-one-or-the-pending-target
                  (s linked) (dir :transactions))
                 (:instance fn-bs-crash-keeps-fenced-content
                            (s linked) (ino ino))
                 (:instance fn-bs-crash-image-is-quiet (s linked)))
           :in-theory (e/d (fn-bs-namep
                             fn-bs-quiet-lookup-is-durable-entry)
                           (fn-bs-crash-imagep fn-bs-lookup
                            fn-bs-durable-entry fn-bs-durable-content
                            fn-bs-fencedp
                            fn-bs-k6-lookup-is-entry-after)))))

(local
 (defthm fn-bs-k6-name-ops-of-append
   (equal (fn-bs-ops-for-name (append a b) dir name)
          (append (fn-bs-ops-for-name a dir name)
                  (fn-bs-ops-for-name b dir name)))
   :hints (("Goal" :induct (fn-bs-ops-for-name a dir name)
            :in-theory (enable fn-bs-ops-for-name)))))
(local
 (defthm fn-bs-k6-untouched-absent-name-is-durably-absent
   (implies (and (fn-bs-namep name)
                 (equal (fn-bs-ops-for-name
                         (fn-bs-pending bs) :transactions name) nil)
                 (not (fn-bs-lookup bs :transactions name)))
            (equal (fn-bs-durable-entry bs :transactions name) nil))
   :hints (("Goal"
            :use ((:instance fn-bs-lookup-of-an-untouched-name
                             (s bs) (dir :transactions) (name name)))
            :in-theory (e/d (fn-bs-namep)
                            (fn-bs-lookup fn-bs-durable-entry
                             fn-bs-ops-for-name))))))
(defthm fn-bs-k6-link-is-sole-pending-final-name
  (implies
   (and (fn-bs-inop (fn-bs-lookup bs :staging stage))
        (fn-bs-namep name)
        (not (fn-bs-lookup bs :transactions name))
        (equal (fn-bs-ops-for-name
                (fn-bs-pending bs) :transactions name) nil))
   (let* ((ino (fn-bs-lookup bs :staging stage))
          (linked (mv-nth 1
                          (fn-bs-link bs :staging stage
                                      :transactions name :ok))))
     (and (equal (fn-bs-durable-entry linked :transactions name) nil)
          (equal (fn-bs-ops-for-name
                  (fn-bs-pending linked) :transactions name)
                 (list (list :set-entry :transactions name ino))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  fn-bs-k6-untouched-absent-name-is-durably-absent))
           :in-theory (e/d (fn-bs-link fn-bs-ops-for-name
                             fn-bs-k6-name-ops-of-append
                             fn-bs-durable-entry)
                           (fn-bs-lookup
                            fn-bs-k6-lookup-is-entry-after)))))

; The two namespace premises at the file cut are meaningful.  A final
; name that is only hidden by a pending delete may reappear after a crash;
; one earlier pending set/delete pair may leave an unrelated target visible.
(defthm fn-bs-k6-actual-link-cut-has-sole-pending-name
  (implies
   (and (fn-bs-statep bs)
        (fn-bs-record-inputp ks stage name frame)
        (not (fn-bs-lookup bs :staging stage))
        (let ((file (car (nth 5
                              (fn-bs-run
                               bs ks
                               (fn-bs-record-program stage name frame)
                               nil groups capacity)))))
          (and (not (fn-bs-lookup file :transactions name))
               (equal (fn-bs-ops-for-name
                       (fn-bs-pending file) :transactions name) nil))))
   (let ((linked (car (nth 8
                           (fn-bs-run
                            bs ks (fn-bs-record-program stage name frame)
                            nil groups capacity)))))
     (and (equal (fn-bs-durable-entry linked :transactions name) nil)
          (equal (fn-bs-ops-for-name
                  (fn-bs-pending linked) :transactions name)
                 (list (list :set-entry :transactions name
                             (fn-bs-next-ino bs)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance
                  fn-bs-k6-actual-record-linked-input-has-exact-frame)
                 (:instance fn-bs-k6-actual-link-cut-is-file-cut-link)
                 (:instance fn-bs-k6-file-cut-source-is-fenced-frame)
                 (:instance fn-bs-k6-link-is-sole-pending-final-name
                            (bs (car (nth 5
                                          (fn-bs-run
                                           bs ks
                                           (fn-bs-record-program
                                            stage name frame)
                                           nil groups capacity)))))
                 (:instance
                  fn-bs-k6-untouched-absent-name-is-durably-absent
                  (bs (car (nth 5
                                (fn-bs-run
                                 bs ks
                                 (fn-bs-record-program stage name frame)
                                 nil groups capacity))))))
           :in-theory (e/d (fn-bs-record-inputp fn-bs-statep fn-bs-inop)
                           (fn-bs-run fn-bs-record-program fn-bs-link
                            fn-bs-lookup fn-bs-durable-entry
                            fn-bs-ops-for-name fn-bs-fencedp
                            fn-bs-k6-lookup-is-entry-after)))))

; This is raw-byte provenance through an arbitrary admissible crash image,
; conditional only on the final name actually surviving that image.  It
; does not assume which inode that name addresses or what bytes it holds.
(defthm fn-bs-k6-actual-linked-crash-surviving-name-has-exact-frame
  (implies
   (and (fn-bs-statep bs)
        (fn-bs-record-inputp ks stage name frame)
        (not (fn-bs-lookup bs :staging stage))
        (let ((file (car (nth 5
                              (fn-bs-run
                               bs ks
                               (fn-bs-record-program stage name frame)
                               nil groups capacity)))))
          (and (not (fn-bs-lookup file :transactions name))
               (equal (fn-bs-ops-for-name
                       (fn-bs-pending file) :transactions name) nil)))
        (fn-bs-crash-imagep
         (car (nth 8
                   (fn-bs-run bs ks
                              (fn-bs-record-program stage name frame)
                              nil groups capacity))) image)
        (fn-bs-lookup image :transactions name))
   (and (equal (fn-bs-lookup image :transactions name)
               (fn-bs-next-ino bs))
        (equal (fn-bs-durable-content
                image (fn-bs-lookup image :transactions name)) frame)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance
                  fn-bs-k6-actual-record-linked-input-has-exact-frame)
                 (:instance fn-bs-k6-actual-link-cut-has-sole-pending-name)
                 (:instance fn-bs-k6-sole-link-survival-has-exact-octets
                            (linked (car (nth 8
                                              (fn-bs-run
                                               bs ks
                                               (fn-bs-record-program
                                                stage name frame)
                                               nil groups capacity))))
                            (ino (fn-bs-next-ino bs))))
           :in-theory (e/d (fn-bs-record-inputp fn-bs-statep fn-bs-inop)
                           (fn-bs-run fn-bs-record-program fn-bs-lookup
                            fn-bs-durable-entry fn-bs-durable-content
                            fn-bs-ops-for-name fn-bs-fencedp
                            fn-bs-crash-imagep
                            fn-bs-k6-lookup-is-entry-after)))))

; The scanner's one-record decoder reads exactly those recovered bytes.
; Whole-list scanner membership still needs the namespace/sequence bridge.
(defthm fn-bs-k6-actual-linked-crash-decoder-reads-candidate
  (implies
   (and (fn-bs-statep bs)
        (fn-bs-record-inputp ks stage name frame)
        (not (fn-bs-lookup bs :staging stage))
        (let ((file (car (nth 5
                              (fn-bs-run
                               bs ks
                               (fn-bs-record-program stage name frame)
                               nil groups capacity)))))
          (and (not (fn-bs-lookup file :transactions name))
               (equal (fn-bs-ops-for-name
                       (fn-bs-pending file) :transactions name) nil)))
        (fn-bs-crash-imagep
         (car (nth 8
                   (fn-bs-run bs ks
                              (fn-bs-record-program stage name frame)
                              nil groups capacity))) image)
        (fn-bs-lookup image :transactions name))
   (equal (fn-bs-record-of image
                           (fn-bs-lookup image :transactions name))
          (fn-sf-record-candidate ks)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  fn-bs-k6-actual-linked-crash-surviving-name-has-exact-frame)
                 (:instance fn-bs-crash-image-is-quiet
                            (s (car (nth 8
                                          (fn-bs-run
                                           bs ks
                                           (fn-bs-record-program
                                            stage name frame)
                                           nil groups capacity))))))
           :in-theory (e/d (fn-bs-record-of fn-bs-record-inputp
                             fn-bs-quiet-content-is-durable-content)
                           (fn-bs-run fn-bs-record-program fn-bs-lookup
                            fn-bs-durable-content fn-bs-record-of-octets
                            fn-bs-content fn-bs-crash-imagep
                            fn-bs-k6-lookup-is-entry-after)))))

; The two physical steps after link are a kernel observation and a named
; crash cut.  Neither changes the byte state; this theorem proves that for
; the same actual interpreter run rather than assuming the cuts coincide.
(defthm fn-bs-k6-actual-attempted-cut-keeps-linked-byte-state
  (implies
   (and (fn-bs-statep bs)
        (fn-bs-record-inputp ks stage name frame)
        (not (fn-bs-lookup bs :staging stage))
        (not (fn-bs-lookup
              (car (nth 5
                        (fn-bs-run bs ks
                                   (fn-bs-record-program stage name frame)
                                   nil groups capacity)))
              :transactions name)))
   (equal
    (car (nth 10
              (fn-bs-run bs ks
                         (fn-bs-record-program stage name frame)
                         nil groups capacity)))
    (car (nth 8
              (fn-bs-run bs ks
                         (fn-bs-record-program stage name frame)
                         nil groups capacity)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k6-actual-link-cut-is-file-cut-link)
                 (:instance fn-bs-k6-file-cut-source-is-fenced-frame)
                 (:instance fn-bs-k6-link-returns-ok
                            (bs (car (nth 5
                                          (fn-bs-run
                                           bs ks
                                           (fn-bs-record-program
                                            stage name frame)
                                           nil groups capacity))))))
           :in-theory (e/d (fn-bs-record-inputp fn-bs-record-program
                             fn-bs-run fn-bs-step fn-bs-fsync-file)
                           (fn-bs-statep fn-bs-create fn-bs-write
                            fn-bs-fence-file fn-bs-link fn-bs-lookup
                            fn-bs-durable-content
                            fn-bs-k6-lookup-is-entry-after)))))

; This is the P-RECORD crash cut K8 also names.  Its admissible crash images
; have the same raw candidate frame and decoder result as pair 8 whenever
; the final name survives.  Scanner list membership remains a separate
; namespace/sequence obligation.
(defthm fn-bs-k6-attempted-crash-decoder-reads-exact-frame
  (implies
   (and (fn-bs-statep bs)
        (fn-bs-record-inputp ks stage name frame)
        (not (fn-bs-lookup bs :staging stage))
        (let ((file (car (nth 5
                              (fn-bs-run
                               bs ks
                               (fn-bs-record-program stage name frame)
                               nil groups capacity)))))
          (and (not (fn-bs-lookup file :transactions name))
               (equal (fn-bs-ops-for-name
                       (fn-bs-pending file) :transactions name) nil)))
        (fn-bs-crash-imagep
         (car (nth 10
                   (fn-bs-run bs ks
                              (fn-bs-record-program stage name frame)
                              nil groups capacity))) image)
        (fn-bs-lookup image :transactions name))
   (and (equal (fn-bs-durable-content
                image (fn-bs-lookup image :transactions name)) frame)
        (equal (fn-bs-record-of
                image (fn-bs-lookup image :transactions name))
               (fn-sf-record-candidate ks))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  fn-bs-k6-actual-attempted-cut-keeps-linked-byte-state)
                 (:instance
                  fn-bs-k6-actual-linked-crash-decoder-reads-candidate)
                 (:instance
                  fn-bs-k6-actual-linked-crash-surviving-name-has-exact-frame)
                 (:instance
                  fn-bs-k6-untouched-absent-name-is-durably-absent
                  (bs (car (nth 5
                                (fn-bs-run
                                 bs ks
                                 (fn-bs-record-program stage name frame)
                                 nil groups capacity))))))
           :in-theory (e/d (fn-bs-record-inputp)
                           (fn-bs-run fn-bs-record-program fn-bs-lookup
                            fn-bs-durable-entry fn-bs-durable-content
                            fn-bs-record-of fn-bs-ops-for-name
                            fn-bs-crash-imagep
                            fn-bs-k6-lookup-is-entry-after)))))

; The related :record-staged input has no transaction-directory operation.
; The actual create/write/file-fence prefix touches staging and its new inode,
; not transactions.  This discharges the earlier-operation premise of the
; surviving-name crash theorem for this related-input slice of K0.
(defthm fn-bs-k6-related-record-staged-has-no-transaction-pending
  (implies (and (fn-bs-store-relation bs ks)
                (equal (fn-sf-phase ks) :record-staged))
           (not (consp (fn-bs-ops-for-dir
                        (fn-bs-pending bs) :transactions))))
  :rule-classes nil
  :hints (("Goal" :use (fn-bs-store-relation-window-unfolds
                         fn-bs-pending-matches-phase-unfolds)
           :in-theory (enable fn-bs-replay-visiblep
                              fn-sf-record-present-visiblep))))

(local
 (defthm fn-bs-k6-filter-inode-writes-keeps-dir-ops
   (equal (fn-bs-ops-for-dir (fn-bs-ops-not-for-ino ops ino) dir)
          (fn-bs-ops-for-dir ops dir))
   :hints (("Goal" :induct (fn-bs-ops-not-for-ino ops ino)
            :in-theory (enable fn-bs-ops-not-for-ino fn-bs-ops-for-dir)))))

(defthm fn-bs-k6-related-input-file-cut-has-no-transaction-pending
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (not (consp
                 (fn-bs-ops-for-dir
                  (fn-bs-pending
                   (car (nth 5 (fn-bs-run bs ks
                                          (fn-bs-record-program stage name frame)
                                          nil groups capacity))))
                  :transactions))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k6-related-record-staged-has-no-transaction-pending)
                 (:instance fn-bs-k6-interpreted-record-fence-is-write-fence)
                 (:instance fn-bs-store-relation-unfolds))
           :in-theory (e/d (fn-bs-record-inputp fn-bs-create fn-bs-write
                            fn-bs-fence-file fn-bs-ops-for-dir
                            fn-bs-ops-for-dir-of-append)
                           (fn-bs-run fn-bs-record-program fn-bs-statep
                            fn-bs-store-relation fn-bs-lookup
                            fn-bs-ops-not-for-ino)))))

(defthm fn-bs-k6-related-input-file-cut-has-no-prior-final-op
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (equal (fn-bs-ops-for-name
                   (fn-bs-pending
                    (car (nth 5 (fn-bs-run bs ks
                                           (fn-bs-record-program stage name frame)
                                           nil groups capacity))))
                   :transactions name) nil))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-k6-related-input-file-cut-has-no-transaction-pending)
                         (:instance fn-bs-ops-for-name-through-ops-for-dir
                                    (ops (fn-bs-pending
                                          (car (nth 5 (fn-bs-run bs ks
                                                                 (fn-bs-record-program stage name frame)
                                                                 nil groups capacity)))))
                                    (dir :transactions)))
           :in-theory (e/d (fn-bs-ops-for-name)
                           (fn-bs-run fn-bs-record-program fn-bs-ops-for-dir)))))

(defthm fn-bs-k6-related-attempted-crash-reads-exact-frame
  (implies
   (and (fn-bs-store-relation bs ks)
        (fn-bs-record-inputp ks stage name frame)
        (not (fn-bs-lookup bs :staging stage))
        (not (fn-bs-lookup
              (car (nth 5 (fn-bs-run bs ks
                                     (fn-bs-record-program stage name frame)
                                     nil groups capacity)))
              :transactions name))
        (fn-bs-crash-imagep
         (car (nth 10 (fn-bs-run bs ks
                                    (fn-bs-record-program stage name frame)
                                    nil groups capacity))) image)
        (fn-bs-lookup image :transactions name))
   (and (equal (fn-bs-durable-content
                image (fn-bs-lookup image :transactions name)) frame)
        (equal (fn-bs-record-of
                image (fn-bs-lookup image :transactions name))
               (fn-sf-record-candidate ks))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bs-k6-related-input-file-cut-has-no-prior-final-op)
                 (:instance fn-bs-k6-attempted-crash-decoder-reads-exact-frame)
                 (:instance fn-bs-store-relation-unfolds))
           :in-theory (disable fn-bs-run fn-bs-record-program
                               fn-bs-store-relation fn-bs-record-inputp
                               fn-bs-crash-imagep fn-bs-lookup
                               fn-bs-durable-content fn-bs-record-of
                               fn-bs-ops-for-name))))

; The typed Store-event sequence, not the article-only accessor, is the
; transaction namespace index.  The staged kernel candidate's sequence is
; the length of the durable record prefix, hence the next name is absent in
; the contiguous durable namespace.  This works for all Store event kinds.
(defthm fn-bs-k6-related-staged-durable-name-count-is-record-count
  (implies (and (fn-bs-store-relation bs ks)
                (equal (fn-sf-phase ks) :record-staged))
           (equal (len (fn-bs-durable-names bs :transactions))
                  (len (fn-sf-records ks))))
  :rule-classes nil
  :hints (("Goal" :use (fn-bs-store-relation-window-unfolds
                         fn-bs-durable-records-length)
           :in-theory (enable fn-bs-replay-visiblep
                              fn-sf-crash-imagep
                              fn-sf-record-present-visiblep))))

(local
 (defthm fn-bs-k6-assoc-absent-outside-strip-cars
   (implies (not (member-equal name (strip-cars alist)))
            (not (assoc-equal name alist)))
   :hints (("Goal" :induct (strip-cars alist)))))

(defthm fn-bs-k6-related-staged-durable-final-name-absent
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame))
           (not (fn-bs-durable-entry bs :transactions name)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k6-related-staged-durable-name-count-is-record-count)
                 (:instance fn-bs-store-relation-unfolds)
                 (:instance fn-bs-txn-name-not-in-txn-names
                            (i (len (fn-bs-durable-names bs :transactions)))
                            (n (len (fn-bs-durable-names bs :transactions)))))
           :in-theory (e/d (fn-bs-record-inputp fn-sf-statep
                            fn-sf-phase-shapep fn-sf-candidatep
                            fn-bs-durable-entry fn-bs-durable-names
                            fn-bs-contiguous-namesp fn-store-event-sequence)
                           (fn-bs-store-relation fn-bs-statep
                            fn-bs-txn-names)))))

(defthm fn-bs-k6-file-cut-dirs-are-input-dirs
  (implies (and (fn-bs-statep bs)
                (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage))
                (true-listp frame))
           (equal (fn-bs-dirs
                   (car (nth 5 (fn-bs-run bs ks
                                          (fn-bs-record-program stage name frame)
                                          nil groups capacity))))
                  (fn-bs-dirs bs)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k6-interpreted-record-fence-is-write-fence))
           :in-theory (e/d (fn-bs-create fn-bs-write)
                           (fn-bs-run fn-bs-record-program fn-bs-statep
                            fn-bs-fence-file fn-bs-lookup)))))

(local
 (defthm fn-bs-k6-quiet-directory-lookup-is-durable-entry
   (implies (and dir name
                 (not (consp (fn-bs-ops-for-dir (fn-bs-pending bs) dir))))
            (equal (fn-bs-lookup bs dir name)
                   (fn-bs-durable-entry bs dir name)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-bs-k6-lookup-is-entry-after)
                          (:instance fn-bs-ops-for-name-through-ops-for-dir
                                     (ops (fn-bs-pending bs)))
                          (:instance fn-bs-entry-after-through-ops-for-name
                                     (ops (fn-bs-pending bs))
                                     (old (fn-bs-durable-entry bs dir name))))
            :in-theory (e/d (fn-bs-ops-for-name fn-bs-entry-after)
                            (fn-bs-lookup fn-bs-ops-for-dir))))))

(defthm fn-bs-k6-related-input-file-cut-final-name-absent
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (not (fn-bs-lookup
                 (car (nth 5 (fn-bs-run bs ks
                                        (fn-bs-record-program stage name frame)
                                        nil groups capacity)))
                 :transactions name)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k6-related-staged-durable-final-name-absent)
                 (:instance fn-bs-k6-related-input-file-cut-has-no-transaction-pending)
                 (:instance fn-bs-k6-file-cut-dirs-are-input-dirs)
                 (:instance fn-bs-store-relation-unfolds)
                 (:instance fn-bs-txn-name-is-a-name
                            (n (fn-store-event-sequence (fn-sf-record-candidate ks))))
                 (:instance fn-bs-k6-quiet-directory-lookup-is-durable-entry
                            (bs (car (nth 5 (fn-bs-run bs ks
                                                     (fn-bs-record-program stage name frame)
                                                     nil groups capacity))))
                            (dir :transactions)))
           :in-theory (e/d (fn-bs-durable-entry fn-bs-record-inputp)
                           (fn-bs-run fn-bs-record-program fn-bs-lookup
                            fn-bs-k6-lookup-is-entry-after
                            fn-bs-store-relation fn-bs-ops-for-dir
                            fn-bs-pending fn-bs-dirs)))))

; Related-input K0 slice: both final-name freshness conditions are now
; consequences of the relation and the actual interpreted prefix.  The
; remaining premises identify a model crash image and the surviving link.
(defthm fn-bs-k6-related-attempted-surviving-scan-source-is-exact-frame
  (implies
   (and (fn-bs-store-relation bs ks)
        (fn-bs-record-inputp ks stage name frame)
        (not (fn-bs-lookup bs :staging stage))
        (fn-bs-crash-imagep
         (car (nth 10 (fn-bs-run bs ks
                                    (fn-bs-record-program stage name frame)
                                    nil groups capacity))) image)
        (fn-bs-lookup image :transactions name))
   (and (equal (fn-bs-durable-content
                image (fn-bs-lookup image :transactions name)) frame)
        (equal (fn-bs-record-of
                image (fn-bs-lookup image :transactions name))
               (fn-sf-record-candidate ks))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bs-k6-related-input-file-cut-final-name-absent)
                 (:instance fn-bs-k6-related-attempted-crash-reads-exact-frame))
           :in-theory (disable fn-bs-run fn-bs-record-program
                               fn-bs-store-relation fn-bs-record-inputp
                               fn-bs-crash-imagep fn-bs-lookup
                               fn-bs-durable-content fn-bs-record-of))))
