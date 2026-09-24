; K6: the actual P-RECORD program must publish exactly the whole frame it
; wrote and fenced, not merely a record with matching decoded fields.
(in-package "ACL2")
(include-book "byte-store-relation")
(include-book "byte-store-program-invariants")
(include-book "frame-trailer")
(include-book "byte-store-frame")

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

; The candidate exists already in :record-staged, before it is eligible for
; crash-image visibility.  State just its sequence shape here; opening the
; complete Store-event codec together with the byte relation makes the final
; name proof expand for minutes without adding a needed fact.
(local
 (defthm fn-bs-k6-staged-candidate-is-next-sequence
   (implies (and (fn-sf-statep ks)
                 (equal (fn-sf-phase ks) :record-staged))
            (equal (fn-store-event-sequence (fn-sf-record-candidate ks))
                   (len (fn-sf-records ks))))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (e/d (fn-sf-statep fn-sf-phase-shapep
                  fn-sf-record-phasep fn-sf-candidatep)
                 (fn-store-event-sequence fn-store-event-p
                  fn-sf-record-listp fn-sf-success-listp
                  fn-sf-shapep))))))

(defthm fn-bs-k6-related-staged-durable-final-name-absent
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame))
           (not (fn-bs-durable-entry bs :transactions name)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k6-related-staged-durable-name-count-is-record-count)
                 (:instance fn-bs-store-relation-unfolds)
                 (:instance fn-bs-k6-staged-candidate-is-next-sequence)
                 (:instance fn-bs-txn-name-not-in-txn-names
                            (i (len (fn-bs-durable-names bs :transactions)))
                            (n (len (fn-bs-durable-names bs :transactions)))))
           :in-theory (e/d (fn-bs-record-inputp fn-bs-durable-entry
                            fn-bs-durable-names fn-bs-contiguous-namesp)
                           (fn-bs-store-relation fn-bs-statep fn-sf-statep
                            fn-sf-phase-shapep fn-sf-candidatep
                            fn-store-event-sequence fn-bs-txn-names
                            fn-bs-txn-name-not-in-txn-names)))))

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

; The actual link and callback do not fence a directory.  Therefore the
; scanner's durable index at pair 10 is still the input's next index.
(defthm fn-bs-k6-related-attempt-durable-namespace-is-input-namespace
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (equal (fn-bs-dirs
                   (car (nth 10 (fn-bs-run bs ks
                                           (fn-bs-record-program stage name frame)
                                           nil groups capacity))))
                  (fn-bs-dirs bs)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k6-related-input-file-cut-final-name-absent)
                 (:instance fn-bs-k6-file-cut-dirs-are-input-dirs)
                 (:instance fn-bs-k6-actual-link-cut-is-file-cut-link)
                 (:instance fn-bs-k6-actual-attempted-cut-keeps-linked-byte-state)
                 (:instance fn-bs-store-relation-unfolds))
           :in-theory (e/d (fn-bs-record-inputp fn-bs-link)
                           (fn-bs-run fn-bs-record-program fn-bs-statep
                            fn-bs-store-relation fn-bs-lookup
                            fn-bs-k6-lookup-is-entry-after)))))

(defthm fn-bs-k6-related-attempt-name-is-next-scanner-name
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (equal name
                  (fn-bs-txn-name
                   (len (fn-bs-durable-names
                         (car (nth 10 (fn-bs-run bs ks
                                                 (fn-bs-record-program stage name frame)
                                                 nil groups capacity)))
                         :transactions)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bs-k6-related-attempt-durable-namespace-is-input-namespace)
                 (:instance fn-bs-k6-related-staged-durable-name-count-is-record-count)
                 (:instance fn-bs-store-relation-unfolds))
           :in-theory (e/d (fn-bs-record-inputp fn-sf-statep
                            fn-sf-phase-shapep fn-sf-candidatep
                            fn-bs-durable-names)
                           (fn-bs-run fn-bs-record-program
                            fn-bs-store-relation fn-bs-dirs)))))

(defthm fn-bs-k6-present-lookup-is-in-names
  (implies (fn-bs-lookup s dir name)
           (member-equal name (fn-bs-names s dir)))
  :hints (("Goal" :in-theory (enable fn-bs-lookup fn-bs-names))))

(defthm fn-bs-k6-surviving-next-name-extends-scanner-namespace
  (implies (and (fn-bs-store-relation at ak)
                (fn-bs-crash-imagep at image)
                (fn-bs-lookup image :transactions
                              (fn-bs-txn-name
                               (len (fn-bs-durable-names at :transactions)))))
           (equal (fn-bs-names image :transactions)
                  (fn-bs-txn-names
                   (1+ (len (fn-bs-durable-names at :transactions))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-crash-image-transaction-names
                                    (bs at) (ks ak))
                         (:instance fn-bs-k6-present-lookup-is-in-names
                                    (s image) (dir :transactions)
                                    (name (fn-bs-txn-name
                                           (len (fn-bs-durable-names at :transactions)))))
                         (:instance fn-bs-txn-name-not-in-txn-names
                                    (i (len (fn-bs-durable-names at :transactions)))
                                    (n (len (fn-bs-durable-names at :transactions)))))
           :in-theory (disable fn-bs-store-relation fn-bs-crash-imagep
                               fn-bs-names fn-bs-lookup fn-bs-txn-names))))

(local
 (defthm fn-bs-k6-read-records-at-end
   (implies (natp n)
            (equal (fn-bs-read-records image n n) nil))
   :hints (("Goal" :expand ((fn-bs-read-records image n n))))))

(local
 (defthm fn-bs-k6-one-scanner-record-is-candidate
   (implies (and (natp n)
                 (fn-bs-inop (fn-bs-lookup image :transactions (fn-bs-txn-name n)))
                 (fn-store-event-p candidate)
                 (equal (fn-store-event-sequence candidate) n)
                 (equal (fn-bs-record-of
                         image (fn-bs-lookup image :transactions
                                             (fn-bs-txn-name n))) candidate))
            (equal (fn-bs-read-records image n (1+ n))
                   (list candidate)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bs-read-records)
                            (fn-bs-record-of fn-bs-lookup))))))

(local
 (defthm fn-bs-k6-related-durable-prefix-is-not-fault
   (implies (fn-bs-store-relation at ak)
            (not (equal (fn-bs-durable-records at) :fault)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-bs-store-relation-unfolds
                                     (bs at) (ks ak)))))))

; This is the namespace/ordered-scan bridge, independent of a particular
; publisher.  It needs neither a scan-list equality nor a candidate-membership
; premise: it reads the old prefix and the one exact event at the next name.
(defthm fn-bs-k6-related-surviving-next-record-is-scanner-tail
  (implies (and (fn-bs-store-relation at ak)
                (fn-bs-crash-imagep at image)
                (let ((n (len (fn-bs-durable-names at :transactions))))
                  (and (fn-bs-inop
                        (fn-bs-lookup image :transactions (fn-bs-txn-name n)))
                       (fn-store-event-p candidate)
                       (equal (fn-store-event-sequence candidate) n)
                       (equal (fn-bs-record-of
                               image (fn-bs-lookup image :transactions
                                                   (fn-bs-txn-name n)))
                              candidate))))
           (equal (fn-bs-scan-records (fn-bs-scan-store image))
                  (append (fn-bs-durable-records at) (list candidate))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k6-surviving-next-name-extends-scanner-namespace)
                 (:instance fn-bs-k6-related-durable-prefix-is-not-fault)
                 (:instance fn-bs-crash-image-reads-the-durable-records
                            (bs at) (ks ak))
                 (:instance fn-bs-store-crash-image-scans
                            (bs at) (ks ak))
                 (:instance fn-bs-txn-names-length
                            (n (1+ (len (fn-bs-durable-names at :transactions)))))
                 (:instance fn-bs-read-records-of-one-more
                            (s image) (n 0)
                            (count (len (fn-bs-durable-names at :transactions))))
                 (:instance fn-bs-k6-one-scanner-record-is-candidate
                            (n (len (fn-bs-durable-names at :transactions)))))
           :in-theory (e/d (fn-bs-scan-store fn-bs-scan-records
                            fn-bs-scan-okp fn-bs-contiguous-namesp)
                           (fn-bs-store-relation fn-bs-crash-imagep
                            fn-bs-read-records fn-bs-names
                            fn-bs-lookup fn-bs-record-of
                            fn-bs-txn-names)))))

(defthm fn-bs-k6-related-attempt-surviving-name-is-fresh-inode
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage))
                (fn-bs-crash-imagep
                 (car (nth 10 (fn-bs-run bs ks
                                            (fn-bs-record-program stage name frame)
                                            nil groups capacity))) image)
                (fn-bs-lookup image :transactions name))
           (equal (fn-bs-lookup image :transactions name)
                  (fn-bs-next-ino bs)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bs-k6-related-input-file-cut-final-name-absent)
                 (:instance fn-bs-k6-related-input-file-cut-has-no-prior-final-op)
                 (:instance fn-bs-k6-actual-attempted-cut-keeps-linked-byte-state)
                 (:instance fn-bs-k6-actual-linked-crash-surviving-name-has-exact-frame)
                 (:instance fn-bs-store-relation-unfolds))
           :in-theory (disable fn-bs-run fn-bs-record-program
                               fn-bs-store-relation fn-bs-record-inputp
                               fn-bs-crash-imagep fn-bs-lookup
                               fn-bs-ops-for-name))))

(defthm fn-bs-k6-related-input-candidate-is-next-typed-event
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((at (car (nth 10 (fn-bs-run bs ks
                                              (fn-bs-record-program stage name frame)
                                              nil groups capacity)))))
             (and (fn-store-event-p (fn-sf-record-candidate ks))
                  (equal (fn-store-event-sequence (fn-sf-record-candidate ks))
                         (len (fn-bs-durable-names at :transactions))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-k6-related-attempt-durable-namespace-is-input-namespace)
                         (:instance fn-bs-k6-related-staged-durable-name-count-is-record-count)
                         (:instance fn-bs-store-relation-unfolds))
           :in-theory (e/d (fn-bs-record-inputp fn-sf-statep
                            fn-sf-phase-shapep fn-sf-candidatep
                            fn-bs-durable-names)
                           (fn-bs-run fn-bs-record-program
                            fn-bs-store-relation fn-bs-dirs)))))

(local
 (defthm fn-bs-k6-state-next-ino-is-inop
   (implies (fn-bs-statep bs)
            (fn-bs-inop (fn-bs-next-ino bs)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-bs-statep fn-bs-inop)))))

(local
 (defthm fn-bs-k6-related-attempt-surviving-lookup-is-inop
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-record-inputp ks stage name frame)
                 (not (fn-bs-lookup bs :staging stage))
                 (fn-bs-crash-imagep
                  (car (nth 10 (fn-bs-run bs ks
                                             (fn-bs-record-program stage name frame)
                                             nil groups capacity))) image)
                 (fn-bs-lookup image :transactions name))
            (fn-bs-inop (fn-bs-lookup image :transactions name)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-bs-k6-related-attempt-surviving-name-is-fresh-inode)
                          (:instance fn-bs-k6-state-next-ino-is-inop)
                          (:instance fn-bs-store-relation-unfolds))
            :in-theory (disable fn-bs-run fn-bs-record-program
                                fn-bs-lookup fn-bs-store-relation
                                fn-bs-crash-imagep)))))

; The actual pair-10 interpreter and byte crash now meet the ordered scan.
; The attempt-state relation is explicit: establishing it for all successful
; served calls is the remaining K0 program-preservation obligation.
(defthm fn-bs-k6-related-attempt-surviving-crash-scans-exact-frame-event
  (implies
   (and (fn-bs-store-relation bs ks)
        (fn-bs-record-inputp ks stage name frame)
        (not (fn-bs-lookup bs :staging stage))
        (let ((pair (nth 10 (fn-bs-run bs ks
                                        (fn-bs-record-program stage name frame)
                                        nil groups capacity))))
          (fn-bs-store-relation (car pair) (cdr pair)))
        (fn-bs-crash-imagep
         (car (nth 10 (fn-bs-run bs ks
                                    (fn-bs-record-program stage name frame)
                                    nil groups capacity))) image)
        (fn-bs-lookup image :transactions name))
   (let ((at (car (nth 10 (fn-bs-run bs ks
                                        (fn-bs-record-program stage name frame)
                                        nil groups capacity)))))
     (and (equal (fn-bs-durable-content
                  image (fn-bs-lookup image :transactions name)) frame)
          (equal (fn-bs-scan-records (fn-bs-scan-store image))
                 (append (fn-bs-durable-records at)
                         (list (fn-sf-record-candidate ks)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k6-related-attempted-surviving-scan-source-is-exact-frame)
                 (:instance fn-bs-k6-related-attempt-surviving-name-is-fresh-inode)
                 (:instance fn-bs-k6-related-attempt-surviving-lookup-is-inop)
                 (:instance fn-bs-k6-related-attempt-name-is-next-scanner-name)
                 (:instance fn-bs-k6-related-input-candidate-is-next-typed-event)
                 (:instance fn-bs-k6-related-surviving-next-record-is-scanner-tail
                            (at (car (nth 10 (fn-bs-run bs ks
                                                           (fn-bs-record-program stage name frame)
                                                           nil groups capacity))))
                            (ak (cdr (nth 10 (fn-bs-run bs ks
                                                           (fn-bs-record-program stage name frame)
                                                           nil groups capacity))))
                            (candidate (fn-sf-record-candidate ks))))
           :in-theory (disable fn-bs-run fn-bs-record-program
                               fn-bs-store-relation fn-bs-record-inputp
                               fn-bs-crash-imagep fn-bs-scan-store
                               fn-bs-scan-records fn-bs-durable-records
                               fn-bs-durable-content fn-bs-record-of
                               fn-bs-lookup fn-bs-durable-names))))

; K0 trace slice.  The host calls the ACL2 record-file and record-link
; observations only after the corresponding successful syscalls.  These
; equalities derive the logical state at that *actual* interpreter cut;
; they do not assume the byte/kernel relation at the output.
(local
 (defthm fn-bs-k0-record-file-cut-kernel-is-file-observation
   (implies (and (fn-bs-statep bs)
                 (not (fn-bs-lookup bs :staging stage)))
            (equal (cdr (nth 5 (fn-bs-run bs ks
                                            (fn-bs-record-program stage name frame)
                                            nil groups capacity)))
                   (fn-sf-record-file-result ks :ok)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-k6-interpreted-record-fence-without-namep)
                  (:instance fn-bs-k6-write-created-inode-returns-ok-without-namep))
            :in-theory (e/d (fn-bs-record-program fn-bs-run fn-bs-step
                             fn-sf-dispatch fn-bs-fsync-file)
                            (fn-bs-statep fn-bs-create fn-bs-write
                             fn-bs-fence-file fn-bs-lookup fn-bs-content
                             fn-bs-view))))))

(local
 (defthm fn-bs-k0-record-suffix-starts-at-file-cut
   (implies (and (fn-bs-statep bs)
                 (fn-bs-record-inputp ks stage name frame)
                 (not (fn-bs-lookup bs :staging stage)))
            (equal (nth 10 (fn-bs-run bs ks
                                         (fn-bs-record-program stage name frame)
                                         nil groups capacity))
                   (nth 4 (fn-bs-run
                           (car (nth 5 (fn-bs-run bs ks
                                                   (fn-bs-record-program stage name frame)
                                                   nil groups capacity)))
                           (cdr (nth 5 (fn-bs-run bs ks
                                                   (fn-bs-record-program stage name frame)
                                                   nil groups capacity)))
                           (nthcdr 6 (fn-bs-record-program stage name frame))
                           nil groups capacity))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-k0-record-file-cut-kernel-is-file-observation))
            :in-theory (e/d (fn-bs-record-program fn-bs-run fn-bs-step
                             fn-bs-fsync-file)
                            (fn-bs-statep fn-bs-create fn-bs-write
                             fn-bs-fence-file fn-bs-lookup fn-bs-content
                             fn-bs-view))))))

(local
 (defthm fn-bs-k0-record-suffix-link-callback
   (implies (and (fn-bs-inop (fn-bs-lookup file :staging stage))
                 (not (fn-bs-lookup file :transactions name)))
            (equal (cdr (nth 4 (fn-bs-run
                                file fileks
                                (nthcdr 6 (fn-bs-record-program stage name frame))
                                nil groups capacity)))
                   (fn-sf-record-link-result fileks :ok)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-k6-link-returns-ok (bs file)))
            :in-theory (e/d (fn-bs-record-program fn-bs-run fn-bs-step
                             fn-sf-dispatch)
                            (fn-bs-link fn-bs-lookup fn-sf-record-link-result))))))

(defthm fn-bs-k0-record-attempted-cut-kernel-is-link-observation
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (equal (cdr (nth 10 (fn-bs-run bs ks
                                            (fn-bs-record-program stage name frame)
                                            nil groups capacity)))
                  (fn-sf-record-link-result
                   (fn-sf-record-file-result ks :ok) :ok)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-store-relation-unfolds)
                 (:instance fn-bs-k6-state-next-ino-is-inop)
                 (:instance fn-bs-k0-record-suffix-starts-at-file-cut)
                 (:instance fn-bs-k0-record-file-cut-kernel-is-file-observation)
                 (:instance fn-bs-k6-related-input-file-cut-final-name-absent)
                 (:instance fn-bs-k6-file-cut-source-is-fenced-frame)
                 (:instance fn-bs-k0-record-suffix-link-callback
                            (file (car (nth 5 (fn-bs-run bs ks
                                                           (fn-bs-record-program stage name frame)
                                                           nil groups capacity))))
                            (fileks (cdr (nth 5 (fn-bs-run bs ks
                                                              (fn-bs-record-program stage name frame)
                                                              nil groups capacity))))))
           :in-theory (e/d (fn-bs-record-inputp fn-bs-inop)
                           (fn-bs-run fn-bs-record-program fn-bs-statep
                            fn-bs-store-relation fn-bs-lookup
                            fn-bs-k6-lookup-is-entry-after
                            fn-sf-record-link-result)))))

; The physical half of the same cut has exactly one transaction-directory
; operation.  This is an issued immutable link, not an assumed scanner row.
; Earlier pending transaction operations are ruled out by the input relation;
; staging create/write/fence cannot add one, and the successful link adds
; precisely the fresh inode at the typed candidate's next name.
(defthm fn-bs-k0-attempted-cut-has-one-issued-transaction-link
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (equal
            (fn-bs-ops-for-dir
             (fn-bs-pending
              (car (nth 10 (fn-bs-run bs ks
                                           (fn-bs-record-program stage name frame)
                                           nil groups capacity))))
             :transactions)
            (list (list :set-entry :transactions name (fn-bs-next-ino bs)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k6-related-input-file-cut-has-no-transaction-pending)
                 (:instance fn-bs-k6-related-input-file-cut-final-name-absent)
                 (:instance fn-bs-k6-file-cut-source-is-fenced-frame)
                 (:instance fn-bs-k6-state-next-ino-is-inop)
                 (:instance fn-bs-k6-actual-link-cut-is-file-cut-link)
                 (:instance fn-bs-k6-actual-attempted-cut-keeps-linked-byte-state)
                 (:instance fn-bs-store-relation-unfolds))
           :in-theory (e/d (fn-bs-link fn-bs-ops-for-dir-of-append
                            fn-bs-ops-for-dir fn-bs-record-inputp)
                           (fn-bs-run fn-bs-record-program fn-bs-store-relation
                            fn-bs-statep fn-bs-lookup
                            fn-bs-k6-lookup-is-entry-after)))))

; Local clause helpers for the still-open whole output relation.  The
; staged input cannot carry a root operation (a pending frontier candidate
; would contradict :record-staged), and P-RECORD only touches staging and
; transactions through the attempted cut.
(local
 (defthm fn-bs-k0-record-staged-input-has-no-root-pending
   (implies (and (fn-bs-store-relation bs ks)
                 (equal (fn-sf-phase ks) :record-staged))
            (not (consp (fn-bs-ops-for-dir (fn-bs-pending bs) :root))))
   :rule-classes nil
   :hints (("Goal" :use (fn-bs-store-relation-window-unfolds
                          fn-bs-pending-matches-phase-unfolds)
            :in-theory (enable fn-bs-replay-visiblep
                               fn-sf-frontier-new-visiblep)))))

(local
 (defthm fn-bs-k0-related-input-file-cut-has-no-root-pending
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-record-inputp ks stage name frame)
                 (not (fn-bs-lookup bs :staging stage)))
            (not (consp
                  (fn-bs-ops-for-dir
                   (fn-bs-pending
                    (car (nth 5 (fn-bs-run bs ks
                                           (fn-bs-record-program stage name frame)
                                           nil groups capacity))))
                   :root))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-k0-record-staged-input-has-no-root-pending)
                  (:instance fn-bs-k6-interpreted-record-fence-is-write-fence)
                  (:instance fn-bs-store-relation-unfolds))
            :in-theory (e/d (fn-bs-record-inputp fn-bs-create fn-bs-write
                             fn-bs-fence-file fn-bs-ops-for-dir
                             fn-bs-ops-for-dir-of-append)
                            (fn-bs-run fn-bs-record-program fn-bs-statep
                             fn-bs-store-relation fn-bs-lookup
                             fn-bs-ops-not-for-ino))))))

(local
 (defthm fn-bs-k0-attempted-cut-has-no-root-pending
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-record-inputp ks stage name frame)
                 (not (fn-bs-lookup bs :staging stage)))
            (not (consp
                  (fn-bs-ops-for-dir
                   (fn-bs-pending
                    (car (nth 10 (fn-bs-run bs ks
                                            (fn-bs-record-program stage name frame)
                                            nil groups capacity))))
                   :root))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-k0-related-input-file-cut-has-no-root-pending)
                  (:instance fn-bs-k6-related-input-file-cut-final-name-absent)
                  (:instance fn-bs-k6-file-cut-source-is-fenced-frame)
                  (:instance fn-bs-k6-state-next-ino-is-inop)
                  (:instance fn-bs-k6-actual-link-cut-is-file-cut-link)
                  (:instance fn-bs-k6-actual-attempted-cut-keeps-linked-byte-state)
                  (:instance fn-bs-store-relation-unfolds))
            :in-theory (e/d (fn-bs-link fn-bs-ops-for-dir-of-append
                             fn-bs-ops-for-dir fn-bs-record-inputp)
                            (fn-bs-run fn-bs-record-program fn-bs-store-relation
                             fn-bs-statep fn-bs-lookup
                             fn-bs-k6-lookup-is-entry-after))))))

(local
 (defthm fn-bs-k0-attempted-cut-has-pending-shape
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-record-inputp ks stage name frame)
                 (not (fn-bs-lookup bs :staging stage)))
            (fn-bs-pending-shape-okp
             (car (nth 10 (fn-bs-run bs ks
                                          (fn-bs-record-program stage name frame)
                                          nil groups capacity)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-k0-attempted-cut-has-one-issued-transaction-link)
                  (:instance fn-bs-k0-attempted-cut-has-no-root-pending)
                  (:instance fn-bs-k6-related-attempt-durable-namespace-is-input-namespace)
                  (:instance fn-bs-k6-related-attempt-name-is-next-scanner-name)
                  (:instance fn-bs-k6-related-input-file-cut-final-name-absent)
                  (:instance fn-bs-k6-actual-record-linked-input-has-exact-frame)
                  (:instance fn-bs-k6-actual-attempted-cut-keeps-linked-byte-state)
                  (:instance fn-bs-k6-state-next-ino-is-inop)
                  (:instance fn-bs-store-relation-unfolds))
            :in-theory (e/d (fn-bs-pending-shape-okp fn-bs-record-inputp)
                            (fn-bs-run fn-bs-record-program fn-bs-store-relation
                             fn-bs-statep fn-bs-ops-for-dir fn-bs-lookup
                             fn-bs-k6-lookup-is-entry-after
                             fn-bs-fencedp fn-bs-durable-names))))))

(local
 (defthm fn-bs-k0-durable-state-content-is-durable-content
   (equal (fn-bs-content (fn-bs-durable bs) ino)
          (fn-bs-durable-content bs ino))
   :hints (("Goal" :use ((:instance fn-bs-quiet-content-is-durable-content
                                     (s (fn-bs-durable bs))))
            :in-theory (e/d (fn-bs-durable fn-bs-durable-content)
                            (fn-bs-content fn-bs-view))))))

(local
 (defthm fn-bs-k0-attempted-cut-pending-target-decodes-candidate
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-record-inputp ks stage name frame)
                 (not (fn-bs-lookup bs :staging stage)))
            (equal
             (fn-bs-record-of
              (fn-bs-durable
               (car (nth 10 (fn-bs-run bs ks
                                            (fn-bs-record-program stage name frame)
                                            nil groups capacity))))
              (fn-bs-next-ino bs))
             (fn-sf-record-candidate ks)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-k6-related-input-file-cut-final-name-absent)
                  (:instance fn-bs-k6-actual-record-linked-input-has-exact-frame)
                  (:instance fn-bs-k6-actual-attempted-cut-keeps-linked-byte-state)
                  (:instance fn-bs-store-relation-unfolds)
                  (:instance fn-bs-k0-durable-state-content-is-durable-content
                             (bs (car (nth 10 (fn-bs-run bs ks
                                                            (fn-bs-record-program stage name frame)
                                                            nil groups capacity))))
                             (ino (fn-bs-next-ino bs))))
            :in-theory (e/d (fn-bs-record-inputp fn-bs-record-of)
                            (fn-bs-run fn-bs-record-program fn-bs-store-relation
                             fn-bs-statep fn-bs-record-of-octets
                             fn-bs-fencedp fn-bs-lookup
                             fn-bs-k6-lookup-is-entry-after
                             fn-bs-durable fn-bs-content
                             fn-bs-durable-content))))))

; K0 old-prefix preservation.  The new inode is outside every retained
; transaction target by authority-known and the next-inode bound (proved in
; byte-store-program-invariants).  Each old pathname therefore keeps its
; exact durable octets through create, write, file fence and immutable link;
; the existing decoder agreement theorem lifts that pointwise fact to the
; complete previously durable record list.
(local
 (defthm fn-bs-k0-file-cut-keeps-other-durable-content
   (implies (and (fn-bs-statep bs)
                 (fn-bs-namep stage)
                 (not (fn-bs-lookup bs :staging stage))
                 (true-listp frame)
                 (not (equal other (fn-bs-next-ino bs))))
            (equal (fn-bs-durable-content
                    (car (nth 5 (fn-bs-run bs ks
                                           (fn-bs-record-program stage name frame)
                                           nil groups capacity)))
                    other)
                   (fn-bs-durable-content bs other)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-k6-interpreted-record-fence-is-write-fence)
                  (:instance fn-bs-fence-file-touches-only-its-inode
                             (s (mv-nth 1 (fn-bs-write
                                            (mv-nth 1 (fn-bs-create bs :staging stage :ok))
                                            (fn-bs-next-ino bs) 0 frame :ok)))
                             (ino (fn-bs-next-ino bs))))
            :in-theory (e/d (fn-bs-create fn-bs-write fn-bs-durable-content)
                            (fn-bs-run fn-bs-record-program fn-bs-statep
                             fn-bs-fence-file fn-bs-lookup
                             fn-bs-k6-lookup-is-entry-after))))))

(local
 (defthm fn-bs-k0-link-keeps-durable-content
   (equal (fn-bs-durable-content
           (mv-nth 1 (fn-bs-link bs :staging stage
                                 :transactions name :ok)) other)
          (fn-bs-durable-content bs other))
   :hints (("Goal" :in-theory (enable fn-bs-link fn-bs-durable-content)))))

(local
 (defthm fn-bs-k0-attempted-cut-keeps-other-durable-content
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-record-inputp ks stage name frame)
                 (not (fn-bs-lookup bs :staging stage))
                 (not (equal other (fn-bs-next-ino bs))))
            (equal (fn-bs-durable-content
                    (car (nth 10 (fn-bs-run bs ks
                                            (fn-bs-record-program stage name frame)
                                            nil groups capacity)))
                    other)
                   (fn-bs-durable-content bs other)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-store-relation-unfolds)
                  (:instance fn-bs-k6-state-next-ino-is-inop)
                  (:instance fn-bs-txn-name-is-a-name
                             (n (fn-store-event-sequence (fn-sf-record-candidate ks))))
                  (:instance fn-bs-k6-related-input-file-cut-final-name-absent)
                  (:instance fn-bs-k6-file-cut-source-is-fenced-frame)
                  (:instance fn-bs-k6-actual-link-cut-is-file-cut-link)
                  (:instance fn-bs-k6-actual-attempted-cut-keeps-linked-byte-state)
                  (:instance fn-bs-k0-file-cut-keeps-other-durable-content)
                  (:instance fn-bs-k0-link-keeps-durable-content
                             (bs (car (nth 5 (fn-bs-run bs ks
                                                            (fn-bs-record-program stage name frame)
                                                            nil groups capacity))))))
            :in-theory (e/d (fn-bs-record-inputp)
                            (fn-bs-run fn-bs-record-program fn-bs-store-relation
                             fn-bs-statep fn-bs-durable-content fn-bs-lookup
                             fn-bs-k6-lookup-is-entry-after))))))

(local
 (defthm fn-bs-k0-attempted-durable-transaction-lookup-is-input
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-record-inputp ks stage final frame)
                 (not (fn-bs-lookup bs :staging stage)))
            (equal
             (fn-bs-lookup
              (fn-bs-durable
               (car (nth 10 (fn-bs-run bs ks
                                            (fn-bs-record-program stage final frame)
                                            nil groups capacity))))
              :transactions name)
             (fn-bs-lookup (fn-bs-durable bs) :transactions name)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-k6-related-attempt-durable-namespace-is-input-namespace
                             (name final))
                  (:instance fn-bs-quiet-lookup-is-durable-entry
                             (s (fn-bs-durable bs)) (dir :transactions))
                  (:instance fn-bs-quiet-lookup-is-durable-entry
                             (s (fn-bs-durable
                                 (car (nth 10 (fn-bs-run bs ks
                                                              (fn-bs-record-program stage final frame)
                                                              nil groups capacity)))))
                             (dir :transactions)))
            :in-theory (e/d (fn-bs-durable fn-bs-durable-entry)
                            (fn-bs-run fn-bs-record-program fn-bs-store-relation
                             fn-bs-record-inputp fn-bs-lookup fn-bs-view))))))

(local
 (defthm fn-bs-k0-attempted-durable-transaction-content-is-input
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-record-inputp ks stage final frame)
                 (not (fn-bs-lookup bs :staging stage)))
            (equal
             (fn-bs-content
              (fn-bs-durable
               (car (nth 10 (fn-bs-run bs ks
                                            (fn-bs-record-program stage final frame)
                                            nil groups capacity))))
              (fn-bs-lookup
               (fn-bs-durable
                (car (nth 10 (fn-bs-run bs ks
                                             (fn-bs-record-program stage final frame)
                                             nil groups capacity))))
               :transactions name))
             (fn-bs-content (fn-bs-durable bs)
                            (fn-bs-lookup (fn-bs-durable bs)
                                          :transactions name))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-k0-attempted-durable-transaction-lookup-is-input)
                  (:instance fn-bs-related-allocation-is-not-a-transaction-target
                             (name name))
                  (:instance fn-bs-quiet-lookup-is-durable-entry
                             (s (fn-bs-durable bs)) (dir :transactions))
                  (:instance fn-bs-k0-attempted-cut-keeps-other-durable-content
                             (name final)
                             (other (fn-bs-durable-entry bs :transactions name)))
                  (:instance fn-bs-k0-durable-state-content-is-durable-content
                             (bs bs)
                             (ino (fn-bs-durable-entry bs :transactions name)))
                  (:instance fn-bs-k0-durable-state-content-is-durable-content
                             (bs (car (nth 10 (fn-bs-run bs ks
                                                            (fn-bs-record-program stage final frame)
                                                            nil groups capacity))))
                             (ino (fn-bs-durable-entry bs :transactions name))))
            :in-theory (e/d (fn-bs-durable fn-bs-durable-entry)
                            (fn-bs-run fn-bs-record-program fn-bs-store-relation
                             fn-bs-record-inputp fn-bs-lookup fn-bs-content
                             fn-bs-durable-content))))))

(local
 (defthm fn-bs-k0-attempted-durable-prefix-agrees
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-record-inputp ks stage final frame)
                 (not (fn-bs-lookup bs :staging stage)))
            (fn-bs-txn-prefix-agreesp
             (fn-bs-durable
              (car (nth 10 (fn-bs-run bs ks
                                           (fn-bs-record-program stage final frame)
                                           nil groups capacity))))
             (fn-bs-durable bs) n count))
   :rule-classes nil
   :hints (("Goal" :induct (fn-bs-txn-prefix-agreesp
                             (fn-bs-durable
                              (car (nth 10 (fn-bs-run bs ks
                                                           (fn-bs-record-program stage final frame)
                                                           nil groups capacity))))
                             (fn-bs-durable bs) n count)
            :in-theory (e/d (fn-bs-txn-prefix-agreesp)
                            (fn-bs-run fn-bs-record-program fn-bs-store-relation
                             fn-bs-record-inputp fn-bs-lookup fn-bs-content)))
           ("Subgoal *1/4"
            :use ((:instance fn-bs-k0-attempted-durable-transaction-lookup-is-input
                             (name (fn-bs-txn-name n)))))
           ("Subgoal *1/3"
            :use ((:instance fn-bs-k0-attempted-durable-transaction-content-is-input
                             (name (fn-bs-txn-name n))))))))

(defthm fn-bs-k0-attempted-cut-keeps-old-durable-record-prefix
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (equal
            (fn-bs-durable-records
             (car (nth 10 (fn-bs-run bs ks
                                           (fn-bs-record-program stage name frame)
                                           nil groups capacity))))
            (fn-bs-durable-records bs)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k6-related-attempt-durable-namespace-is-input-namespace)
                 (:instance fn-bs-k0-attempted-durable-prefix-agrees
                            (final name) (n 0)
                            (count (len (fn-bs-durable-names bs :transactions))))
                 (:instance fn-bs-read-records-under-agreement
                            (a (fn-bs-durable
                                (car (nth 10 (fn-bs-run bs ks
                                                             (fn-bs-record-program stage name frame)
                                                             nil groups capacity)))))
                            (b (fn-bs-durable bs)) (n 0)
                            (count (len (fn-bs-durable-names bs :transactions)))))
           :in-theory (e/d (fn-bs-durable-records fn-bs-durable-names)
                           (fn-bs-run fn-bs-record-program fn-bs-store-relation
                            fn-bs-record-inputp fn-bs-read-records
                            fn-bs-txn-prefix-agreesp)))))

; K0 actual pair-10 authority-state and kernel-admissibility clauses.
(defthm fn-bs-k0-record-file-cut-statep
  (implies (and (fn-bs-statep bs)
                (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage))
                (fn-cbor-octet-listp frame))
           (fn-bs-statep
            (car (nth 5 (fn-bs-run bs ks
                                        (fn-bs-record-program stage name frame)
                                        nil groups capacity)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k6-interpreted-record-fence-is-write-fence)
                 (:instance fn-bs-create-preserves-statep
                            (s bs) (dir :staging) (name stage) (outcome :ok))
                 (:instance fn-bs-write-preserves-statep
                            (s (mv-nth 1 (fn-bs-create bs :staging stage :ok)))
                            (ino (fn-bs-next-ino bs)) (offset 0)
                            (octets frame) (outcome :ok))
                 (:instance fn-bs-fence-file-preserves-statep
                            (s (mv-nth 1 (fn-bs-write
                                           (mv-nth 1 (fn-bs-create bs :staging stage :ok))
                                           (fn-bs-next-ino bs) 0 frame :ok)))
                            (ino (fn-bs-next-ino bs))))
           :in-theory (e/d (fn-bs-create fn-bs-write)
                           (fn-bs-run fn-bs-record-program fn-bs-statep
                            fn-bs-fence-file fn-bs-lookup)))))

(defthm fn-bs-k0-attempted-cut-statep
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (fn-bs-statep
            (car (nth 10 (fn-bs-run bs ks
                                         (fn-bs-record-program stage name frame)
                                         nil groups capacity)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-store-relation-unfolds)
                 (:instance fn-bs-k0-record-file-cut-statep)
                 (:instance fn-bs-k6-state-next-ino-is-inop)
                 (:instance fn-bs-txn-name-is-a-name
                            (n (fn-store-event-sequence (fn-sf-record-candidate ks))))
                 (:instance fn-bs-k6-file-cut-source-is-fenced-frame)
                 (:instance fn-bs-k6-related-input-file-cut-final-name-absent)
                 (:instance fn-bs-k6-actual-link-cut-is-file-cut-link)
                 (:instance fn-bs-k6-actual-attempted-cut-keeps-linked-byte-state)
                 (:instance fn-bs-link-preserves-statep
                            (s (car (nth 5 (fn-bs-run bs ks
                                                           (fn-bs-record-program stage name frame)
                                                           nil groups capacity))))
                            (sdir :staging) (sname stage)
                            (ddir :transactions) (dname name) (outcome :ok)))
           :in-theory (e/d (fn-bs-record-inputp)
                           (fn-bs-run fn-bs-record-program fn-bs-statep
                            fn-bs-link fn-bs-lookup fn-bs-store-relation
                            fn-bs-k6-lookup-is-entry-after)))))

(defthm fn-bs-k0-related-allocation-is-not-frontier-target
  (implies (fn-bs-store-relation bs ks)
           (not (equal (fn-bs-next-ino bs)
                       (fn-bs-durable-entry bs :root *fn-bs-scan-frontier-name*))))
  :rule-classes nil
  :hints (("Goal" :use (fn-bs-related-allocation-is-fresh)
           :in-theory (e/d (fn-bs-authority-inode-list fn-bs-durable-entry
                            fn-bs-member-of-append)
                           (fn-bs-store-relation fn-bs-authority-knownp)))))

(defthm fn-bs-k0-attempted-cut-keeps-durable-frontier
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (equal
            (fn-bs-durable-frontier
             (car (nth 10 (fn-bs-run bs ks
                                           (fn-bs-record-program stage name frame)
                                           nil groups capacity))))
            (fn-bs-durable-frontier bs)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-related-allocation-is-not-frontier-target)
                 (:instance fn-bs-k0-attempted-cut-keeps-other-durable-content
                            (other (fn-bs-durable-entry bs :root *fn-bs-scan-frontier-name*)))
                 (:instance fn-bs-k6-related-attempt-durable-namespace-is-input-namespace))
           :in-theory (e/d (fn-bs-durable-frontier fn-bs-durable-entry)
                           (fn-bs-run fn-bs-record-program fn-bs-store-relation
                            fn-bs-record-inputp fn-bs-durable-content)))))

(defthm fn-bs-k0-attempted-cut-kernel-admits-durable-image
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (fn-sf-crash-imagep
            (cdr (nth 10 (fn-bs-run bs ks
                                         (fn-bs-record-program stage name frame)
                                         nil groups capacity)))
            (fn-bs-durable-frontier
             (car (nth 10 (fn-bs-run bs ks
                                          (fn-bs-record-program stage name frame)
                                          nil groups capacity))))
            (fn-bs-durable-records
             (car (nth 10 (fn-bs-run bs ks
                                          (fn-bs-record-program stage name frame)
                                          nil groups capacity))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-record-attempted-cut-kernel-is-link-observation)
                 (:instance fn-bs-k0-attempted-cut-keeps-old-durable-record-prefix)
                 (:instance fn-bs-k0-attempted-cut-keeps-durable-frontier)
                 (:instance fn-bs-store-relation-window-unfolds)
                 (:instance fn-bs-store-relation-unfolds)
                 (:instance fn-sf-record-file-result-preserves-state
                            (s ks) (result :ok))
                 (:instance fn-sf-record-link-result-preserves-state
                            (s (fn-sf-record-file-result ks :ok))
                            (result :ok)))
           :in-theory (e/d (fn-bs-record-inputp fn-bs-replay-visiblep
                            fn-sf-crash-imagep fn-sf-frontier-new-visiblep
                            fn-sf-record-present-visiblep
                            fn-sf-record-file-result fn-sf-record-link-result)
                           (fn-bs-run fn-bs-record-program fn-bs-store-relation
                            fn-bs-durable-records fn-bs-durable-frontier
                            fn-sf-statep)))))

(defthm fn-bs-k0-related-allocation-is-not-config-target
  (implies (fn-bs-store-relation bs ks)
           (not (equal (fn-bs-next-ino bs)
                       (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*))))
  :rule-classes nil
  :hints (("Goal" :use (fn-bs-related-allocation-is-fresh)
           :in-theory (e/d (fn-bs-authority-inode-list fn-bs-durable-entry
                            fn-bs-member-of-append)
                           (fn-bs-store-relation fn-bs-authority-knownp)))))

(defthm fn-bs-k0-attempted-cut-keeps-durable-config
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((at (car (nth 10 (fn-bs-run bs ks
                                              (fn-bs-record-program stage name frame)
                                              nil groups capacity)))))
             (and (equal (fn-bs-durable-entry at :root *fn-bs-scan-config-name*)
                         (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*))
                  (equal (fn-bs-durable-content
                          at (fn-bs-durable-entry at :root *fn-bs-scan-config-name*))
                         (fn-bs-durable-content
                          bs (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-related-allocation-is-not-config-target)
                 (:instance fn-bs-k0-attempted-cut-keeps-other-durable-content
                            (other (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*)))
                 (:instance fn-bs-k6-related-attempt-durable-namespace-is-input-namespace))
           :in-theory (e/d (fn-bs-durable-entry)
                           (fn-bs-run fn-bs-record-program fn-bs-store-relation
                            fn-bs-record-inputp fn-bs-durable-content)))))

; The fold is independent of the number and content of write operations.
; This is the link between O_EXCL's freshly allocated inode and both the
; empty and nonempty write-all branches in the actual P-RECORD program.
(local
 (defthm fn-bs-k0-apply-writes-preserves-known-inode
   (implies (and (natp key)
                 (alistp inodes)
                 (assoc-equal key inodes))
            (consp (assoc-equal key (fn-bs-apply-writes inodes ops))))
   :hints (("Goal" :induct (fn-bs-apply-writes inodes ops)
            :in-theory (e/d (fn-bs-apply-writes
                             fn-bs-assoc-of-put-assoc-iff
                             fn-bs-alistp-of-put-assoc)
                            (fn-bs-splice fn-bs-take))))))

(local
 (defthm fn-bs-k0-new-inode-survives-write-fold
   (implies (and (natp key) (alistp inodes))
            (consp (assoc-equal
                    key
                    (fn-bs-apply-writes (cons (cons key nil) inodes) ops))))
   :hints (("Goal"
            :use ((:instance fn-bs-k0-apply-writes-preserves-known-inode
                             (inodes (cons (cons key nil) inodes))))
            :in-theory (e/d (assoc-equal alistp)
                            (fn-bs-apply-writes))))))

(local
 (defthm fn-bs-k0-file-cut-has-new-inode
   (implies (and (fn-bs-statep bs) (fn-bs-namep stage)
                 (not (fn-bs-lookup bs :staging stage))
                 (true-listp frame))
            (consp (assoc-equal
                    (fn-bs-next-ino bs)
                    (fn-bs-inodes
                     (car (nth 5 (fn-bs-run bs ks
                                            (fn-bs-record-program stage name frame)
                                            nil groups capacity)))))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-k6-interpreted-record-fence-is-write-fence)
                  (:instance fn-bs-inode-tablep-implies-alistp
                             (x (fn-bs-inodes bs))))
            :in-theory (e/d (fn-bs-create fn-bs-write fn-bs-fence-file
                             fn-bs-apply-ops-inodes-are-apply-writes
                             fn-bs-statep
                             fn-bs-k0-new-inode-survives-write-fold)
                            (fn-bs-run fn-bs-record-program
                             fn-bs-lookup fn-bs-apply-ops))))))

(local
 (defthm fn-bs-k0-link-keeps-inode-entry
   (equal (assoc-equal other
                       (fn-bs-inodes (mv-nth 1 (fn-bs-link bs :staging stage
                                                       :transactions name :ok))))
          (assoc-equal other (fn-bs-inodes bs)))
   :hints (("Goal" :in-theory (enable fn-bs-link)))))

(local
 (defthm fn-bs-k0-link-cut-has-new-inode
   (implies
    (and (fn-bs-statep bs) (fn-bs-namep stage) (fn-bs-namep name)
         (not (fn-bs-lookup bs :staging stage)) (true-listp frame)
         (not (fn-bs-lookup
               (car (nth 5 (fn-bs-run bs ks
                                          (fn-bs-record-program stage name frame)
                                          nil groups capacity)))
               :transactions name)))
    (consp (assoc-equal
            (fn-bs-next-ino bs)
            (fn-bs-inodes
             (car (nth 8 (fn-bs-run bs ks
                                    (fn-bs-record-program stage name frame)
                                    nil groups capacity)))))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-k0-file-cut-has-new-inode)
                  (:instance fn-bs-k6-actual-link-cut-is-file-cut-link)
                  (:instance fn-bs-k0-link-keeps-inode-entry
                             (bs (car (nth 5 (fn-bs-run bs ks
                                                    (fn-bs-record-program stage name frame)
                                                    nil groups capacity))))
                             (other (fn-bs-next-ino bs))))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn-bs-k0-related-input-enables-link-cut
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-record-inputp ks stage name frame)
                 (not (fn-bs-lookup bs :staging stage)))
            (and (fn-bs-statep bs)
                 (fn-bs-namep stage)
                 (fn-bs-namep name)
                 (true-listp frame)
                 (not (fn-bs-lookup
                       (car (nth 5 (fn-bs-run bs ks
                                                  (fn-bs-record-program stage name frame)
                                                  nil groups capacity)))
                       :transactions name))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use (fn-bs-store-relation-unfolds
                  fn-bs-k6-related-input-file-cut-final-name-absent
                  (:instance fn-bs-txn-name-is-a-name
                             (n (fn-store-event-sequence
                                 (fn-sf-record-candidate ks))))
                  (:instance fn-cbor-octet-listp-implies-true-listp
                             (xs frame)))
            :in-theory (union-theories '(fn-bs-record-inputp)
                                       (theory 'minimal-theory))))))

(defthm fn-bs-k0-attempted-cut-has-new-inode
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (consp (assoc-equal
                   (fn-bs-next-ino bs)
                   (fn-bs-inodes
                    (car (nth 10 (fn-bs-run bs ks
                                           (fn-bs-record-program stage name frame)
                                           nil groups capacity)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-related-input-enables-link-cut)
                 (:instance fn-bs-k0-link-cut-has-new-inode)
                 (:instance fn-bs-k6-actual-attempted-cut-keeps-linked-byte-state))
           :in-theory (theory 'minimal-theory))))

; K0 authority-list shape and old inode-table preservation.
(local
 (defthm fn-bs-k0-pending-entry-targets-of-append
  (equal (fn-bs-pending-entry-targets (append a b))
         (append (fn-bs-pending-entry-targets a)
                 (fn-bs-pending-entry-targets b)))
  :hints (("Goal" :induct (append a b)
           :in-theory (enable fn-bs-pending-entry-targets))))
)

(local
 (defthm fn-bs-k0-pending-entry-targets-of-inode-filter
  (equal (fn-bs-pending-entry-targets (fn-bs-ops-not-for-ino ops ino))
         (fn-bs-pending-entry-targets ops))
  :hints (("Goal" :induct (fn-bs-ops-not-for-ino ops ino)
           :in-theory (enable fn-bs-ops-not-for-ino
                              fn-bs-pending-entry-targets))))
)

(local
 (defthm fn-bs-k0-file-cut-keeps-pending-authority-targets
  (implies (and (fn-bs-statep bs) (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage))
                (true-listp frame))
           (equal (fn-bs-pending-entry-targets
                   (fn-bs-pending
                    (car (nth 5 (fn-bs-run bs ks
                                           (fn-bs-record-program stage name frame)
                                           nil groups capacity)))))
                  (fn-bs-pending-entry-targets (fn-bs-pending bs))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k6-interpreted-record-fence-is-write-fence))
           :in-theory (e/d (fn-bs-create fn-bs-write fn-bs-fence-file
                            fn-bs-pending-entry-targets)
                           (fn-bs-run fn-bs-record-program fn-bs-statep
                            fn-bs-lookup fn-bs-ops-not-for-ino)))))
)

(local
 (defthm fn-bs-k0-append-associative
  (equal (append (append x y) z) (append x (append y z))))
)

(defthm fn-bs-k0-attempted-cut-authority-targets-are-old-plus-new
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (equal
            (fn-bs-authority-inode-list
             (car (nth 10 (fn-bs-run bs ks
                                           (fn-bs-record-program stage name frame)
                                           nil groups capacity))))
            (append (fn-bs-authority-inode-list bs)
                    (list (fn-bs-next-ino bs)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-store-relation-unfolds)
                 (:instance fn-bs-k0-file-cut-keeps-pending-authority-targets)
                 (:instance fn-bs-k6-file-cut-dirs-are-input-dirs)
                 (:instance fn-bs-k6-related-input-file-cut-final-name-absent)
                 (:instance fn-bs-k6-file-cut-source-is-fenced-frame)
                 (:instance fn-bs-k6-state-next-ino-is-inop)
                 (:instance fn-bs-k6-actual-link-cut-is-file-cut-link)
                 (:instance fn-bs-k6-actual-attempted-cut-keeps-linked-byte-state))
           :in-theory (e/d (fn-bs-authority-inode-list fn-bs-pending-entry-targets
                            fn-bs-durable-entry fn-bs-link
                            fn-bs-k0-pending-entry-targets-of-append)
                           (fn-bs-run fn-bs-record-program fn-bs-store-relation
                            fn-bs-statep fn-bs-lookup
                            fn-bs-k6-lookup-is-entry-after)))))

(local
 (defthm fn-bs-k0-other-inode-has-no-selected-write
  (implies (not (equal other ino))
           (equal (fn-bs-ops-for-ino (fn-bs-ops-for-ino ops ino) other) nil))
  :hints (("Goal" :induct (fn-bs-ops-for-ino ops ino)
           :in-theory (enable fn-bs-ops-for-ino))))
)

(local
 (defthm fn-bs-k0-fence-file-keeps-other-inode-entry
  (implies (not (equal other ino))
           (equal (assoc-equal other (fn-bs-inodes (fn-bs-fence-file bs ino)))
                  (assoc-equal other (fn-bs-inodes bs))))
  :hints (("Goal" :use ((:instance fn-bs-k0-other-inode-has-no-selected-write
                                    (ops (fn-bs-pending bs)))
                         (:instance fn-bs-apply-writes-keeps-quiet-ino
                                    (ops (fn-bs-ops-for-ino (fn-bs-pending bs) ino))
                                    (inodes (fn-bs-inodes bs)) (ino other)))
           :in-theory (e/d (fn-bs-fence-file
                            fn-bs-apply-ops-inodes-are-apply-writes)
                           (fn-bs-apply-ops fn-bs-ops-for-ino)))))
)

(local
 (defthm fn-bs-k0-file-cut-keeps-other-inode-entry
  (implies (and (fn-bs-statep bs) (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage))
                (true-listp frame)
                (not (equal other (fn-bs-next-ino bs))))
           (equal (assoc-equal other
                               (fn-bs-inodes
                                (car (nth 5 (fn-bs-run bs ks
                                                       (fn-bs-record-program stage name frame)
                                                       nil groups capacity)))))
                  (assoc-equal other (fn-bs-inodes bs))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k6-interpreted-record-fence-is-write-fence)
                 (:instance fn-bs-k0-fence-file-keeps-other-inode-entry
                            (bs (mv-nth 1 (fn-bs-write
                                           (mv-nth 1 (fn-bs-create bs :staging stage :ok))
                                           (fn-bs-next-ino bs) 0 frame :ok)))
                            (ino (fn-bs-next-ino bs))))
           :in-theory (e/d (fn-bs-create fn-bs-write)
                           (fn-bs-run fn-bs-record-program fn-bs-statep
                            fn-bs-fence-file fn-bs-lookup
                            fn-bs-k6-lookup-is-entry-after)))))
)

(defthm fn-bs-k0-attempted-cut-keeps-other-inode-entry
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage))
                (not (equal other (fn-bs-next-ino bs))))
           (equal (assoc-equal other
                               (fn-bs-inodes
                                (car (nth 10 (fn-bs-run bs ks
                                                        (fn-bs-record-program stage name frame)
                                                        nil groups capacity)))))
                  (assoc-equal other (fn-bs-inodes bs))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-store-relation-unfolds)
                 (:instance fn-bs-k6-state-next-ino-is-inop)
                 (:instance fn-bs-txn-name-is-a-name
                            (n (fn-store-event-sequence (fn-sf-record-candidate ks))))
                 (:instance fn-bs-k6-related-input-file-cut-final-name-absent)
                 (:instance fn-bs-k6-file-cut-source-is-fenced-frame)
                 (:instance fn-bs-k6-actual-link-cut-is-file-cut-link)
                 (:instance fn-bs-k6-actual-attempted-cut-keeps-linked-byte-state)
                 (:instance fn-bs-k0-file-cut-keeps-other-inode-entry)
                 (:instance fn-bs-k0-link-keeps-inode-entry
                            (bs (car (nth 5 (fn-bs-run bs ks
                                                           (fn-bs-record-program stage name frame)
                                                           nil groups capacity))))))
           :in-theory (e/d (fn-bs-record-inputp)
                           (fn-bs-run fn-bs-record-program fn-bs-store-relation
                            fn-bs-statep fn-bs-lookup
                            fn-bs-k6-lookup-is-entry-after)))))

; K0 attempted-cut authority existence and file-fence preservation.
(local (defthm fn-bs-k0-attempted-cut-keeps-known-list
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage))
                (fn-bs-inode-list-knownp bs xs)
                (not (member-equal (fn-bs-next-ino bs) xs)))
           (fn-bs-inode-list-knownp
            (car (nth 10 (fn-bs-run bs ks
                                    (fn-bs-record-program stage name frame)
                                    nil groups capacity))) xs))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bs-inode-list-knownp bs xs)
           :in-theory (e/d (fn-bs-inode-list-knownp)
                           (fn-bs-run fn-bs-record-program
                            fn-bs-store-relation fn-bs-statep
                            fn-bs-record-inputp fn-bs-lookup)))
          ("Subgoal *1/1''"
           :use ((:instance fn-bs-k0-attempted-cut-keeps-other-inode-entry
                            (other (car xs))))))))

(local (defthm fn-bs-k0-inode-list-knownp-append
  (equal (fn-bs-inode-list-knownp bs (append x y))
         (and (fn-bs-inode-list-knownp bs x)
              (fn-bs-inode-list-knownp bs y)))
  :hints (("Goal" :induct (append x y)
           :in-theory (enable fn-bs-inode-list-knownp)))))

(defthm fn-bs-k0-attempted-cut-authority-known
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (fn-bs-authority-knownp
            (car (nth 10 (fn-bs-run bs ks
                                    (fn-bs-record-program stage name frame)
                                    nil groups capacity)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-related-allocation-is-fresh)
                 (:instance fn-bs-k0-attempted-cut-authority-targets-are-old-plus-new)
                 (:instance fn-bs-k0-attempted-cut-keeps-known-list
                            (xs (fn-bs-authority-inode-list bs)))
                 (:instance fn-bs-k0-attempted-cut-has-new-inode))
           :in-theory (e/d (fn-bs-store-relation fn-bs-authority-knownp
                            fn-bs-inode-list-knownp
                            fn-bs-k0-inode-list-knownp-append)
                           (fn-bs-run fn-bs-record-program fn-bs-statep
                            fn-bs-record-inputp fn-bs-lookup
                            fn-bs-authority-fencedp fn-bs-durable-records
                            fn-bs-replay-matches-scan
                            fn-bs-pending-matches-phase fn-sf-crash-imagep)))))

(local (defthm fn-bs-k0-other-inode-filter-preserves-selected-ops
  (implies (not (equal other ino))
           (equal (fn-bs-ops-for-ino (fn-bs-ops-not-for-ino ops ino) other)
                  (fn-bs-ops-for-ino ops other)))
  :hints (("Goal" :induct (fn-bs-ops-not-for-ino ops ino)
           :in-theory (enable fn-bs-ops-not-for-ino fn-bs-ops-for-ino)))))

(local (defthm fn-bs-k0-file-cut-keeps-other-fenced
  (implies (and (fn-bs-statep bs) (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage))
                (true-listp frame)
                (not (equal other (fn-bs-next-ino bs)))
                (fn-bs-fencedp bs other))
           (fn-bs-fencedp
            (car (nth 5 (fn-bs-run bs ks
                                   (fn-bs-record-program stage name frame)
                                   nil groups capacity))) other))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k6-interpreted-record-fence-is-write-fence))
           :in-theory (e/d (fn-bs-create fn-bs-write fn-bs-fence-file
                            fn-bs-fencedp fn-bs-ops-for-ino-of-append
                            fn-bs-k0-other-inode-filter-preserves-selected-ops)
                           (fn-bs-run fn-bs-record-program fn-bs-statep
                            fn-bs-lookup fn-bs-k6-lookup-is-entry-after))))))

(defthm fn-bs-k0-attempted-cut-keeps-other-fenced
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage))
                (not (equal other (fn-bs-next-ino bs)))
                (fn-bs-fencedp bs other))
           (fn-bs-fencedp
            (car (nth 10 (fn-bs-run bs ks
                                    (fn-bs-record-program stage name frame)
                                    nil groups capacity))) other))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-store-relation-unfolds)
                 (:instance fn-bs-k6-state-next-ino-is-inop)
                 (:instance fn-bs-txn-name-is-a-name
                            (n (fn-store-event-sequence (fn-sf-record-candidate ks))))
                 (:instance fn-bs-k6-related-input-file-cut-final-name-absent)
                 (:instance fn-bs-k6-file-cut-source-is-fenced-frame)
                 (:instance fn-bs-k6-actual-link-cut-is-file-cut-link)
                 (:instance fn-bs-k6-actual-attempted-cut-keeps-linked-byte-state)
                 (:instance fn-bs-k0-file-cut-keeps-other-fenced))
           :in-theory (e/d (fn-bs-record-inputp fn-bs-fencedp
                            fn-bs-link fn-bs-ops-for-ino-of-append)
                           (fn-bs-run fn-bs-record-program fn-bs-store-relation
                            fn-bs-statep fn-bs-lookup
                            fn-bs-k6-lookup-is-entry-after)))))

(local (defthm fn-bs-k0-attempted-cut-new-target-fenced
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (fn-bs-fencedp
            (car (nth 10 (fn-bs-run bs ks
                                    (fn-bs-record-program stage name frame)
                                    nil groups capacity)))
            (fn-bs-next-ino bs)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-store-relation-unfolds)
                 (:instance fn-bs-k6-actual-record-linked-cut-has-exact-frame)
                 (:instance fn-bs-k6-related-input-file-cut-final-name-absent)
                 (:instance fn-bs-k6-actual-attempted-cut-keeps-linked-byte-state))
           :in-theory (e/d (fn-bs-record-inputp)
                           (fn-bs-run fn-bs-record-program fn-bs-store-relation
                            fn-bs-statep fn-bs-lookup fn-bs-fencedp
                            fn-bs-k6-lookup-is-entry-after))))))

(local (defthm fn-bs-k0-attempted-cut-keeps-fenced-list
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage))
                (fn-bs-all-fencedp bs xs)
                (not (member-equal (fn-bs-next-ino bs) xs)))
           (fn-bs-all-fencedp
            (car (nth 10 (fn-bs-run bs ks
                                    (fn-bs-record-program stage name frame)
                                    nil groups capacity))) xs))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bs-all-fencedp bs xs)
           :in-theory (e/d (fn-bs-all-fencedp)
                           (fn-bs-run fn-bs-record-program
                            fn-bs-store-relation fn-bs-statep
                            fn-bs-record-inputp fn-bs-lookup)))
          ("Subgoal *1/1''"
           :use ((:instance fn-bs-k0-attempted-cut-keeps-other-fenced
                            (other (car xs))))))))

(local (defthm fn-bs-k0-all-fencedp-append
  (equal (fn-bs-all-fencedp bs (append x y))
         (and (fn-bs-all-fencedp bs x)
              (fn-bs-all-fencedp bs y)))
  :hints (("Goal" :induct (append x y)
           :in-theory (enable fn-bs-all-fencedp)))))

(defthm fn-bs-k0-attempted-cut-authority-fenced
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (fn-bs-authority-fencedp
            (car (nth 10 (fn-bs-run bs ks
                                    (fn-bs-record-program stage name frame)
                                    nil groups capacity)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-related-allocation-is-fresh)
                 (:instance fn-bs-k0-attempted-cut-authority-targets-are-old-plus-new)
                 (:instance fn-bs-k0-attempted-cut-keeps-fenced-list
                            (xs (fn-bs-authority-inode-list bs)))
                 (:instance fn-bs-k0-attempted-cut-new-target-fenced))
           :in-theory (e/d (fn-bs-store-relation fn-bs-authority-fencedp
                            fn-bs-all-fencedp fn-bs-k0-all-fencedp-append)
                           (fn-bs-run fn-bs-record-program fn-bs-statep
                            fn-bs-record-inputp fn-bs-lookup
                            fn-bs-authority-knownp fn-bs-durable-records
                            fn-bs-replay-matches-scan
                            fn-bs-pending-matches-phase fn-sf-crash-imagep)))))

; K0: the actual attempted Store record cut re-establishes the full relation.
(local (defthm fn-bs-k0-staged-input-durable-records-match
  (implies (and (fn-bs-store-relation bs ks)
                (equal (fn-sf-phase ks) :record-staged))
           (equal (fn-bs-durable-records bs) (fn-sf-records ks)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-store-relation-window-unfolds))
           :in-theory (e/d (fn-bs-replay-visiblep fn-sf-crash-imagep
                            fn-sf-record-present-visiblep)
                           (fn-bs-store-relation fn-bs-durable-records
                            fn-bs-durable-frontier fn-bs-pending-matches-phase
                            fn-sf-statep))))))

(defthm fn-bs-k0-record-attempted-cut-establishes-relation
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (fn-bs-store-relation
            (car (nth 10 (fn-bs-run bs ks
                                    (fn-bs-record-program stage name frame)
                                    nil groups capacity)))
            (cdr (nth 10 (fn-bs-run bs ks
                                    (fn-bs-record-program stage name frame)
                                    nil groups capacity)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-store-relation-unfolds)
                 (:instance fn-bs-k0-staged-input-durable-records-match)
                 (:instance fn-bs-store-relation-window-unfolds)
                 (:instance fn-bs-pending-matches-phase-unfolds)
                 (:instance fn-bs-k0-attempted-cut-keeps-durable-frontier)
                 (:instance fn-bs-k0-attempted-cut-statep)
                 (:instance fn-bs-k0-attempted-cut-keeps-durable-config)
                 (:instance fn-bs-k6-related-attempt-durable-namespace-is-input-namespace)
                 (:instance fn-bs-k0-attempted-cut-keeps-old-durable-record-prefix)
                 (:instance fn-bs-k0-attempted-cut-kernel-admits-durable-image)
                 (:instance fn-bs-k0-attempted-cut-has-pending-shape)
                 (:instance fn-bs-k0-attempted-cut-has-one-issued-transaction-link)
                 (:instance fn-bs-k0-attempted-cut-has-no-root-pending)
                 (:instance fn-bs-k0-attempted-cut-pending-target-decodes-candidate)
                 (:instance fn-bs-k0-attempted-cut-authority-known)
                 (:instance fn-bs-k0-attempted-cut-authority-fenced)
                 (:instance fn-bs-k0-record-attempted-cut-kernel-is-link-observation)
                 (:instance fn-sf-record-file-result-preserves-state (s ks) (result :ok))
                 (:instance fn-sf-record-link-result-preserves-state
                            (s (fn-sf-record-file-result ks :ok)) (result :ok)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-contiguous-namesp
                            fn-bs-durable-entry fn-bs-durable-names
                            fn-bs-pending-matches-phase
                            fn-bs-replay-visiblep fn-sf-record-present-visiblep
                            fn-sf-record-file-result fn-sf-record-link-result
                            fn-bs-record-inputp)
                           (fn-bs-run fn-bs-record-program fn-bs-statep
                            fn-bs-lookup fn-bs-durable-records
                            fn-bs-authority-knownp fn-bs-authority-fencedp
                            fn-sf-statep fn-sf-crash-imagep
                            fn-bs-fencedp fn-bs-pending-shape-okp)))))

; K0 served article call arguments: ACL2 codec, frame, and filename.
(local (defthm fn-bs-k0-host-frame-decodes-event
  (implies (and (fn-cbor-octet-listp payload)
                (fn-cbor-at-mostp payload *fn-frame-max-store-payload*)
                (equal (fn-store-event-decode-exact payload)
                       (list :ok event))
                (fn-store-event-p event))
           (equal
            (fn-bs-record-of-octets
             (append (fn-frame-store-protected payload)
                     (fn-frame-trailer (fn-frame-store-protected payload))))
            event))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-at-mostp-bounds-len
                            (xs payload) (bound *fn-frame-max-store-payload*))
                 (:instance fn-frame-store-protected-plus-trailer-is-seal
                            (record payload))
                 (:instance fn-frame-decode-is-open
                            (octets (fn-frame-seal *fn-frame-magic-store*
                                                   *fn-frame-version*
                                                   *fn-frame-store-kind* payload))
                            (digest (fn-frame-digest
                                     (fn-frame-protected-prefix
                                      (fn-frame-seal *fn-frame-magic-store*
                                                     *fn-frame-version*
                                                     *fn-frame-store-kind* payload))))
                            (max-payload *fn-frame-max-store-payload*))
                 (:instance fn-frame-open-of-seal
                            (magic *fn-frame-magic-store*)
                            (version *fn-frame-version*)
                            (kind *fn-frame-store-kind*)
                            (payload payload)
                            (max-payload *fn-frame-max-store-payload*)))
           :in-theory (e/d (fn-bs-record-of-octets fn-frame-store-decode
                            fn-frame-result-okp fn-frame-result-payload
                            fn-frame-result-magic fn-frame-result-version
                            fn-frame-result-kind
                            fn-frame-ok fn-frame-inputp)
                           (fn-frame-seal fn-frame-protected-prefix
                            fn-store-event-decode-exact fn-store-event-p))))))

(local (defthm fn-bs-k0-article-event-round-trip
  (implies (fn-record-p record)
           (equal (fn-store-event-decode-exact
                   (fn-store-event-encode record))
                  (list :ok record)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-record-round-trip))
           :in-theory (e/d (fn-store-event-encode
                            fn-store-event-decode-exact
                            fn-record-result-okp)
                           (fn-store-retention-event-decode-exact
                            fn-stxe-decode-exact fn-stxk-decode-exact
                            fn-stxa-decode-exact))))))

(local (defthm fn-bs-k0-article-encoding-fits-frame
  (implies (fn-record-p record)
           (and (fn-cbor-octet-listp (fn-store-event-encode record))
                (fn-cbor-at-mostp (fn-store-event-encode record)
                                  *fn-frame-max-store-payload*)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-record-encode-shape)
                 (:instance fn-record-encode-length)
                 (:instance fn-cbor-at-mostp-from-length
                            (xs (fn-record-encode record))
                            (bound *fn-frame-max-store-payload*)))
           :in-theory (e/d (fn-store-event-encode)
                           (fn-record-p fn-cbor-at-mostp))))))

(local (defthm fn-bs-k0-host-frame-is-octets
  (implies (and (fn-cbor-octet-listp payload)
                (fn-cbor-at-mostp payload *fn-frame-max-store-payload*))
           (fn-cbor-octet-listp
            (append (fn-frame-store-protected payload)
                    (fn-frame-trailer (fn-frame-store-protected payload)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-store-protected-plus-trailer-is-seal
                            (record payload))
                 (:instance fn-frame-at-mostp-bounds-len
                            (xs payload) (bound *fn-frame-max-store-payload*)))
           :in-theory (e/d (fn-frame-seal fn-frame-encode
                            fn-frame-protected fn-frame-header)
                           (fn-frame-store-protected fn-frame-trailer))))))

(defthm fn-bs-k0-article-host-arguments-are-typed-record-input
  (implies (and (fn-record-p record)
                (equal (fn-sf-phase ks) :record-staged)
                (equal (fn-sf-record-candidate ks) record)
                (fn-bs-namep stage))
           (fn-bs-record-inputp
            ks stage
            (fn-bs-txn-name (fn-store-event-sequence record))
            (append
             (fn-frame-store-protected (fn-store-event-encode record))
             (fn-frame-trailer
              (fn-frame-store-protected (fn-store-event-encode record))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-article-encoding-fits-frame)
                 (:instance fn-bs-k0-article-event-round-trip)
                 (:instance fn-bs-k0-host-frame-is-octets
                            (payload (fn-store-event-encode record)))
                 (:instance fn-bs-k0-host-frame-decodes-event
                            (payload (fn-store-event-encode record))
                            (event record)))
           :in-theory (e/d (fn-bs-record-inputp)
                           (fn-bs-record-of-octets fn-store-event-encode
                            fn-store-event-decode-exact fn-record-p
                            fn-frame-store-protected fn-frame-trailer)))))

(defthm fn-bs-k0-article-host-arguments-reach-related-attempted-cut
  (implies
   (and (fn-bs-store-relation bs ks)
        (fn-record-p record)
        (equal (fn-sf-phase ks) :record-staged)
        (equal (fn-sf-record-candidate ks) record)
        (fn-bs-namep stage)
        (not (fn-bs-lookup bs :staging stage)))
   (let ((frame (append
                 (fn-frame-store-protected (fn-store-event-encode record))
                 (fn-frame-trailer
                  (fn-frame-store-protected (fn-store-event-encode record)))))
         (name (fn-bs-txn-name (fn-store-event-sequence record))))
     (fn-bs-store-relation
      (car (nth 10 (fn-bs-run bs ks
                              (fn-bs-record-program stage name frame)
                              nil groups capacity)))
      (cdr (nth 10 (fn-bs-run bs ks
                              (fn-bs-record-program stage name frame)
                              nil groups capacity))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-article-host-arguments-are-typed-record-input)
                 (:instance fn-bs-k0-record-attempted-cut-establishes-relation
                            (name (fn-bs-txn-name (fn-store-event-sequence record)))
                            (frame (append
                                    (fn-frame-store-protected
                                     (fn-store-event-encode record))
                                    (fn-frame-trailer
                                     (fn-frame-store-protected
                                      (fn-store-event-encode record)))))))
           :in-theory (theory 'minimal-theory))))

; K0 call-entry handoff: ACL2 preparation writes no byte state.
(defthm fn-bs-k0-record-prepare-preserves-relation
  (implies (fn-bs-store-relation bs ks)
           (fn-bs-store-relation
            bs (fn-sf-prepare-record ks record groups capacity)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-store-relation-unfolds)
                 (:instance fn-sf-prepare-record-preserves-state (s ks))
                 (:instance fn-bs-store-relation-window-unfolds))
           :in-theory (e/d (fn-bs-store-relation fn-sf-prepare-record
                            fn-sf-crash-imagep fn-bs-replay-visiblep
                            fn-bs-pending-matches-phase
                            fn-sf-frontier-new-visiblep
                            fn-sf-record-present-visiblep)
                           (fn-bs-statep fn-sf-statep fn-bs-durable-records
                            fn-bs-durable-frontier fn-bs-authority-fencedp
                            fn-bs-authority-knownp fn-sf-history-recoverablep
                            fn-sf-candidatep)))))

(include-book "store-node")

(defthm fn-bs-k0-node-article-prepare-preserves-relation
  (implies (fn-bs-store-relation bs (fn-sn-files s))
           (fn-bs-store-relation
            bs (fn-sn-files (fn-sn-prepare s record))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-record-prepare-preserves-relation
                            (ks (fn-sn-files s))
                            (groups (fn-sn-groups s))
                            (capacity (fn-sn-capacity s))))
           :in-theory (e/d (fn-sn-prepare)
                           (fn-sn-update fn-sn-make-v6
                            fn-sn-statep fn-node-statep
                            fn-sn-prepare-node fn-sn-record-bindsp
                            fn-sf-prepare-record fn-bs-store-relation)))))

; K0 served article: reserved node prepare to actual P-RECORD pair 10.
(local (defthm fn-bs-k0-node-article-prepare-binds-candidate
  (implies (and (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                (equal (fn-sf-phase (fn-sn-files (fn-sn-prepare s record)))
                       :record-staged))
           (equal (fn-sf-record-candidate
                   (fn-sn-files (fn-sn-prepare s record)))
                  record))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-sn-prepare
                            fn-sf-prepare-record)
                           (fn-sn-update fn-sn-make-v6
                            fn-sn-statep fn-node-statep
                            fn-sn-prepare-node fn-sn-record-bindsp
                            fn-sf-history-recoverablep fn-sf-candidatep))))))

(local (defthm fn-bs-k0-node-article-prepare-success-has-recordp
  (implies (and (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                (equal (fn-sf-phase (fn-sn-files (fn-sn-prepare s record)))
                       :record-staged))
           (fn-record-p record))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-sn-prepare
                            fn-sf-prepare-record)
                           (fn-sn-update fn-sn-make-v6
                            fn-sn-statep fn-node-statep
                            fn-sn-prepare-node fn-sn-record-bindsp
                            fn-sf-history-recoverablep fn-sf-candidatep))))))

(defthm fn-bs-k0-served-article-prepare-to-attempted-relation
  (implies
   (and (fn-bs-store-relation bs (fn-sn-files s))
        (equal (fn-sf-phase (fn-sn-files s)) :reserved)
        (equal (fn-sf-phase (fn-sn-files (fn-sn-prepare s record)))
               :record-staged)
        (fn-bs-namep stage)
        (not (fn-bs-lookup bs :staging stage)))
   (let* ((ks (fn-sn-files (fn-sn-prepare s record)))
          (frame (append
                  (fn-frame-store-protected (fn-store-event-encode record))
                  (fn-frame-trailer
                   (fn-frame-store-protected (fn-store-event-encode record)))))
          (name (fn-bs-txn-name (fn-store-event-sequence record))))
     (fn-bs-store-relation
      (car (nth 10 (fn-bs-run bs ks
                              (fn-bs-record-program stage name frame)
                              nil groups capacity)))
      (cdr (nth 10 (fn-bs-run bs ks
                              (fn-bs-record-program stage name frame)
                              nil groups capacity))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-node-article-prepare-preserves-relation)
                 (:instance fn-bs-k0-node-article-prepare-binds-candidate)
                 (:instance fn-bs-k0-node-article-prepare-success-has-recordp)
                 (:instance fn-bs-k0-article-host-arguments-reach-related-attempted-cut
                            (ks (fn-sn-files (fn-sn-prepare s record)))))
           :in-theory (theory 'minimal-theory))))

; K0 allocator entry.  host/native/io.lisp:fnn-advance-frontier calls
; fn-store-metadata-frontier-next and fn-store-metadata-frontier-frame.
; host/store-host.lisp routes the frame/decode wrappers through the public
; constrained functions, whose checked defattach is the concrete codec.
; This theorem checks the attached implementation's separate byte grammar.
(defthm fn-bs-k0-host-frontier-frame-is-concrete-codec
  (implies (and (natp n) (<= n *fn-cbor-max-uint*))
           (and (fn-cbor-octet-listp (fn-bs-frontier-encode-impl n))
                (equal (fn-bs-frontier-decode-impl
                        (fn-bs-frontier-encode-impl n)) n)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bs-frontier-seal-octet-listp)
                 (:instance fn-bs-frontier-impl-round-trip))
           :in-theory (e/d (fn-bs-frontier-encode-impl)
                           (fn-bs-frontier-decode-impl
                            fn-bs-frontier-seal-octet-listp
                            fn-bs-frontier-impl-round-trip)))))

(defthm fn-bs-k0-host-frontier-arguments-are-typed-input
  (implies
   (and (fn-sf-statep ks)
        (equal (fn-sf-phase ks) :ready)
        (fn-bs-namep stage)
        (equal current (fn-sf-frontier ks))
        (equal next (fn-bs-frontier-next current))
        next
        ; fnn-metadata-frontier-frame checks this before I/O.  The abstract
        ; encoder constraint provides round-trip but no octet-list theorem.
        (fn-cbor-octet-listp (fn-bs-frontier-encode next)))
   (fn-bs-frontier-inputp
    ks stage (fn-bs-frontier-encode next)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bs-frontier-round-trip (n next))
                 (:instance fn-bs-frontier-next-is-successor (n current)))
           :in-theory (e/d (fn-bs-frontier-inputp fn-bs-frontier-next
                             fn-sf-statep)
                           (fn-bs-frontier-round-trip
                            fn-bs-frontier-next-is-successor)))))

; Actual P-FRONTIER pair 5 is after create/write/fsync(fd), before the
; namespace replacement.  This applies to retained transaction histories:
; it mentions only the fresh staging name and the state invariant.
(defthm fn-bs-k0-frontier-file-cut-is-write-fence
  (implies (and (fn-bs-statep bs)
                (not (fn-bs-lookup bs :staging stage)))
           (equal
            (car (nth 5 (fn-bs-run bs ks
                      (fn-bs-frontier-program stage octets)
                      nil groups capacity)))
            (let* ((ino (fn-bs-next-ino bs))
                   (created (mv-nth 1 (fn-bs-create bs :staging stage :ok)))
                   (written (mv-nth 1 (fn-bs-write created ino 0 octets :ok))))
              (fn-bs-fence-file written ino))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-frontier-program fn-bs-run fn-bs-step
                             fn-bs-fsync-file)
                           (fn-bs-statep fn-bs-create fn-bs-write
                            fn-bs-fence-file fn-bs-lookup)))))

(defthm fn-bs-k0-frontier-file-cut-has-exact-frame
  (implies (and (fn-bs-statep bs)
                (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage))
                (true-listp octets))
           (equal (fn-bs-durable-content
                   (car (nth 5 (fn-bs-run bs ks
                     (fn-bs-frontier-program stage octets)
                     nil groups capacity)))
                   (fn-bs-next-ino bs))
                  octets))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-k0-frontier-file-cut-is-write-fence
                 (:instance fn-bs-k6-create-write-fence-exact-frame
                            (frame octets)))
           :in-theory (disable fn-bs-run fn-bs-frontier-program
                               fn-bs-durable-content fn-bs-create
                               fn-bs-write fn-bs-fence-file))))

(defthm fn-bs-k0-frontier-file-cut-source-is-new-inode
  (implies (and (fn-bs-statep bs)
                (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage))
                (true-listp octets))
           (equal (fn-bs-lookup
                   (car (nth 5 (fn-bs-run bs ks
                                  (fn-bs-frontier-program stage octets)
                                  nil groups capacity)))
                   :staging stage)
                  (fn-bs-next-ino bs)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-file-cut-is-write-fence
                 (:instance fn-bs-k6-created-stage-lookup)
                 (:instance fn-bs-k6-write-keeps-lookup
                            (bs (mv-nth 1
                                 (fn-bs-create bs :staging stage :ok)))
                            (ino (fn-bs-next-ino bs)) (offset 0)
                            (octets octets) (dir :staging) (name stage))
                 (:instance fn-bs-k6-file-fence-keeps-valid-name-lookup
                            (bs (mv-nth 1
                             (fn-bs-write
                              (mv-nth 1 (fn-bs-create bs :staging stage :ok))
                              (fn-bs-next-ino bs) 0 octets :ok)))
                            (ino (fn-bs-next-ino bs))
                            (dir :staging) (name stage)))
           :in-theory (disable fn-bs-lookup fn-bs-run
                               fn-bs-frontier-program fn-bs-create
                               fn-bs-write fn-bs-fence-file))))

(defthm fn-bs-k0-frontier-file-cut-kernel-is-file-observation
  (implies (and (fn-bs-statep bs)
                (not (fn-bs-lookup bs :staging stage)))
           (equal (cdr (nth 6 (fn-bs-run bs ks
                         (fn-bs-frontier-program stage octets)
                         nil groups capacity)))
                  (fn-sf-frontier-file-result
                   (fn-sf-start-frontier ks) :ok)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-frontier-program fn-bs-run fn-bs-step
                             fn-sf-dispatch fn-bs-fsync-file)
                           (fn-bs-statep fn-bs-create fn-bs-write
                            fn-bs-fence-file fn-bs-lookup fn-bs-content
                            fn-bs-view)))))

; The staged file cut is well formed.  Keeping this recognizer closed avoids
; opening the whole relation on a half-reduced interpreter run.
(defthm fn-bs-k0-frontier-file-cut-statep
  (implies (and (fn-bs-statep bs)
                (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage))
                (fn-cbor-octet-listp octets))
           (fn-bs-statep
            (car (nth 5 (fn-bs-run bs ks
              (fn-bs-frontier-program stage octets)
              nil groups capacity)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-frontier-file-cut-is-write-fence)
                 (:instance fn-bs-create-preserves-statep
                            (s bs) (dir :staging) (name stage) (outcome :ok))
                 (:instance fn-bs-write-preserves-statep
                            (s (mv-nth 1 (fn-bs-create bs :staging stage :ok)))
                            (ino (fn-bs-next-ino bs)) (offset 0)
                            (octets octets) (outcome :ok))
                 (:instance fn-bs-fence-file-preserves-statep
                            (s (mv-nth 1 (fn-bs-write
                               (mv-nth 1 (fn-bs-create bs :staging stage :ok))
                               (fn-bs-next-ino bs) 0 octets :ok)))
                            (ino (fn-bs-next-ino bs))))
           :in-theory (e/d (fn-bs-create fn-bs-write)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-statep fn-bs-fence-file)))))

; P-FRONTIER and P-RECORD have the same successful staging prefix in the
; byte interpreter.  The allocator's earlier :start-frontier observation
; changes only the kernel state.  This by-definition bridge reuses existing
; old-authority content lemmas without assuming a post-cut scan or relation.
(local
 (defthm fn-bs-k0-frontier-file-cut-is-record-file-cut
   (implies (and (fn-bs-statep bs)
                 (fn-bs-namep stage)
                 (not (fn-bs-lookup bs :staging stage))
                 (true-listp octets))
            (equal (car (nth 5 (fn-bs-run bs ks
                                    (fn-bs-frontier-program stage octets)
                                    nil groups capacity)))
                   (car (nth 5 (fn-bs-run bs ks
                                    (fn-bs-record-program stage name octets)
                                    nil groups capacity)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use (fn-bs-k0-frontier-file-cut-is-write-fence
                  (:instance fn-bs-k6-interpreted-record-fence-is-write-fence
                             (frame octets)))
            :in-theory (disable fn-bs-run fn-bs-frontier-program
                                fn-bs-record-program fn-bs-create
                                fn-bs-write fn-bs-fence-file)))))

(defthm fn-bs-k0-frontier-file-cut-keeps-dirs
  (implies (and (fn-bs-statep bs)
                (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage))
                (true-listp octets))
           (equal (fn-bs-dirs
                   (car (nth 5 (fn-bs-run bs ks
                     (fn-bs-frontier-program stage octets)
                     nil groups capacity))))
                  (fn-bs-dirs bs)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-k0-frontier-file-cut-is-record-file-cut
                 (:instance fn-bs-k6-file-cut-dirs-are-input-dirs
                            (frame octets)))
           :in-theory (disable fn-bs-run fn-bs-frontier-program
                               fn-bs-record-program fn-bs-dirs))))

(defthm fn-bs-k0-frontier-file-cut-keeps-old-content
  (implies (and (fn-bs-statep bs)
                (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage))
                (true-listp octets)
                (not (equal other (fn-bs-next-ino bs))))
           (equal (fn-bs-durable-content
                   (car (nth 5 (fn-bs-run bs ks
                     (fn-bs-frontier-program stage octets)
                     nil groups capacity)))
                   other)
                  (fn-bs-durable-content bs other)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-k0-frontier-file-cut-is-record-file-cut
                 (:instance fn-bs-k0-file-cut-keeps-other-durable-content
                            (frame octets)))
           :in-theory (disable fn-bs-run fn-bs-frontier-program
                               fn-bs-record-program fn-bs-durable-content))))

(defthm fn-bs-k0-frontier-file-cut-keeps-old-frontier
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (equal (fn-bs-durable-frontier
                   (car (nth 5 (fn-bs-run bs ks
                     (fn-bs-frontier-program stage octets)
                     nil groups capacity))))
                  (fn-bs-durable-frontier bs)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-related-allocation-is-not-frontier-target
                 fn-bs-k0-frontier-file-cut-keeps-dirs
                 (:instance fn-bs-k0-frontier-file-cut-keeps-old-content
                            (other (fn-bs-durable-entry
                                    bs :root *fn-bs-scan-frontier-name*))))
           :in-theory (e/d (fn-bs-durable-frontier fn-bs-durable-entry
                             fn-bs-frontier-inputp)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-store-relation fn-bs-durable-content
                            fn-bs-statep)))))

(defthm fn-bs-k0-frontier-file-cut-keeps-config
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((file (car (nth 5 (fn-bs-run bs ks
                     (fn-bs-frontier-program stage octets)
                     nil groups capacity)))))
             (and (equal (fn-bs-durable-entry
                          file :root *fn-bs-scan-config-name*)
                         (fn-bs-durable-entry
                          bs :root *fn-bs-scan-config-name*))
                  (equal (fn-bs-durable-content file
                          (fn-bs-durable-entry
                           file :root *fn-bs-scan-config-name*))
                         (fn-bs-durable-content bs
                          (fn-bs-durable-entry
                           bs :root *fn-bs-scan-config-name*))))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-related-allocation-is-not-config-target
                 fn-bs-k0-frontier-file-cut-keeps-dirs
                 (:instance fn-bs-k0-frontier-file-cut-keeps-old-content
                            (other (fn-bs-durable-entry
                                    bs :root *fn-bs-scan-config-name*))))
           :in-theory (e/d (fn-bs-durable-entry fn-bs-frontier-inputp)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-store-relation fn-bs-durable-content
                            fn-bs-statep)))))

; Retained-history preservation is pointwise first.  The new inode is not
; any old transaction target (the relation's authority-known clause and
; state next-ino bound establish that), so each old path keeps both inode
; identity and exact raw octets through the allocator file fence.
(local
 (defthm fn-bs-k0-frontier-file-cut-txn-entry-is-input
   (implies (and (fn-bs-statep bs)
                 (fn-bs-namep stage)
                 (not (fn-bs-lookup bs :staging stage))
                 (true-listp octets))
            (equal
             (fn-bs-durable-entry
              (car (nth 5 (fn-bs-run bs ks
                (fn-bs-frontier-program stage octets)
                nil groups capacity))) :transactions name)
             (fn-bs-durable-entry bs :transactions name)))
   :rule-classes nil
   :hints (("Goal"
            :use (fn-bs-k0-frontier-file-cut-keeps-dirs)
            :in-theory (e/d (fn-bs-durable-entry)
                            (fn-bs-run fn-bs-frontier-program
                             fn-bs-dirs))))))

(local
 (defthm fn-bs-k0-frontier-file-cut-txn-content-is-input
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-frontier-inputp ks stage octets)
                 (not (fn-bs-lookup bs :staging stage)))
            (let ((file (car (nth 5 (fn-bs-run bs ks
                      (fn-bs-frontier-program stage octets)
                      nil groups capacity)))))
              (equal
               (fn-bs-durable-content
                file (fn-bs-durable-entry file :transactions name))
               (fn-bs-durable-content
                bs (fn-bs-durable-entry bs :transactions name)))))
   :rule-classes nil
   :hints (("Goal"
            :use (fn-bs-store-relation-unfolds
                  (:instance fn-bs-related-allocation-is-not-a-transaction-target
                             (name name))
                  fn-bs-k0-frontier-file-cut-txn-entry-is-input
                  (:instance fn-bs-k0-frontier-file-cut-keeps-old-content
                             (other (fn-bs-durable-entry
                                     bs :transactions name))))
            :in-theory (e/d (fn-bs-frontier-inputp)
                            (fn-bs-run fn-bs-frontier-program
                             fn-bs-store-relation fn-bs-durable-content
                             fn-bs-durable-entry fn-bs-statep))))))

(local
 (defthm fn-bs-k0-frontier-file-cut-durable-txn-lookup-is-input
   (implies (and (fn-bs-statep bs)
                 (fn-bs-namep stage)
                 (not (fn-bs-lookup bs :staging stage))
                 (true-listp octets))
            (let ((file (car (nth 5 (fn-bs-run bs ks
                      (fn-bs-frontier-program stage octets)
                      nil groups capacity)))))
              (equal (fn-bs-lookup (fn-bs-durable file)
                                    :transactions name)
                     (fn-bs-lookup (fn-bs-durable bs)
                                    :transactions name))))
   :rule-classes nil
   :hints (("Goal"
            :use (fn-bs-k0-frontier-file-cut-txn-entry-is-input
                  (:instance fn-bs-quiet-lookup-is-durable-entry
                             (s (fn-bs-durable bs)) (dir :transactions))
                  (:instance fn-bs-quiet-lookup-is-durable-entry
                             (s (fn-bs-durable
                              (car (nth 5 (fn-bs-run bs ks
                                (fn-bs-frontier-program stage octets)
                                nil groups capacity)))))
                             (dir :transactions)))
            :in-theory (e/d (fn-bs-durable fn-bs-durable-entry)
                            (fn-bs-run fn-bs-frontier-program
                             fn-bs-lookup fn-bs-view))))))

(local
 (defthm fn-bs-k0-frontier-file-cut-durable-txn-content-is-input
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-frontier-inputp ks stage octets)
                 (not (fn-bs-lookup bs :staging stage)))
            (let ((file (car (nth 5 (fn-bs-run bs ks
                      (fn-bs-frontier-program stage octets)
                      nil groups capacity)))))
              (equal (fn-bs-content
                      (fn-bs-durable file)
                      (fn-bs-lookup (fn-bs-durable file)
                                    :transactions name))
                     (fn-bs-content
                      (fn-bs-durable bs)
                      (fn-bs-lookup (fn-bs-durable bs)
                                    :transactions name)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use (fn-bs-store-relation-unfolds
                  fn-bs-k0-frontier-file-cut-durable-txn-lookup-is-input
                  fn-bs-k0-frontier-file-cut-txn-content-is-input
                  (:instance fn-bs-durable-is-quiet (bs bs))
                  (:instance fn-bs-durable-is-quiet
                             (bs (car (nth 5 (fn-bs-run bs ks
                               (fn-bs-frontier-program stage octets)
                               nil groups capacity)))))
                  (:instance fn-bs-quiet-lookup-is-durable-entry
                             (s (fn-bs-durable bs)) (dir :transactions))
                  (:instance fn-bs-quiet-lookup-is-durable-entry
                             (s (fn-bs-durable
                              (car (nth 5 (fn-bs-run bs ks
                                (fn-bs-frontier-program stage octets)
                                nil groups capacity)))))
                             (dir :transactions))
                  (:instance fn-bs-k0-durable-state-content-is-durable-content
                             (bs bs)
                             (ino (fn-bs-durable-entry bs :transactions name)))
                  (:instance fn-bs-k0-durable-state-content-is-durable-content
                             (bs (car (nth 5 (fn-bs-run bs ks
                               (fn-bs-frontier-program stage octets)
                               nil groups capacity))))
                             (ino (fn-bs-durable-entry bs :transactions name))))
            :in-theory (e/d (fn-bs-frontier-inputp fn-bs-durable-entry)
                            (fn-bs-run fn-bs-frontier-program
                             fn-bs-store-relation fn-bs-statep
                             fn-bs-lookup fn-bs-content
                             fn-bs-durable-content))))))

(local
 (defthm fn-bs-k0-frontier-file-cut-prefix-agrees
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-frontier-inputp ks stage octets)
                 (not (fn-bs-lookup bs :staging stage)))
            (fn-bs-txn-prefix-agreesp
             (fn-bs-durable
              (car (nth 5 (fn-bs-run bs ks
                (fn-bs-frontier-program stage octets)
                nil groups capacity))))
             (fn-bs-durable bs) n count))
   :rule-classes nil
   :hints (("Goal" :induct (fn-bs-txn-prefix-agreesp
               (fn-bs-durable
                (car (nth 5 (fn-bs-run bs ks
                  (fn-bs-frontier-program stage octets)
                  nil groups capacity))))
               (fn-bs-durable bs) n count)
            :in-theory (e/d (fn-bs-txn-prefix-agreesp fn-bs-frontier-inputp)
                            (fn-bs-run fn-bs-frontier-program
                             fn-bs-store-relation fn-bs-lookup fn-bs-content)))
           ("Subgoal *1/4"
            :use (fn-bs-store-relation-unfolds
                  (:instance fn-bs-k0-frontier-file-cut-durable-txn-lookup-is-input
                             (name (fn-bs-txn-name n)))))
           ("Subgoal *1/3"
            :use (fn-bs-store-relation-unfolds
                  (:instance fn-bs-k0-frontier-file-cut-durable-txn-content-is-input
                             (name (fn-bs-txn-name n))))))))

(defthm fn-bs-k0-frontier-file-cut-keeps-durable-records
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (equal
            (fn-bs-durable-records
             (car (nth 5 (fn-bs-run bs ks
               (fn-bs-frontier-program stage octets)
               nil groups capacity))))
            (fn-bs-durable-records bs)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-frontier-file-cut-keeps-dirs
                 (:instance fn-bs-k0-frontier-file-cut-prefix-agrees
                            (n 0)
                            (count (len (fn-bs-durable-names
                                         bs :transactions))))
                 (:instance fn-bs-read-records-under-agreement
                            (a (fn-bs-durable
                             (car (nth 5 (fn-bs-run bs ks
                               (fn-bs-frontier-program stage octets)
                               nil groups capacity)))))
                            (b (fn-bs-durable bs)) (n 0)
                            (count (len (fn-bs-durable-names
                                         bs :transactions)))))
           :in-theory (e/d (fn-bs-durable-records fn-bs-durable-names
                             fn-bs-frontier-inputp)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-store-relation fn-bs-read-records
                            fn-bs-txn-prefix-agreesp)))))

; The allocator's file callback is observational only.  The interpreter
; byte state at pair 6 is exactly the just-fenced pair 5 byte state.
(defthm fn-bs-k0-frontier-file-observation-keeps-byte-state
  (implies (and (fn-bs-statep bs)
                (not (fn-bs-lookup bs :staging stage)))
           (equal (car (nth 6 (fn-bs-run bs ks
                                 (fn-bs-frontier-program stage octets)
                                 nil groups capacity)))
                  (car (nth 5 (fn-bs-run bs ks
                                 (fn-bs-frontier-program stage octets)
                                 nil groups capacity)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-frontier-program fn-bs-run fn-bs-step
                             fn-bs-fsync-file)
                           (fn-bs-statep fn-bs-create fn-bs-write
                            fn-bs-fence-file fn-bs-lookup)))))

; At the file-fence cut the only new directory operation is in :staging.
; File fsync drains inode writes without changing root or transaction ops.
(local
 (defthm fn-bs-k0-frontier-file-cut-keeps-authority-dir-ops
   (implies (and (fn-bs-statep bs)
                 (fn-bs-namep stage)
                 (not (fn-bs-lookup bs :staging stage))
                 (true-listp octets)
                 (not (equal dir :staging)))
            (equal (fn-bs-ops-for-dir
                    (fn-bs-pending
                     (car (nth 5 (fn-bs-run bs ks
                       (fn-bs-frontier-program stage octets)
                       nil groups capacity))))
                    dir)
                   (fn-bs-ops-for-dir (fn-bs-pending bs) dir)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use (fn-bs-k0-frontier-file-cut-is-write-fence)
            :in-theory (e/d (fn-bs-create fn-bs-write fn-bs-fence-file
                              fn-bs-ops-for-dir-of-append
                              fn-bs-k6-filter-inode-writes-keeps-dir-ops)
                            (fn-bs-run fn-bs-frontier-program fn-bs-statep
                             fn-bs-lookup fn-bs-ops-not-for-ino))))))

(local
 (defthm fn-bs-k0-frontier-file-cut-authority-quiet
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-frontier-inputp ks stage octets)
                 (not (fn-bs-lookup bs :staging stage)))
            (let ((file (car (nth 5 (fn-bs-run bs ks
                      (fn-bs-frontier-program stage octets)
                      nil groups capacity)))))
              (and (equal (fn-bs-ops-for-dir
                           (fn-bs-pending file) :root) nil)
                   (equal (fn-bs-ops-for-dir
                           (fn-bs-pending file) :transactions) nil))))
   :rule-classes nil
   :hints (("Goal"
            :use (fn-bs-store-relation-unfolds
                  fn-bs-ready-relation-authority-is-quiet
                  (:instance fn-bs-k0-frontier-file-cut-keeps-authority-dir-ops
                             (dir :root))
                  (:instance fn-bs-k0-frontier-file-cut-keeps-authority-dir-ops
                             (dir :transactions)))
            :in-theory (e/d (fn-bs-frontier-inputp)
                            (fn-bs-run fn-bs-frontier-program
                             fn-bs-store-relation fn-bs-ops-for-dir))))))

; Authority target identities are unchanged: staging's new inode is not an
; authority target until the root rename is issued.  This fact supports both
; known-inode and file-fence preservation without inspecting old records.
(local
 (defthm fn-bs-k0-frontier-file-cut-authority-list-is-input
   (implies (and (fn-bs-statep bs)
                 (fn-bs-namep stage)
                 (not (fn-bs-lookup bs :staging stage))
                 (true-listp octets))
            (equal (fn-bs-authority-inode-list
                    (car (nth 5 (fn-bs-run bs ks
                      (fn-bs-frontier-program stage octets)
                      nil groups capacity))))
                   (fn-bs-authority-inode-list bs)))
   :rule-classes nil
   :hints (("Goal"
            :use (fn-bs-k0-frontier-file-cut-is-record-file-cut
                  fn-bs-k0-frontier-file-cut-keeps-dirs
                  (:instance fn-bs-k0-file-cut-keeps-pending-authority-targets
                             (frame octets)))
            :in-theory (e/d (fn-bs-authority-inode-list
                              fn-bs-durable-entry)
                            (fn-bs-run fn-bs-frontier-program
                             fn-bs-record-program fn-bs-pending-entry-targets
                             fn-bs-pending fn-bs-dirs))))))

(local
 (defthm fn-bs-k0-frontier-file-cut-keeps-known-list
   (implies (and (fn-bs-statep bs)
                 (fn-bs-namep stage)
                 (not (fn-bs-lookup bs :staging stage))
                 (true-listp octets)
                 (fn-bs-inode-list-knownp bs xs)
                 (not (member-equal (fn-bs-next-ino bs) xs)))
            (fn-bs-inode-list-knownp
             (car (nth 5 (fn-bs-run bs ks
               (fn-bs-frontier-program stage octets)
               nil groups capacity))) xs))
   :rule-classes nil
   :hints (("Goal" :induct (fn-bs-inode-list-knownp bs xs)
            :in-theory (e/d (fn-bs-inode-list-knownp)
                            (fn-bs-run fn-bs-frontier-program
                             fn-bs-statep fn-bs-lookup)))
           ("Subgoal *1/1''"
            :use (fn-bs-k0-frontier-file-cut-is-record-file-cut
                  (:instance fn-bs-k0-file-cut-keeps-other-inode-entry
                             (frame octets) (other (car xs))))))))

(defthm fn-bs-k0-frontier-file-cut-authority-known
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (fn-bs-authority-knownp
            (car (nth 5 (fn-bs-run bs ks
              (fn-bs-frontier-program stage octets)
              nil groups capacity)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-related-allocation-is-fresh
                 fn-bs-k0-frontier-file-cut-authority-list-is-input
                 (:instance fn-bs-k0-frontier-file-cut-keeps-known-list
                            (xs (fn-bs-authority-inode-list bs))))
           :in-theory (e/d (fn-bs-store-relation fn-bs-authority-knownp
                             fn-bs-frontier-inputp)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-statep fn-bs-inode-list-knownp
                            fn-bs-authority-fencedp fn-bs-durable-records
                            fn-bs-replay-matches-scan
                            fn-bs-pending-matches-phase fn-sf-crash-imagep)))))

(local
 (defthm fn-bs-k0-frontier-file-cut-keeps-fenced-list
   (implies (and (fn-bs-statep bs)
                 (fn-bs-namep stage)
                 (not (fn-bs-lookup bs :staging stage))
                 (true-listp octets)
                 (fn-bs-all-fencedp bs xs)
                 (not (member-equal (fn-bs-next-ino bs) xs)))
            (fn-bs-all-fencedp
             (car (nth 5 (fn-bs-run bs ks
               (fn-bs-frontier-program stage octets)
               nil groups capacity))) xs))
   :rule-classes nil
   :hints (("Goal" :induct (fn-bs-all-fencedp bs xs)
            :in-theory (e/d (fn-bs-all-fencedp)
                            (fn-bs-run fn-bs-frontier-program
                             fn-bs-statep fn-bs-lookup)))
           ("Subgoal *1/1''"
            :use (fn-bs-k0-frontier-file-cut-is-record-file-cut
                  (:instance fn-bs-k0-file-cut-keeps-other-fenced
                             (frame octets) (other (car xs))))))))

(defthm fn-bs-k0-frontier-file-cut-authority-fenced
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (fn-bs-authority-fencedp
            (car (nth 5 (fn-bs-run bs ks
              (fn-bs-frontier-program stage octets)
              nil groups capacity)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-related-allocation-is-fresh
                 fn-bs-k0-frontier-file-cut-authority-list-is-input
                 (:instance fn-bs-k0-frontier-file-cut-keeps-fenced-list
                            (xs (fn-bs-authority-inode-list bs))))
           :in-theory (e/d (fn-bs-store-relation fn-bs-authority-fencedp
                             fn-bs-frontier-inputp)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-statep fn-bs-all-fencedp
                            fn-bs-authority-knownp fn-bs-durable-records
                            fn-bs-replay-matches-scan
                            fn-bs-pending-matches-phase fn-sf-crash-imagep)))))

; Structural projection transport: while there is no pending authority
; entry, the relation depends only on exact durable config, frontier and
; record observations plus the separate state/authority invariants.  This
; is a helper, not a new K0 keystone and not a scan-equality assumption.
(local
 (defthm fn-bs-k0-quiet-projection-transports-relation
   (implies (and (fn-bs-store-relation bs k)
                 (not (fn-bs-replay-visiblep k))
                 (fn-bs-statep file)
                 (equal (fn-bs-dirs file) (fn-bs-dirs bs))
                 (equal (fn-bs-durable-content
                         file (fn-bs-durable-entry
                               file :root *fn-bs-scan-config-name*))
                        (fn-bs-durable-content
                         bs (fn-bs-durable-entry
                             bs :root *fn-bs-scan-config-name*)))
                 (equal (fn-bs-durable-frontier file)
                        (fn-bs-durable-frontier bs))
                 (equal (fn-bs-durable-records file)
                        (fn-bs-durable-records bs))
                 (fn-bs-authority-fencedp file)
                 (fn-bs-authority-knownp file)
                 (equal (fn-bs-ops-for-dir
                         (fn-bs-pending file) :root) nil)
                 (equal (fn-bs-ops-for-dir
                         (fn-bs-pending file) :transactions) nil))
            (fn-bs-store-relation file k))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use (fn-bs-store-relation-unfolds
                  fn-bs-store-relation-window-unfolds)
            :in-theory (e/d (fn-bs-store-relation fn-bs-durable-entry
                              fn-bs-durable-names fn-bs-contiguous-namesp
                              fn-bs-pending-matches-phase
                              fn-bs-pending-shape-okp)
                            (fn-bs-statep fn-sf-statep
                             fn-bs-durable-records fn-bs-durable-frontier
                             fn-bs-authority-fencedp fn-bs-authority-knownp
                             fn-bs-ops-for-dir fn-sf-crash-imagep
                             fn-bs-replay-matches-scan))))))

(local
 (defthm fn-bs-k0-frontier-file-kernel-relation
   (implies (fn-bs-store-relation bs ks)
            (fn-bs-store-relation
             bs (fn-sf-frontier-file-result
                 (fn-sf-start-frontier ks) :ok)))
   :rule-classes nil
   :hints (("Goal"
            :use (fn-bs-start-frontier-preserves-relation
                  (:instance fn-bs-frontier-file-result-preserves-relation
                             (ks (fn-sf-start-frontier ks)) (result :ok)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn-bs-k0-frontier-file-kernel-not-replaying
   (implies (equal (fn-sf-phase ks) :ready)
            (not (fn-bs-replay-visiblep
                  (fn-sf-frontier-file-result
                   (fn-sf-start-frontier ks) :ok))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (enable fn-bs-replay-visiblep
                               fn-sf-start-frontier
                               fn-sf-frontier-file-result)))))

; Actual arbitrary-history P-FRONTIER pair 6: the host has completed
; fsync(fd) and reported :frontier-file :ok, but has not attempted the
; replacement.  No output relation is assumed.  This is a complete
; physical/logical relation at this cut, not yet at :reserved.
(defthm fn-bs-k0-frontier-file-observation-establishes-relation
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (fn-bs-store-relation
            (car (nth 6 (fn-bs-run bs ks
                           (fn-bs-frontier-program stage octets)
                           nil groups capacity)))
            (cdr (nth 6 (fn-bs-run bs ks
                           (fn-bs-frontier-program stage octets)
                           nil groups capacity)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-frontier-file-cut-statep
                 fn-bs-k0-frontier-file-cut-keeps-dirs
                 fn-bs-k0-frontier-file-cut-keeps-old-frontier
                 fn-bs-k0-frontier-file-cut-keeps-config
                 fn-bs-k0-frontier-file-cut-keeps-durable-records
                 fn-bs-k0-frontier-file-cut-authority-known
                 fn-bs-k0-frontier-file-cut-authority-fenced
                 fn-bs-k0-frontier-file-cut-authority-quiet
                 fn-bs-k0-frontier-file-observation-keeps-byte-state
                 fn-bs-k0-frontier-file-cut-kernel-is-file-observation
                 fn-bs-k0-frontier-file-kernel-relation
                 fn-bs-k0-frontier-file-kernel-not-replaying
                 (:instance fn-bs-k0-quiet-projection-transports-relation
                            (file (car (nth 5 (fn-bs-run bs ks
                              (fn-bs-frontier-program stage octets)
                              nil groups capacity))))
                            (k (fn-sf-frontier-file-result
                                (fn-sf-start-frontier ks) :ok))))
           :in-theory (e/d (fn-bs-frontier-inputp fn-bs-ops-for-dir)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-store-relation fn-bs-statep
                            fn-bs-durable-frontier fn-bs-durable-records
                            fn-bs-authority-knownp
                            fn-bs-authority-fencedp)))))

; Successful allocator rename and root barrier, at the exact interpreter
; cuts called by Store.advance_frontier.  These facts use the prior relation
; only at entry; none assumes the desired post-fence scan or relation.
(local
 (defthm fn-bs-k0-frontier-replace-cut-is-rename
  (implies (and (fn-bs-statep bs) (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage)) (true-listp octets))
           (equal (car (nth 8 (fn-bs-run bs ks (fn-bs-frontier-program stage octets)
                                         nil groups capacity)))
                  (mv-nth 1 (fn-bs-rename
                             (car (nth 6 (fn-bs-run bs ks
                                                   (fn-bs-frontier-program stage octets)
                                                   nil groups capacity)))
                             :staging stage :root *fn-bs-frontier-name* :ok))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-file-observation-keeps-byte-state
                 fn-bs-k0-frontier-file-cut-source-is-new-inode
                 fn-bs-k0-frontier-file-cut-is-write-fence
                 (:instance fn-bs-k6-write-created-inode-returns-ok-without-namep
                            (frame octets)))
           :in-theory (e/d (fn-bs-frontier-program fn-bs-run fn-bs-step fn-bs-inop)
                           (fn-bs-statep fn-bs-create fn-bs-write fn-bs-fsync-file
                            fn-bs-fence-file fn-bs-lookup fn-bs-rename))))))

(local
 (defthm fn-bs-k0-frontier-rename-returns-ok
  (implies (and (fn-bs-statep bs) (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage)) (true-listp octets))
           (equal (mv-nth 0 (fn-bs-rename
                             (car (nth 6 (fn-bs-run bs ks
                                                   (fn-bs-frontier-program stage octets)
                                                   nil groups capacity)))
                             :staging stage :root *fn-bs-frontier-name* :ok))
                  :ok))
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-file-cut-source-is-new-inode
                 fn-bs-k0-frontier-file-observation-keeps-byte-state
                 (:instance fn-bs-k6-state-next-ino-is-inop))
           :in-theory (e/d (fn-bs-rename)
                           (fn-bs-statep fn-bs-run fn-bs-frontier-program
                            fn-bs-lookup fn-bs-inop))))))

(local
 (defthm fn-bs-k0-frontier-dir-cut-is-fence
  (implies (and (fn-bs-statep bs) (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage)) (true-listp octets))
           (equal (car (nth 12 (fn-bs-run bs ks
                                    (fn-bs-frontier-program stage octets)
                                    nil groups capacity)))
                  (fn-bs-fence-dir
                   (mv-nth 1 (fn-bs-rename
                              (car (nth 6 (fn-bs-run bs ks
                                                    (fn-bs-frontier-program stage octets)
                                                    nil groups capacity)))
                              :staging stage :root *fn-bs-frontier-name* :ok))
                   :root)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-replace-cut-is-rename
                 fn-bs-k0-frontier-rename-returns-ok
                 fn-bs-k0-frontier-file-observation-keeps-byte-state
                 fn-bs-k0-frontier-file-cut-source-is-new-inode
                 fn-bs-k0-frontier-file-cut-is-write-fence
                 (:instance fn-bs-k6-write-created-inode-returns-ok-without-namep
                            (frame octets)))
           :in-theory (e/d (fn-bs-frontier-program fn-bs-run fn-bs-step
                            fn-bs-fsync-dir fn-bs-inop)
                           (fn-bs-statep fn-bs-create fn-bs-write fn-bs-fsync-file
                            fn-bs-fence-file fn-bs-fence-dir fn-bs-lookup fn-bs-rename))))))

(local
 (defthm fn-bs-k0-one-set-entry
  (implies (and dir name)
   (equal (cdr (assoc-equal name
                  (cdr (assoc-equal dir
                        (fn-bs-apply-entries dirs
                           (list (list :set-entry dir name ino)))))))
         ino))
  :hints (("Goal" :use ((:instance fn-bs-apply-entries-entry-is-entry-after
                                    (ops (list (list :set-entry dir name ino)))))
           :in-theory (e/d (fn-bs-entry-after)
                           (fn-bs-apply-entries))))))

(local
 (defthm fn-bs-k0-rename-root-fence-installs-source
  (implies (and (fn-bs-dir-quietp file :root)
                (fn-bs-inop (fn-bs-lookup file :staging stage)))
           (equal (fn-bs-durable-entry
                   (fn-bs-fence-dir
                    (mv-nth 1 (fn-bs-rename file :staging stage
                                            :root *fn-bs-frontier-name* :ok))
                    :root)
                   :root *fn-bs-frontier-name*)
                  (fn-bs-lookup file :staging stage)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-one-set-entry
                            (dirs (fn-bs-dirs file))
                            (dir :root) (name *fn-bs-frontier-name*)
                            (ino (fn-bs-lookup file :staging stage))))
           :in-theory (e/d (fn-bs-dir-quietp fn-bs-rename
                            fn-bs-fence-dir fn-bs-durable-entry
                            fn-bs-ops-for-dir-of-append
                            fn-bs-apply-ops-dirs-are-apply-entries)
                           (fn-bs-lookup fn-bs-apply-ops
                            fn-bs-apply-entries))))))

(local
 (defthm fn-bs-k0-rename-root-fence-keeps-inode-content
  (equal (fn-bs-durable-content
          (fn-bs-fence-dir
           (mv-nth 1 (fn-bs-rename file :staging stage
                                   :root *fn-bs-frontier-name* :ok))
           :root)
          ino)
         (fn-bs-durable-content file ino))
  :hints (("Goal" :in-theory (e/d (fn-bs-fence-dir fn-bs-rename
                                     fn-bs-durable-content)
                                  (fn-bs-lookup fn-bs-apply-ops))))))

(local
 (defthm fn-bs-k0-frontier-dir-cut-durable-entry
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (equal (fn-bs-durable-entry
                   (car (nth 12 (fn-bs-run bs ks
                             (fn-bs-frontier-program stage octets)
                             nil groups capacity)))
                   :root *fn-bs-frontier-name*)
                  (fn-bs-next-ino bs)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-frontier-dir-cut-is-fence
                 fn-bs-k0-frontier-file-cut-source-is-new-inode
                 fn-bs-k0-frontier-file-observation-keeps-byte-state
                 fn-bs-k0-frontier-file-cut-authority-quiet
                 (:instance fn-bs-k6-state-next-ino-is-inop)
                 (:instance fn-bs-k0-rename-root-fence-installs-source
                            (file (car (nth 6 (fn-bs-run bs ks
                                             (fn-bs-frontier-program stage octets)
                                             nil groups capacity))))))
           :in-theory (e/d (fn-bs-frontier-inputp fn-bs-dir-quietp)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-store-relation fn-bs-statep
                            fn-bs-durable-entry fn-bs-rename
                            fn-bs-fence-dir fn-bs-lookup))))))

(defthm fn-bs-k0-frontier-dir-cut-exact-octets
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (equal (fn-bs-durable-content
                   (car (nth 12 (fn-bs-run bs ks
                             (fn-bs-frontier-program stage octets)
                             nil groups capacity)))
                   (fn-bs-durable-entry
                    (car (nth 12 (fn-bs-run bs ks
                              (fn-bs-frontier-program stage octets)
                              nil groups capacity)))
                    :root *fn-bs-frontier-name*))
                  octets))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-frontier-dir-cut-is-fence
                 fn-bs-k0-frontier-dir-cut-durable-entry
                 fn-bs-k0-frontier-file-observation-keeps-byte-state
                 fn-bs-k0-frontier-file-cut-has-exact-frame
                 (:instance fn-bs-k0-rename-root-fence-keeps-inode-content
                            (file (car (nth 6 (fn-bs-run bs ks
                                             (fn-bs-frontier-program stage octets)
                                             nil groups capacity))))
                            (ino (fn-bs-next-ino bs))))
           :in-theory (e/d (fn-bs-frontier-inputp)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-store-relation fn-bs-statep
                            fn-bs-durable-entry fn-bs-durable-content
                            fn-bs-rename fn-bs-fence-dir)))))

(defthm fn-bs-k0-frontier-dir-cut-decodes-candidate
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (equal (fn-bs-durable-frontier
                   (car (nth 12 (fn-bs-run bs ks
                             (fn-bs-frontier-program stage octets)
                             nil groups capacity))))
                  (1+ (fn-sf-frontier ks))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-dir-cut-exact-octets)
           :in-theory (e/d (fn-bs-frontier-inputp fn-bs-durable-frontier)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-durable-entry fn-bs-durable-content)))))

(defthm fn-bs-k0-frontier-dir-cut-root-quiet
  (implies (and (fn-bs-statep bs) (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage)) (true-listp octets))
           (fn-bs-dir-quietp
            (car (nth 12 (fn-bs-run bs ks
                      (fn-bs-frontier-program stage octets)
                      nil groups capacity)))
            :root))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-dir-cut-is-fence)
           :in-theory (e/d (fn-bs-dir-quietp)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-fence-dir fn-bs-rename)))))

(local
 (defthm fn-bs-k0-frontier-suffix-kernel
  (implies (and (fn-sf-statep fileks)
                (equal (fn-sf-phase fileks) :frontier-data-durable)
                (fn-bs-inop (fn-bs-lookup file :staging stage)))
           (equal (cdr (nth 5 (fn-bs-run
                               file fileks
                               (nthcdr 7 (fn-bs-frontier-program stage octets))
                               nil groups capacity)))
                  (fn-sf-frontier-replace-result fileks :ok)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-frontier-program fn-bs-run fn-bs-step
                            fn-sf-dispatch fn-bs-rename fn-bs-fsync-dir)
                           (fn-bs-lookup fn-sf-statep
                            fn-sf-frontier-replace-result fn-bs-fence-dir))))))

(local
 (defthm fn-bs-k0-frontier-suffix-starts-at-file-observation
  (implies (and (fn-bs-statep bs) (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage)) (true-listp octets))
           (equal (nth 12 (fn-bs-run bs ks
                                      (fn-bs-frontier-program stage octets)
                                      nil groups capacity))
                  (nth 5 (fn-bs-run
                          (car (nth 6 (fn-bs-run bs ks
                                                (fn-bs-frontier-program stage octets)
                                                nil groups capacity)))
                          (cdr (nth 6 (fn-bs-run bs ks
                                                (fn-bs-frontier-program stage octets)
                                                nil groups capacity)))
                          (nthcdr 7 (fn-bs-frontier-program stage octets))
                          nil groups capacity))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-file-cut-is-write-fence
                 fn-bs-k0-frontier-file-cut-source-is-new-inode
                 (:instance fn-bs-k6-write-created-inode-returns-ok-without-namep
                            (frame octets)))
           :in-theory (e/d (fn-bs-frontier-program fn-bs-run fn-bs-step
                            fn-bs-fsync-file)
                           (fn-bs-statep fn-bs-create fn-bs-write
                            fn-bs-fence-file fn-bs-lookup
                            fn-bs-fsync-dir fn-bs-rename))))))

(local
 (defthm fn-bs-k0-frontier-file-callback-is-durable-phase
  (implies (and (fn-sf-statep ks)
                (equal (fn-sf-phase ks) :ready)
                (< (fn-sf-frontier ks) *fn-sf-max-uint*))
           (equal (fn-sf-phase
                   (fn-sf-frontier-file-result
                    (fn-sf-start-frontier ks) :ok))
                  :frontier-data-durable))
  :hints (("Goal" :use ((:instance fn-sf-start-frontier-preserves-state (s ks)))
           :in-theory (enable fn-sf-start-frontier
                              fn-sf-frontier-file-result)))))

(local
 (defthm fn-bs-k0-frontier-file-observation-source-is-new-inode
  (implies (and (fn-bs-statep bs) (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage)) (true-listp octets))
           (equal (fn-bs-lookup
                   (car (nth 6 (fn-bs-run bs ks
                             (fn-bs-frontier-program stage octets)
                             nil groups capacity)))
                   :staging stage)
                  (fn-bs-next-ino bs)))
  :rule-classes nil
  :hints (("Goal" :use (fn-bs-k0-frontier-file-cut-source-is-new-inode
                        fn-bs-k0-frontier-file-observation-keeps-byte-state)
           :in-theory (disable fn-bs-run fn-bs-frontier-program
                               fn-bs-lookup)))))

(defthm fn-bs-k0-frontier-dir-cut-kernel-is-replace-observation
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (equal (cdr (nth 12 (fn-bs-run bs ks
                                         (fn-bs-frontier-program stage octets)
                                         nil groups capacity)))
                  (fn-sf-frontier-replace-result
                   (fn-sf-frontier-file-result
                    (fn-sf-start-frontier ks) :ok)
                   :ok)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-frontier-suffix-starts-at-file-observation
                 (:instance fn-bs-k0-frontier-suffix-kernel
                            (file (car (nth 6 (fn-bs-run bs ks
                                              (fn-bs-frontier-program stage octets)
                                              nil groups capacity))))
                            (fileks (cdr (nth 6 (fn-bs-run bs ks
                                               (fn-bs-frontier-program stage octets)
                                               nil groups capacity)))))
                 fn-bs-k0-frontier-file-cut-kernel-is-file-observation
                 fn-bs-k0-frontier-file-observation-source-is-new-inode
                 fn-bs-k0-frontier-file-callback-is-durable-phase
                 (:instance fn-sf-start-frontier-preserves-state (s ks))
                 (:instance fn-sf-frontier-file-result-preserves-state
                            (s (fn-sf-start-frontier ks)) (result :ok))
                 (:instance fn-bs-k6-state-next-ino-is-inop))
           :in-theory (e/d (fn-bs-frontier-inputp)
                           (fn-bs-run fn-bs-frontier-program fn-bs-store-relation
                            fn-bs-statep fn-bs-lookup
                            fn-sf-start-frontier fn-sf-frontier-file-result
                            fn-sf-frontier-replace-result)))))

(defthm fn-bs-k0-frontier-dir-cut-kernel-candidate-and-phase
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (and (equal (fn-sf-phase
                        (cdr (nth 12 (fn-bs-run bs ks
                                        (fn-bs-frontier-program stage octets)
                                        nil groups capacity))))
                       :frontier-attempted)
                (equal (fn-sf-frontier-candidate
                        (cdr (nth 12 (fn-bs-run bs ks
                                        (fn-bs-frontier-program stage octets)
                                        nil groups capacity))))
                       (1+ (fn-sf-frontier ks)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-frontier-dir-cut-kernel-is-replace-observation
                 (:instance fn-sf-start-frontier-preserves-state (s ks))
                 (:instance fn-sf-frontier-file-result-preserves-state
                            (s (fn-sf-start-frontier ks)) (result :ok)))
           :in-theory (e/d (fn-bs-frontier-inputp fn-sf-start-frontier
                            fn-sf-frontier-file-result
                            fn-sf-frontier-replace-result)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-store-relation fn-bs-statep)))))

; This supplies the concrete byte/candidate premise of the existing
; frontier-directory callback theorem.  Its remaining pre-callback relation
; premise is an actual K0 obligation, not silently assumed here.
(defthm fn-bs-k0-frontier-dir-cut-committedp
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (fn-bs-frontier-directory-committedp
            (car (nth 12 (fn-bs-run bs ks
                      (fn-bs-frontier-program stage octets)
                      nil groups capacity)))
            (cdr (nth 12 (fn-bs-run bs ks
                      (fn-bs-frontier-program stage octets)
                      nil groups capacity)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-frontier-dir-cut-decodes-candidate
                 fn-bs-k0-frontier-dir-cut-root-quiet
                 fn-bs-k0-frontier-dir-cut-kernel-candidate-and-phase)
           :in-theory (e/d (fn-bs-frontier-directory-committedp
                            fn-bs-frontier-inputp)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-durable-frontier fn-bs-dir-quietp)))))

; The physical root fence drains its own rename.  The rename adds only a
; root entry and a staging deletion, so it cannot introduce a transaction
; operation.  This is the pending-authority clause needed by the still-open
; complete relation at the actual pre-callback pair 12.
(local
 (defthm fn-bs-k0-frontier-rename-keeps-transaction-quiet
  (implies (equal (fn-bs-ops-for-dir (fn-bs-pending file) :transactions) nil)
           (equal (fn-bs-ops-for-dir
                   (fn-bs-pending (mv-nth 1 (fn-bs-rename
                     file :staging stage :root *fn-bs-frontier-name* :ok)))
                   :transactions) nil))
  :hints (("Goal" :use ((:instance fn-bs-ops-for-dir-of-append
                           (a (fn-bs-pending file))
                           (b (list (list :set-entry :root *fn-bs-frontier-name*
                                          (fn-bs-lookup file :staging stage))
                                    (list :del-entry :staging stage)))
                           (dir :transactions)))
           :in-theory (e/d (fn-bs-rename)
                           (fn-bs-lookup fn-bs-ops-for-dir-of-append))))))

(local
 (defthm fn-bs-k0-other-directory-ops-survive-filter
  (implies (not (equal kept removed))
           (equal (fn-bs-ops-for-dir (fn-bs-ops-not-for-dir ops removed) kept)
                  (fn-bs-ops-for-dir ops kept)))
  :hints (("Goal" :induct (fn-bs-ops-not-for-dir ops removed)
           :in-theory (enable fn-bs-ops-for-dir fn-bs-ops-not-for-dir)))))

(local
 (defthm fn-bs-k0-root-fence-keeps-transaction-quiet
  (implies (equal (fn-bs-ops-for-dir (fn-bs-pending file) :transactions) nil)
           (equal (fn-bs-ops-for-dir
                   (fn-bs-pending (fn-bs-fence-dir file :root))
                   :transactions) nil))
  :hints (("Goal" :use ((:instance fn-bs-k0-other-directory-ops-survive-filter
                                    (ops (fn-bs-pending file))
                                    (removed :root) (kept :transactions)))
           :in-theory (e/d (fn-bs-fence-dir)
                           (fn-bs-ops-for-dir fn-bs-ops-not-for-dir
                            fn-bs-k0-other-directory-ops-survive-filter))))))

(local
 (defthm fn-bs-k0-frontier-dir-cut-transaction-quiet
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (equal (fn-bs-ops-for-dir
                   (fn-bs-pending
                    (car (nth 12 (fn-bs-run bs ks
                                   (fn-bs-frontier-program stage octets)
                                   nil groups capacity))))
                   :transactions)
                  nil))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-frontier-file-cut-authority-quiet
                 fn-bs-k0-frontier-file-observation-keeps-byte-state
                 fn-bs-k0-frontier-dir-cut-is-fence
                 (:instance fn-bs-k0-frontier-rename-keeps-transaction-quiet
                   (file (car (nth 6 (fn-bs-run bs ks
                         (fn-bs-frontier-program stage octets)
                         nil groups capacity)))))
                 (:instance fn-bs-k0-root-fence-keeps-transaction-quiet
                   (file (mv-nth 1 (fn-bs-rename
                         (car (nth 6 (fn-bs-run bs ks
                           (fn-bs-frontier-program stage octets)
                           nil groups capacity)))
                         :staging stage :root *fn-bs-frontier-name* :ok)))))
           :in-theory (e/d (fn-bs-frontier-inputp)
                           (fn-bs-run fn-bs-frontier-program fn-bs-statep
                            fn-bs-store-relation fn-bs-lookup
                            fn-bs-rename fn-bs-fence-dir fn-bs-ops-for-dir
                            fn-bs-k0-frontier-rename-keeps-transaction-quiet
                            fn-bs-k0-root-fence-keeps-transaction-quiet))))))

(defthm fn-bs-k0-frontier-dir-cut-pending-matches-phase
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (fn-bs-pending-matches-phase
            (car (nth 12 (fn-bs-run bs ks
                           (fn-bs-frontier-program stage octets)
                           nil groups capacity)))
            (cdr (nth 12 (fn-bs-run bs ks
                           (fn-bs-frontier-program stage octets)
                           nil groups capacity)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-frontier-dir-cut-root-quiet
                 fn-bs-k0-frontier-dir-cut-transaction-quiet)
           :in-theory (e/d (fn-bs-pending-matches-phase
                            fn-bs-pending-shape-okp fn-bs-dir-quietp
                            fn-bs-frontier-inputp)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-ops-for-dir fn-bs-store-relation)))))

(defthm fn-bs-k0-frontier-dir-cut-statep
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (fn-bs-statep
            (car (nth 12 (fn-bs-run bs ks
                           (fn-bs-frontier-program stage octets)
                           nil groups capacity)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-frontier-file-cut-statep
                 fn-bs-k0-frontier-file-observation-keeps-byte-state
                 fn-bs-k0-frontier-dir-cut-is-fence
                 (:instance fn-bs-rename-preserves-statep
                   (s (car (nth 6 (fn-bs-run bs ks
                           (fn-bs-frontier-program stage octets)
                           nil groups capacity))))
                   (sdir :staging) (sname stage)
                   (ddir :root) (dname *fn-bs-frontier-name*)
                   (outcome :ok))
                 (:instance fn-bs-fence-dir-preserves-statep
                   (s (mv-nth 1 (fn-bs-rename
                         (car (nth 6 (fn-bs-run bs ks
                           (fn-bs-frontier-program stage octets)
                           nil groups capacity)))
                         :staging stage :root *fn-bs-frontier-name* :ok)))
                   (dir :root)))
           :in-theory (e/d (fn-bs-frontier-inputp fn-bs-dir-idp fn-bs-namep)
                           (fn-bs-run fn-bs-frontier-program fn-bs-statep
                            fn-bs-store-relation fn-bs-lookup
                            fn-bs-rename fn-bs-fence-dir)))))

; Pair 12: root replacement retains every prior transaction byte projection.
(defthm fn-bs-k0-same-transaction-tables-lookup
  (implies (equal (cdr (assoc-equal :transactions (fn-bs-dirs a)))
                  (cdr (assoc-equal :transactions (fn-bs-dirs b))))
           (equal (fn-bs-lookup (fn-bs-durable a) :transactions name)
                  (fn-bs-lookup (fn-bs-durable b) :transactions name)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-quiet-lookup-is-durable-entry
                           (s (fn-bs-durable a)) (dir :transactions))
                         (:instance fn-bs-quiet-lookup-is-durable-entry
                           (s (fn-bs-durable b)) (dir :transactions)))
           :in-theory (e/d (fn-bs-durable fn-bs-durable-entry)
                           (fn-bs-lookup fn-bs-view)))))

(defthm fn-bs-k0-same-inodes-durable-content
  (implies (equal (fn-bs-inodes a) (fn-bs-inodes b))
           (equal (fn-bs-content (fn-bs-durable a) ino)
                  (fn-bs-content (fn-bs-durable b) ino)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-quiet-content-is-durable-content
                           (s (fn-bs-durable a)))
                         (:instance fn-bs-quiet-content-is-durable-content
                           (s (fn-bs-durable b))))
           :in-theory (e/d (fn-bs-durable fn-bs-durable-content)
                           (fn-bs-content fn-bs-view)))))

(defthm fn-bs-k0-same-txn-tables-prefix-agrees
  (implies (and (equal (fn-bs-inodes a) (fn-bs-inodes b))
                (equal (cdr (assoc-equal :transactions (fn-bs-dirs a)))
                       (cdr (assoc-equal :transactions (fn-bs-dirs b)))))
           (fn-bs-txn-prefix-agreesp (fn-bs-durable a) (fn-bs-durable b) n count))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bs-txn-prefix-agreesp
                            (fn-bs-durable a) (fn-bs-durable b) n count)
           :in-theory (e/d (fn-bs-txn-prefix-agreesp)
                           (fn-bs-durable fn-bs-lookup fn-bs-content)))
          ("Subgoal *1/4"
           :use ((:instance fn-bs-k0-same-transaction-tables-lookup
                            (name (fn-bs-txn-name n)))))
          ("Subgoal *1/3"
           :use ((:instance fn-bs-k0-same-inodes-durable-content
                            (ino (fn-bs-lookup (fn-bs-durable a)
                                               :transactions (fn-bs-txn-name n))))
                 (:instance fn-bs-k0-same-transaction-tables-lookup
                            (name (fn-bs-txn-name n)))))))

(defthm fn-bs-k0-same-transaction-tables-durable-records
  (implies (and (equal (fn-bs-inodes a) (fn-bs-inodes b))
                (equal (cdr (assoc-equal :transactions (fn-bs-dirs a)))
                       (cdr (assoc-equal :transactions (fn-bs-dirs b)))))
           (equal (fn-bs-durable-records a)
                  (fn-bs-durable-records b)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-same-txn-tables-prefix-agrees
                            (n 0)
                            (count (len (fn-bs-durable-names a :transactions))))
                 (:instance fn-bs-read-records-under-agreement
                            (a (fn-bs-durable a)) (b (fn-bs-durable b))
                            (n 0)
                            (count (len (fn-bs-durable-names a :transactions)))))
           :in-theory (e/d (fn-bs-durable-records fn-bs-durable-names)
                           (fn-bs-read-records fn-bs-txn-prefix-agreesp)))))

(defthm fn-bs-k0-frontier-dir-cut-keeps-inodes
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (equal (fn-bs-inodes
                   (car (nth 12 (fn-bs-run bs ks
                                   (fn-bs-frontier-program stage octets)
                                   nil groups capacity))))
                  (fn-bs-inodes
                   (car (nth 6 (fn-bs-run bs ks
                                  (fn-bs-frontier-program stage octets)
                                  nil groups capacity))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-frontier-dir-cut-is-fence
                 (:instance fn-bs-fence-dir-drains-exactly-its-directory
                   (s (mv-nth 1 (fn-bs-rename
                       (car (nth 6 (fn-bs-run bs ks
                         (fn-bs-frontier-program stage octets)
                         nil groups capacity)))
                       :staging stage :root *fn-bs-frontier-name* :ok)))
                   (dir :root)))
           :in-theory (e/d (fn-bs-frontier-inputp fn-bs-rename)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-fence-dir fn-bs-lookup fn-bs-store-relation)))))

(defthm fn-bs-k0-frontier-dir-cut-keeps-transaction-table
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (equal (cdr (assoc-equal :transactions
                              (fn-bs-dirs (car (nth 12 (fn-bs-run
                                bs ks (fn-bs-frontier-program stage octets)
                                nil groups capacity))))))
                  (cdr (assoc-equal :transactions
                              (fn-bs-dirs (car (nth 6 (fn-bs-run
                                bs ks (fn-bs-frontier-program stage octets)
                                nil groups capacity))))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-frontier-dir-cut-is-fence
                 (:instance fn-bs-fence-dir-touches-only-its-directory
                   (s (mv-nth 1 (fn-bs-rename
                       (car (nth 6 (fn-bs-run bs ks
                         (fn-bs-frontier-program stage octets)
                         nil groups capacity)))
                       :staging stage :root *fn-bs-frontier-name* :ok)))
                   (dir :root) (other :transactions)))
           :in-theory (e/d (fn-bs-frontier-inputp fn-bs-rename)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-fence-dir fn-bs-lookup fn-bs-store-relation)))))

(defthm fn-bs-k0-frontier-dir-cut-keeps-durable-records
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (equal (fn-bs-durable-records
                   (car (nth 12 (fn-bs-run bs ks
                                   (fn-bs-frontier-program stage octets)
                                   nil groups capacity))))
                  (fn-bs-durable-records bs)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-frontier-dir-cut-keeps-inodes
                 fn-bs-k0-frontier-dir-cut-keeps-transaction-table
                 fn-bs-k0-frontier-file-observation-keeps-byte-state
                 fn-bs-k0-frontier-file-cut-keeps-durable-records
                 (:instance fn-bs-k0-same-transaction-tables-durable-records
                   (a (car (nth 12 (fn-bs-run bs ks
                         (fn-bs-frontier-program stage octets)
                         nil groups capacity))))
                   (b (car (nth 6 (fn-bs-run bs ks
                         (fn-bs-frontier-program stage octets)
                         nil groups capacity))))))
           :in-theory (e/d (fn-bs-frontier-inputp)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-durable-records fn-bs-store-relation)))))

(defthm fn-bs-k0-ready-input-durable-records-match
  (implies (and (fn-bs-store-relation bs ks)
                (equal (fn-sf-phase ks) :ready))
           (equal (fn-bs-durable-records bs) (fn-sf-records ks)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-window-unfolds)
           :in-theory (e/d (fn-bs-replay-visiblep fn-sf-crash-imagep
                            fn-sf-record-present-visiblep)
                           (fn-bs-store-relation fn-bs-durable-records
                            fn-bs-durable-frontier fn-bs-pending-matches-phase
                            fn-sf-statep)))))

(defthm fn-bs-k0-frontier-dir-cut-crash-imagep
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (fn-sf-crash-imagep
            (cdr (nth 12 (fn-bs-run bs ks
                           (fn-bs-frontier-program stage octets)
                           nil groups capacity)))
            (fn-bs-durable-frontier
             (car (nth 12 (fn-bs-run bs ks
                            (fn-bs-frontier-program stage octets)
                            nil groups capacity))))
            (fn-bs-durable-records
             (car (nth 12 (fn-bs-run bs ks
                            (fn-bs-frontier-program stage octets)
                            nil groups capacity))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-ready-input-durable-records-match
                 fn-bs-k0-frontier-dir-cut-kernel-is-replace-observation
                 fn-bs-k0-frontier-dir-cut-kernel-candidate-and-phase
                 fn-bs-k0-frontier-dir-cut-decodes-candidate
                 fn-bs-k0-frontier-dir-cut-keeps-durable-records
                 (:instance fn-sf-start-frontier-preserves-state (s ks))
                 (:instance fn-sf-frontier-file-result-preserves-state
                            (s (fn-sf-start-frontier ks)) (result :ok))
                 (:instance fn-sf-frontier-replace-result-preserves-state
                            (s (fn-sf-frontier-file-result
                                (fn-sf-start-frontier ks) :ok)) (result :ok)))
           :in-theory (e/d (fn-bs-frontier-inputp fn-sf-crash-imagep
                            fn-sf-frontier-new-visiblep
                            fn-sf-record-present-visiblep
                            fn-sf-start-frontier fn-sf-frontier-file-result
                            fn-sf-frontier-replace-result)
                           (fn-bs-run fn-bs-frontier-program fn-bs-store-relation
                            fn-bs-durable-frontier fn-bs-durable-records
                            fn-sf-statep)))))

(defthm fn-bs-k0-frontier-root-fence-keeps-config-entry
  (implies (and (fn-bs-dir-quietp file :root)
                (fn-bs-inop (fn-bs-lookup file :staging stage)))
           (equal (fn-bs-durable-entry
                   (fn-bs-fence-dir
                    (mv-nth 1 (fn-bs-rename file :staging stage
                                            :root *fn-bs-frontier-name* :ok))
                    :root)
                   :root *fn-bs-scan-config-name*)
                  (fn-bs-durable-entry file :root *fn-bs-scan-config-name*)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-apply-entries-entry-is-entry-after
                            (dirs (fn-bs-dirs file))
                            (ops (list (list :set-entry :root
                                             *fn-bs-frontier-name*
                                             (fn-bs-lookup file :staging stage))))
                            (dir :root) (name *fn-bs-scan-config-name*)))
           :in-theory (e/d (fn-bs-dir-quietp fn-bs-rename fn-bs-fence-dir
                            fn-bs-durable-entry fn-bs-ops-for-dir-of-append
                            fn-bs-apply-ops-dirs-are-apply-entries
                            fn-bs-entry-after)
                           (fn-bs-lookup fn-bs-apply-ops
                            fn-bs-apply-entries)))))

(defthm fn-bs-k0-frontier-dir-cut-keeps-config-entry
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (equal (fn-bs-durable-entry
                   (car (nth 12 (fn-bs-run bs ks
                                   (fn-bs-frontier-program stage octets)
                                   nil groups capacity)))
                   :root *fn-bs-scan-config-name*)
                  (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-frontier-dir-cut-is-fence
                 fn-bs-k0-frontier-file-observation-keeps-byte-state
                 fn-bs-k0-frontier-file-cut-authority-quiet
                 fn-bs-k0-frontier-file-cut-keeps-config
                 fn-bs-k0-frontier-file-observation-source-is-new-inode
                 (:instance fn-bs-k6-state-next-ino-is-inop)
                 (:instance fn-bs-k0-frontier-root-fence-keeps-config-entry
                  (file (car (nth 6 (fn-bs-run bs ks
                           (fn-bs-frontier-program stage octets)
                           nil groups capacity))))))
           :in-theory (e/d (fn-bs-frontier-inputp fn-bs-dir-quietp)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-lookup fn-bs-durable-entry
                            fn-bs-store-relation)))))

(defthm fn-bs-k0-frontier-dir-cut-keeps-config-content
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (equal (fn-bs-durable-content
                   (car (nth 12 (fn-bs-run bs ks
                                   (fn-bs-frontier-program stage octets)
                                   nil groups capacity)))
                   (fn-bs-durable-entry
                    (car (nth 12 (fn-bs-run bs ks
                                    (fn-bs-frontier-program stage octets)
                                    nil groups capacity)))
                    :root *fn-bs-scan-config-name*))
                  (fn-bs-durable-content bs
                   (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-frontier-dir-cut-keeps-inodes
                 fn-bs-k0-frontier-dir-cut-keeps-config-entry
                 fn-bs-k0-frontier-file-observation-keeps-byte-state
                 fn-bs-k0-frontier-file-cut-keeps-config)
           :in-theory (e/d (fn-bs-frontier-inputp fn-bs-durable-content)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-store-relation fn-bs-durable-entry)))))

(defthm fn-bs-k0-pending-authority-targets-empty-when-quiet
  (implies (and (not (fn-bs-ops-for-dir ops :root))
                (not (fn-bs-ops-for-dir ops :transactions)))
           (equal (fn-bs-pending-entry-targets ops) nil))
  :hints (("Goal" :induct (fn-bs-pending-entry-targets ops)
           :in-theory (enable fn-bs-pending-entry-targets fn-bs-ops-for-dir))))

(defthm fn-bs-k0-frontier-dir-cut-authority-list
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (equal (fn-bs-authority-inode-list
                   (car (nth 12 (fn-bs-run bs ks
                                   (fn-bs-frontier-program stage octets)
                                   nil groups capacity))))
                  (append (list (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*)
                                (fn-bs-next-ino bs))
                          (strip-cdrs (cdr (assoc-equal :transactions
                                                       (fn-bs-dirs bs)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-frontier-dir-cut-keeps-config-entry
                 fn-bs-k0-frontier-dir-cut-durable-entry
                 fn-bs-k0-frontier-dir-cut-keeps-transaction-table
                 fn-bs-k0-frontier-dir-cut-root-quiet
                 fn-bs-k0-frontier-dir-cut-transaction-quiet
                 fn-bs-k0-frontier-file-cut-keeps-dirs
                 fn-bs-k0-frontier-file-observation-keeps-byte-state
                 (:instance fn-bs-k0-pending-authority-targets-empty-when-quiet
                   (ops (fn-bs-pending
                         (car (nth 12 (fn-bs-run bs ks
                           (fn-bs-frontier-program stage octets)
                           nil groups capacity)))))))
           :in-theory (e/d (fn-bs-authority-inode-list fn-bs-dir-quietp
                            fn-bs-frontier-inputp)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-pending-entry-targets
                            fn-bs-durable-entry fn-bs-ops-for-dir)))))

; The actual pre-callback allocator pair re-establishes the full K0 relation.
(defthm fn-bs-k0-directory-filter-keeps-inode-ops
  (equal (fn-bs-ops-for-ino (fn-bs-ops-not-for-dir ops dir) ino)
         (fn-bs-ops-for-ino ops ino))
  :hints (("Goal" :induct (fn-bs-ops-not-for-dir ops dir)
           :in-theory (enable fn-bs-ops-not-for-dir fn-bs-ops-for-ino))))

(defthm fn-bs-k0-frontier-rename-preserves-fencedp
  (equal (fn-bs-fencedp
          (mv-nth 1 (fn-bs-rename file :staging stage
                                  :root *fn-bs-frontier-name* :ok)) ino)
         (fn-bs-fencedp file ino))
  :hints (("Goal" :use ((:instance fn-bs-ops-for-ino-of-append
                           (a (fn-bs-pending file))
                           (b (list (list :set-entry :root *fn-bs-frontier-name*
                                          (fn-bs-lookup file :staging stage))
                                    (list :del-entry :staging stage)))))
           :in-theory (e/d (fn-bs-rename fn-bs-fencedp)
                           (fn-bs-lookup fn-bs-ops-for-ino-of-append)))))

(defthm fn-bs-k0-root-fence-preserves-fencedp
  (equal (fn-bs-fencedp (fn-bs-fence-dir file :root) ino)
         (fn-bs-fencedp file ino))
  :hints (("Goal" :use ((:instance fn-bs-k0-directory-filter-keeps-inode-ops
                                    (ops (fn-bs-pending file)) (dir :root)))
           :in-theory (e/d (fn-bs-fence-dir fn-bs-fencedp)
                           (fn-bs-ops-for-ino fn-bs-ops-not-for-dir
                            fn-bs-k0-directory-filter-keeps-inode-ops)))))

(defthm fn-bs-k0-frontier-dir-cut-preserves-fencedp-rewrite
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (equal (fn-bs-fencedp
                   (car (nth 12 (fn-bs-run bs ks
                                   (fn-bs-frontier-program stage octets)
                                   nil groups capacity))) ino)
                  (fn-bs-fencedp
                   (car (nth 6 (fn-bs-run bs ks
                                  (fn-bs-frontier-program stage octets)
                                  nil groups capacity))) ino)))
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-frontier-dir-cut-is-fence
                 (:instance fn-bs-k0-frontier-rename-preserves-fencedp
                   (file (car (nth 6 (fn-bs-run bs ks
                          (fn-bs-frontier-program stage octets)
                          nil groups capacity)))))
                 (:instance fn-bs-k0-root-fence-preserves-fencedp
                   (file (mv-nth 1 (fn-bs-rename
                     (car (nth 6 (fn-bs-run bs ks
                            (fn-bs-frontier-program stage octets)
                            nil groups capacity)))
                     :staging stage :root *fn-bs-frontier-name* :ok)))))
           :in-theory (e/d (fn-bs-frontier-inputp)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-rename fn-bs-fence-dir fn-bs-fencedp
                            fn-bs-store-relation)))))

(defthm fn-bs-k0-frontier-dir-cut-preserves-fenced-list
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (equal
            (fn-bs-all-fencedp
             (car (nth 12 (fn-bs-run bs ks
                            (fn-bs-frontier-program stage octets)
                            nil groups capacity))) xs)
            (fn-bs-all-fencedp
             (car (nth 6 (fn-bs-run bs ks
                           (fn-bs-frontier-program stage octets)
                           nil groups capacity))) xs)))
  :rule-classes nil
  :hints (("Goal" :induct (len xs)
           :in-theory (e/d (fn-bs-all-fencedp)
                           (fn-bs-run fn-bs-frontier-program)))))

(defthm fn-bs-k0-frontier-file-observation-has-new-inode
  (implies (and (fn-bs-statep bs) (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage))
                (true-listp octets))
           (consp (assoc-equal (fn-bs-next-ino bs)
                              (fn-bs-inodes
                               (car (nth 6 (fn-bs-run bs ks
                                  (fn-bs-frontier-program stage octets)
                                  nil groups capacity)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-file-cut-is-record-file-cut
                 fn-bs-k0-frontier-file-observation-keeps-byte-state
                 (:instance fn-bs-k0-file-cut-has-new-inode
                            (frame octets)))
           :in-theory (disable fn-bs-run fn-bs-frontier-program
                               fn-bs-record-program fn-bs-inodes))))

(defthm fn-bs-k0-frontier-file-observation-new-inode-fenced
  (implies (and (fn-bs-statep bs) (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage))
                (true-listp octets))
           (fn-bs-fencedp
            (car (nth 6 (fn-bs-run bs ks
                           (fn-bs-frontier-program stage octets)
                           nil groups capacity)))
            (fn-bs-next-ino bs)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-file-cut-is-record-file-cut
                 fn-bs-k0-frontier-file-observation-keeps-byte-state
                 (:instance fn-bs-k6-file-cut-source-is-fenced-frame
                            (frame octets)))
           :in-theory (disable fn-bs-run fn-bs-frontier-program
                               fn-bs-record-program fn-bs-fencedp))))

(defthm fn-bs-k0-frontier-file-observation-authority-list-is-input
  (implies (and (fn-bs-statep bs) (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage))
                (true-listp octets))
           (equal (fn-bs-authority-inode-list
                   (car (nth 6 (fn-bs-run bs ks
                                  (fn-bs-frontier-program stage octets)
                                  nil groups capacity))))
                  (fn-bs-authority-inode-list bs)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-file-cut-authority-list-is-input
                 fn-bs-k0-frontier-file-observation-keeps-byte-state)
           :in-theory (disable fn-bs-run fn-bs-frontier-program
                               fn-bs-authority-inode-list))))

(defthm fn-bs-k0-replace-authority-target-preserves-fenced-list
  (implies (and (fn-bs-all-fencedp file
                                   (append (list config old)
                                           (append txns pending)))
                (fn-bs-fencedp file new))
           (fn-bs-all-fencedp file (append (list config new) txns)))
  :hints (("Goal" :induct (fn-bs-all-fencedp file txns)
           :in-theory (enable fn-bs-all-fencedp))))

(defthm fn-bs-k0-replace-authority-target-preserves-known-list
  (implies (and (fn-bs-inode-list-knownp file
                                   (append (list config old)
                                           (append txns pending)))
                (consp (assoc-equal new (fn-bs-inodes file))))
           (fn-bs-inode-list-knownp file (append (list config new) txns)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bs-inode-list-knownp file txns)
           :in-theory (enable fn-bs-inode-list-knownp))))

(defthm fn-bs-k0-known-list-equal-when-inodes-equal
  (implies (equal (fn-bs-inodes a) (fn-bs-inodes b))
           (equal (fn-bs-inode-list-knownp a xs)
                  (fn-bs-inode-list-knownp b xs)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bs-inode-list-knownp a xs)
           :in-theory (enable fn-bs-inode-list-knownp))))

(defthm fn-bs-k0-frontier-file-observation-authority-known
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (fn-bs-authority-knownp
            (car (nth 6 (fn-bs-run bs ks
                           (fn-bs-frontier-program stage octets)
                           nil groups capacity)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-file-observation-establishes-relation)
           :in-theory (e/d (fn-bs-store-relation)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-authority-knownp fn-bs-statep
                            fn-bs-authority-fencedp fn-bs-durable-records)))))

(defthm fn-bs-k0-frontier-dir-cut-preserves-known-list
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (equal
            (fn-bs-inode-list-knownp
             (car (nth 12 (fn-bs-run bs ks
                            (fn-bs-frontier-program stage octets)
                            nil groups capacity))) xs)
            (fn-bs-inode-list-knownp
             (car (nth 6 (fn-bs-run bs ks
                           (fn-bs-frontier-program stage octets)
                           nil groups capacity))) xs)))
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-dir-cut-keeps-inodes
                 (:instance fn-bs-k0-known-list-equal-when-inodes-equal
                   (a (car (nth 12 (fn-bs-run bs ks
                          (fn-bs-frontier-program stage octets)
                          nil groups capacity))))
                   (b (car (nth 6 (fn-bs-run bs ks
                          (fn-bs-frontier-program stage octets)
                          nil groups capacity))))))
           :in-theory (e/d (fn-bs-frontier-inputp)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-inode-list-knownp)))))

(defthm fn-bs-k0-frontier-dir-cut-authority-known
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (fn-bs-authority-knownp
            (car (nth 12 (fn-bs-run bs ks
                           (fn-bs-frontier-program stage octets)
                           nil groups capacity)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-frontier-file-observation-authority-known
                 fn-bs-k0-frontier-file-observation-authority-list-is-input
                 fn-bs-k0-frontier-file-observation-has-new-inode
                 fn-bs-k0-frontier-dir-cut-authority-list
                 (:instance fn-bs-k0-frontier-dir-cut-preserves-known-list
                   (xs (append (list (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*)
                                     (fn-bs-next-ino bs))
                               (strip-cdrs (cdr (assoc-equal :transactions
                                                            (fn-bs-dirs bs)))))))
                 (:instance fn-bs-k0-replace-authority-target-preserves-known-list
                   (file (car (nth 6 (fn-bs-run bs ks
                         (fn-bs-frontier-program stage octets)
                         nil groups capacity))))
                   (config (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*))
                   (old (fn-bs-durable-entry bs :root *fn-bs-scan-frontier-name*))
                   (new (fn-bs-next-ino bs))
                   (txns (strip-cdrs (cdr (assoc-equal :transactions (fn-bs-dirs bs)))))
                   (pending (fn-bs-pending-entry-targets (fn-bs-pending bs)))))
           :in-theory (e/d (fn-bs-authority-knownp fn-bs-authority-inode-list
                            fn-bs-frontier-inputp)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-inode-list-knownp fn-bs-store-relation)))))

(defthm fn-bs-k0-frontier-file-observation-authority-fenced
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (fn-bs-authority-fencedp
            (car (nth 6 (fn-bs-run bs ks
                           (fn-bs-frontier-program stage octets)
                           nil groups capacity)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-file-observation-establishes-relation
                 (:instance fn-bs-store-relation-unfolds
                   (bs (car (nth 6 (fn-bs-run bs ks
                         (fn-bs-frontier-program stage octets)
                         nil groups capacity))))
                   (ks (cdr (nth 6 (fn-bs-run bs ks
                         (fn-bs-frontier-program stage octets)
                         nil groups capacity))))))
           :in-theory (disable fn-bs-run fn-bs-frontier-program
                               fn-bs-store-relation fn-bs-authority-fencedp))))

(defthm fn-bs-k0-frontier-dir-cut-authority-fenced
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (fn-bs-authority-fencedp
            (car (nth 12 (fn-bs-run bs ks
                           (fn-bs-frontier-program stage octets)
                           nil groups capacity)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-frontier-file-observation-authority-fenced
                 fn-bs-k0-frontier-file-observation-authority-list-is-input
                 fn-bs-k0-frontier-file-observation-new-inode-fenced
                 fn-bs-k0-frontier-dir-cut-authority-list
                 (:instance fn-bs-k0-frontier-dir-cut-preserves-fenced-list
                   (xs (append (list (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*)
                                     (fn-bs-next-ino bs))
                               (strip-cdrs (cdr (assoc-equal :transactions
                                                            (fn-bs-dirs bs)))))))
                 (:instance fn-bs-k0-replace-authority-target-preserves-fenced-list
                   (file (car (nth 6 (fn-bs-run bs ks
                         (fn-bs-frontier-program stage octets)
                         nil groups capacity))))
                   (config (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*))
                   (old (fn-bs-durable-entry bs :root *fn-bs-scan-frontier-name*))
                   (new (fn-bs-next-ino bs))
                   (txns (strip-cdrs (cdr (assoc-equal :transactions (fn-bs-dirs bs)))))
                   (pending (fn-bs-pending-entry-targets (fn-bs-pending bs)))))
           :in-theory (e/d (fn-bs-authority-fencedp fn-bs-authority-inode-list
                            fn-bs-frontier-inputp)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-all-fencedp fn-bs-store-relation)))))

(defthm fn-bs-k0-frontier-dir-cut-establishes-relation
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (fn-bs-store-relation
            (car (nth 12 (fn-bs-run bs ks
                           (fn-bs-frontier-program stage octets)
                           nil groups capacity)))
            (cdr (nth 12 (fn-bs-run bs ks
                           (fn-bs-frontier-program stage octets)
                           nil groups capacity)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 (:instance fn-bs-k6-state-next-ino-is-inop)
                 fn-bs-k0-frontier-dir-cut-statep
                 fn-bs-k0-frontier-dir-cut-pending-matches-phase
                 fn-bs-k0-frontier-dir-cut-crash-imagep
                 fn-bs-k0-frontier-dir-cut-kernel-candidate-and-phase
                 fn-bs-k0-frontier-dir-cut-keeps-transaction-table
                 fn-bs-k0-frontier-file-cut-keeps-dirs
                 fn-bs-k0-frontier-file-observation-keeps-byte-state
                 fn-bs-k0-frontier-dir-cut-keeps-config-entry
                 fn-bs-k0-frontier-dir-cut-keeps-config-content
                 fn-bs-k0-frontier-dir-cut-durable-entry
                 fn-bs-k0-frontier-dir-cut-keeps-durable-records
                 fn-bs-k0-frontier-dir-cut-authority-known
                 fn-bs-k0-frontier-dir-cut-authority-fenced)
           :in-theory (e/d (fn-bs-store-relation fn-bs-frontier-inputp
                            fn-bs-durable-names fn-bs-contiguous-namesp
                            fn-bs-replay-visiblep fn-bs-inop)
                           (fn-bs-run fn-bs-frontier-program fn-bs-statep
                            fn-sf-statep fn-bs-durable-records
                            fn-bs-durable-frontier fn-bs-authority-knownp
                            fn-bs-authority-fencedp fn-bs-lookup
                            fn-bs-pending-matches-phase fn-sf-crash-imagep)))))

; The final host frontier callback follows the directory-fenced pair.
(local
 (defthm fn-bs-k0-frontier-reserved-suffix-starts-at-file-observation
  (implies (and (fn-bs-statep bs) (fn-bs-namep stage)
                (not (fn-bs-lookup bs :staging stage)) (true-listp octets))
           (equal (nth 14 (fn-bs-run bs ks
                                      (fn-bs-frontier-program stage octets)
                                      nil groups capacity))
                  (nth 7 (fn-bs-run
                          (car (nth 6 (fn-bs-run bs ks
                                                (fn-bs-frontier-program stage octets)
                                                nil groups capacity)))
                          (cdr (nth 6 (fn-bs-run bs ks
                                                (fn-bs-frontier-program stage octets)
                                                nil groups capacity)))
                          (nthcdr 7 (fn-bs-frontier-program stage octets))
                          nil groups capacity))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-file-cut-is-write-fence
                 fn-bs-k0-frontier-file-cut-source-is-new-inode
                 (:instance fn-bs-k6-write-created-inode-returns-ok-without-namep
                            (frame octets)))
           :in-theory (e/d (fn-bs-frontier-program fn-bs-run fn-bs-step
                            fn-bs-fsync-file)
                           (fn-bs-statep fn-bs-create fn-bs-write
                            fn-bs-fence-file fn-bs-lookup
                            fn-bs-fsync-dir fn-bs-rename)))))
)

(local
 (defthm fn-bs-k0-frontier-suffix-reserved-pair-is-directory-callback
  (implies (and (fn-bs-statep file)
                (fn-bs-inop (fn-bs-lookup file :staging stage)))
           (equal
            (nth 7 (fn-bs-run file fileks
                              (nthcdr 7 (fn-bs-frontier-program stage octets))
                              nil groups capacity))
            (cons
             (car (nth 5 (fn-bs-run file fileks
                                  (nthcdr 7 (fn-bs-frontier-program stage octets))
                                  nil groups capacity)))
             (fn-sf-frontier-dir-result
              (cdr (nth 5 (fn-bs-run file fileks
                                   (nthcdr 7 (fn-bs-frontier-program stage octets))
                                   nil groups capacity))) :ok))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-frontier-program fn-bs-run fn-bs-step
                            fn-sf-dispatch fn-bs-rename fn-bs-fsync-dir)
                           (fn-bs-statep fn-bs-lookup fn-bs-fence-dir
                            fn-sf-frontier-dir-result)))))
)

(defthm fn-bs-k0-frontier-reserved-pair-is-directory-callback
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (equal (nth 14 (fn-bs-run bs ks
                          (fn-bs-frontier-program stage octets)
                          nil groups capacity))
                  (cons (car (nth 12 (fn-bs-run bs ks
                          (fn-bs-frontier-program stage octets)
                          nil groups capacity)))
                        (fn-sf-frontier-dir-result
                         (cdr (nth 12 (fn-bs-run bs ks
                          (fn-bs-frontier-program stage octets)
                          nil groups capacity))) :ok))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-k0-frontier-reserved-suffix-starts-at-file-observation
                 fn-bs-k0-frontier-suffix-starts-at-file-observation
                 (:instance fn-bs-k0-frontier-suffix-reserved-pair-is-directory-callback
                   (file (car (nth 6 (fn-bs-run bs ks
                              (fn-bs-frontier-program stage octets)
                              nil groups capacity))))
                   (fileks (cdr (nth 6 (fn-bs-run bs ks
                              (fn-bs-frontier-program stage octets)
                              nil groups capacity)))))
                 fn-bs-k0-frontier-file-cut-statep
                 fn-bs-k0-frontier-file-observation-keeps-byte-state
                 fn-bs-k0-frontier-file-observation-source-is-new-inode
                 (:instance fn-bs-k6-state-next-ino-is-inop))
           :in-theory (e/d (fn-bs-frontier-inputp)
                           (fn-bs-run fn-bs-frontier-program
                            fn-bs-store-relation fn-bs-statep
                            fn-bs-lookup fn-sf-frontier-dir-result)))))

(defthm fn-bs-k0-frontier-reserved-cut-establishes-relation
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((pair (nth 14 (fn-bs-run bs ks
                                   (fn-bs-frontier-program stage octets)
                                   nil groups capacity))))
             (and (fn-bs-store-relation (car pair) (cdr pair))
                  (equal (fn-sf-phase (cdr pair)) :reserved))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-reserved-pair-is-directory-callback
                 fn-bs-k0-frontier-dir-cut-establishes-relation
                 fn-bs-k0-frontier-dir-cut-kernel-candidate-and-phase
                 fn-bs-k0-frontier-dir-cut-committedp
                 (:instance fn-bs-frontier-directory-commit-observation-preserves-relation
                  (bs (car (nth 12 (fn-bs-run bs ks
                              (fn-bs-frontier-program stage octets)
                              nil groups capacity))))
                  (ks (cdr (nth 12 (fn-bs-run bs ks
                              (fn-bs-frontier-program stage octets)
                              nil groups capacity))))))
           :in-theory (disable fn-bs-run fn-bs-frontier-program
                               fn-bs-store-relation
                               fn-bs-frontier-directory-committedp))))

; The native allocator reports the root-directory barrier through
; fnn-observe -> fn-store-sn-io -> fn-sn-io (host/native/io.lisp:1536,
; host/store-node-host.lisp:432).  Pair 12 is the cut after the physical
; fsync; pair 14 is the cut after this exact callback.  Starting from the
; related ready entry, all four native observation calls agree with the byte
; interpreter's kernel states.  The physical syscall-outcome and crash-image
; premises remain separate K0/platform obligations.
(include-book "byte-store-native-correspondence")
(include-book "store-node-invariants")

(defthm fn-bs-k0-frontier-native-call-sequence-matches-run
  (implies
   (and (fn-sn-statep s)
        (fn-bs-store-relation bs (fn-sn-files s))
        (fn-bs-frontier-inputp (fn-sn-files s) stage octets)
        (not (fn-bs-lookup bs :staging stage)))
   (let* ((s1 (fn-sn-io s :start-frontier :ok))
          (s2 (fn-sn-io s1 :frontier-file :ok))
          (s3 (fn-sn-io s2 :frontier-replace :ok))
          (s4 (fn-sn-io s3 :frontier-directory :ok))
          (run (fn-bs-run bs (fn-sn-files s)
                          (fn-bs-frontier-program stage octets)
                          nil groups capacity))
          (file-pair (nth 12 run))
          (return-pair (nth 14 run)))
     (and (equal (cdr file-pair) (fn-sn-files s3))
          (equal (car return-pair) (car file-pair))
          (equal (cdr return-pair) (fn-sn-files s4))
          (fn-bs-store-relation (car return-pair) (fn-sn-files s4))
          (equal (fn-sf-phase (fn-sn-files s4)) :reserved))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-frontier-dir-cut-kernel-is-replace-observation
                            (ks (fn-sn-files s)))
                 (:instance fn-bs-k0-frontier-reserved-pair-is-directory-callback
                            (ks (fn-sn-files s)))
                 (:instance fn-bs-k0-frontier-reserved-cut-establishes-relation
                            (ks (fn-sn-files s)))
                 (:instance fn-bs-native-io-is-byte-observation
                            (operation :start-frontier) (result :ok))
                 (:instance fn-bs-native-io-is-byte-observation
                            (s (fn-sn-io s :start-frontier :ok))
                            (operation :frontier-file) (result :ok))
                 (:instance fn-bs-native-io-is-byte-observation
                            (s (fn-sn-io (fn-sn-io s :start-frontier :ok)
                                         :frontier-file :ok))
                            (operation :frontier-replace) (result :ok))
                 (:instance fn-bs-native-io-is-byte-observation
                            (s (fn-sn-io (fn-sn-io
                                           (fn-sn-io s :start-frontier :ok)
                                           :frontier-file :ok)
                                         :frontier-replace :ok))
                            (operation :frontier-directory) (result :ok))
                 (:instance fn-sn-io-preserves-state
                            (operation :start-frontier) (result :ok))
                 (:instance fn-sn-io-preserves-state
                            (s (fn-sn-io s :start-frontier :ok))
                            (operation :frontier-file) (result :ok))
                 (:instance fn-sn-io-preserves-state
                            (s (fn-sn-io (fn-sn-io s :start-frontier :ok)
                                         :frontier-file :ok))
                            (operation :frontier-replace) (result :ok)))
           :in-theory (e/d (fn-sf-dispatch fn-bs-native-io-event)
                           (fn-bs-run fn-bs-frontier-program fn-sn-io
                            fn-bs-store-relation fn-sf-frontier-dir-result)))))

; The shared native service binds fnn-observe to fnn-owner-observe
; (host/native/owner.lisp:718).  It calls the program-mode fn-owner-io
; (host/owner-host.lisp:299), which submits exactly this event through
; fn-ocfg-step.  Expose the Store-node projection of that called path.
(include-book "owner-config")
(include-book "owner-invariants")

(defthm fn-bs-k0-owner-io-store-is-node-io
  (equal (fn-own-store
          (fn-ocfg-owner
           (fn-ocfg-step oc (list :store (list :io operation result)))))
         (fn-sn-io (fn-own-store (fn-ocfg-owner oc)) operation result))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ocfg-step fn-ocfg-pass fn-ocfg-with-owner
                            fn-own-step fn-own-store-step fn-snrt-step
                            fn-snt-step fn-own-refresh-keeps-fields)
                           (fn-own-refresh fn-sn-io fn-ocfg-make
                            fn-own-make)))))

(defthm fn-bs-k0-owner-frontier-calls-match-byte-run
  (implies
   (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
        (fn-bs-store-relation bs
                              (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
        (fn-bs-frontier-inputp
         (fn-sn-files (fn-own-store (fn-ocfg-owner oc))) stage octets)
        (not (fn-bs-lookup bs :staging stage)))
   (let* ((s (fn-own-store (fn-ocfg-owner oc)))
          (oc1 (fn-ocfg-step oc '(:store (:io :start-frontier :ok))))
          (oc2 (fn-ocfg-step oc1 '(:store (:io :frontier-file :ok))))
          (oc3 (fn-ocfg-step oc2 '(:store (:io :frontier-replace :ok))))
          (oc4 (fn-ocfg-step oc3 '(:store (:io :frontier-directory :ok))))
          (run (fn-bs-run bs (fn-sn-files s)
                          (fn-bs-frontier-program stage octets)
                          nil groups capacity))
          (file-pair (nth 12 run))
          (return-pair (nth 14 run)))
     (and (equal (fn-sn-files (fn-own-store (fn-ocfg-owner oc3)))
                 (cdr file-pair))
          (equal (car return-pair) (car file-pair))
          (equal (fn-sn-files (fn-own-store (fn-ocfg-owner oc4)))
                 (cdr return-pair))
          (fn-bs-store-relation
           (car return-pair)
           (fn-sn-files (fn-own-store (fn-ocfg-owner oc4))))
          (equal (fn-sf-phase
                  (fn-sn-files (fn-own-store (fn-ocfg-owner oc4))))
                 :reserved))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-frontier-native-call-sequence-matches-run
                            (s (fn-own-store (fn-ocfg-owner oc)))))
           :in-theory (union-theories
                       '(fn-bs-k0-owner-io-store-is-node-io)
                       (theory 'minimal-theory)))))

; P-FRONTIER's root-directory fsync can report EIO after the queued
; replacement has landed.  The host observes :frontier-directory :error and
; returns an indeterminate, fenced result; it does not acknowledge the new
; durable frontier.  This schedule chooses :apply explicitly.  :drop is also
; physically legal and is witnessed in the test book; neither syscall error
; nor this theorem implies a particular recovered frontier.
(defun fn-bs-k0-root-error-outcomes (choice)
  (declare (xargs :guard t :verify-guards nil))
  (list :ok :ok :ok :ok :ok :ok :ok :ok :ok :ok :ok :ok
        (list :eio choice)))

(local
 (defthm fn-bs-k0-root-eio-apply-is-fence
   (implies (and (equal (fn-bs-ops-for-dir (fn-bs-pending b) :root)
                        (list op))
                 (not (equal (car op) :write)))
            (equal (mv-nth 1 (fn-bs-fsync-dir b :root '(:eio :apply)))
                   (fn-bs-fence-dir b :root)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (enable fn-bs-fsync-dir fn-bs-fence-dir
                               fn-bs-crash-select)))))

(local
 (defthm fn-bs-k0-frontier-root-eio-apply-is-successful-byte-fence
   (implies (and (fn-bs-dir-quietp file :root)
                 (fn-bs-inop (fn-bs-lookup file :staging stage)))
            (equal
             (mv-nth 1 (fn-bs-fsync-dir
                        (mv-nth 1 (fn-bs-rename file :staging stage :root
                                                *fn-bs-frontier-name* :ok))
                        :root '(:eio :apply)))
             (fn-bs-fence-dir
              (mv-nth 1 (fn-bs-rename file :staging stage :root
                                      *fn-bs-frontier-name* :ok)) :root)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-k0-root-eio-apply-is-fence
                              (b (mv-nth 1 (fn-bs-rename file :staging stage
                                                          :root *fn-bs-frontier-name* :ok)))
                              (op (list :set-entry :root *fn-bs-frontier-name*
                                        (fn-bs-lookup file :staging stage)))))
            :in-theory (e/d (fn-bs-rename fn-bs-ops-for-dir-of-append
                             fn-bs-dir-quietp)
                            (fn-bs-fsync-dir fn-bs-fence-dir fn-bs-lookup))))))

(local
 (defthm fn-bs-k0-frontier-root-eio-apply-reaches-durable-cut
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-frontier-inputp ks stage octets)
                 (not (fn-bs-lookup bs :staging stage)))
            (let* ((run (fn-bs-run bs ks (fn-bs-frontier-program stage octets)
                                   nil groups capacity))
                   (file (car (nth 6 run))))
              (equal (mv-nth 1
                      (fn-bs-fsync-dir
                       (mv-nth 1 (fn-bs-rename file :staging stage :root
                                               *fn-bs-frontier-name* :ok))
                       :root '(:eio :apply)))
                     (car (nth 12 run)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use (fn-bs-store-relation-unfolds
                  fn-bs-k0-frontier-file-cut-authority-quiet
                  fn-bs-k0-frontier-file-observation-keeps-byte-state
                  fn-bs-k0-frontier-file-observation-source-is-new-inode
                  fn-bs-k0-frontier-dir-cut-is-fence
                  (:instance fn-bs-k6-state-next-ino-is-inop)
                  (:instance fn-bs-k0-frontier-root-eio-apply-is-successful-byte-fence
                   (file (car (nth 6 (fn-bs-run bs ks
                                (fn-bs-frontier-program stage octets)
                                nil groups capacity))))))
            :in-theory (e/d (fn-bs-dir-quietp fn-bs-frontier-inputp)
                            (fn-bs-run fn-bs-frontier-program fn-bs-statep
                             fn-bs-store-relation fn-bs-lookup fn-bs-fsync-dir
                             fn-bs-rename fn-bs-fence-dir fn-bs-inop))))))

(defthm fn-bs-k0-frontier-node-root-eio-applied-fences-related-state
  (implies
   (and (fn-sn-statep s)
        (fn-bs-store-relation bs (fn-sn-files s))
        (fn-bs-frontier-inputp (fn-sn-files s) stage octets)
        (not (fn-bs-lookup bs :staging stage)))
   (let* ((ks (fn-sn-files s))
          (run (fn-bs-run bs ks (fn-bs-frontier-program stage octets)
                          nil groups capacity))
          (file (car (nth 6 run)))
          (failed (mv-nth 1 (fn-bs-fsync-dir
                             (mv-nth 1 (fn-bs-rename file :staging stage
                                                     :root *fn-bs-frontier-name* :ok))
                             :root '(:eio :apply))))
          (s3 (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier :ok)
                                      :frontier-file :ok)
                        :frontier-replace :ok))
          (s4 (fn-sn-io s3 :frontier-directory :error)))
     (and (equal failed (car (nth 12 run)))
          (fn-bs-store-relation failed (fn-sn-files s4))
          (equal (fn-sf-phase (fn-sn-files s4)) :fenced-frontier)
          (equal (fn-bs-durable-frontier failed)
                 (fn-sf-frontier-candidate (fn-sn-files s3))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-frontier-native-call-sequence-matches-run)
                 (:instance fn-bs-k0-frontier-dir-cut-establishes-relation
                  (ks (fn-sn-files s)))
                 (:instance fn-bs-k0-frontier-dir-cut-kernel-candidate-and-phase
                  (ks (fn-sn-files s)))
                 (:instance fn-bs-k0-frontier-root-eio-apply-reaches-durable-cut
                  (ks (fn-sn-files s)))
                 (:instance fn-bs-k0-frontier-dir-cut-committedp
                  (ks (fn-sn-files s)))
                 (:instance fn-bs-frontier-dir-error-preserves-relation
                  (bs (car (nth 12 (fn-bs-run bs (fn-sn-files s)
                                    (fn-bs-frontier-program stage octets)
                                    nil groups capacity))))
                  (ks (cdr (nth 12 (fn-bs-run bs (fn-sn-files s)
                                    (fn-bs-frontier-program stage octets)
                                    nil groups capacity)))))
                 (:instance fn-bs-native-io-is-byte-observation
                  (s (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier :ok)
                                       :frontier-file :ok)
                                 :frontier-replace :ok))
                  (operation :frontier-directory) (result :error))
                 (:instance fn-sn-io-preserves-state
                  (operation :start-frontier) (result :ok))
                 (:instance fn-sn-io-preserves-state
                  (s (fn-sn-io s :start-frontier :ok))
                  (operation :frontier-file) (result :ok))
                 (:instance fn-sn-io-preserves-state
                  (s (fn-sn-io (fn-sn-io s :start-frontier :ok)
                               :frontier-file :ok))
                  (operation :frontier-replace) (result :ok)))
           :in-theory (e/d (fn-bs-native-io-event fn-sf-dispatch
                            fn-sf-frontier-dir-result fn-sf-fencedp)
                           (fn-bs-run fn-bs-frontier-program fn-sn-io
                            fn-bs-store-relation fn-bs-durable-frontier)))))

(defthm fn-bs-k0-frontier-eio-applied-run-has-actual-failed-cut
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (equal
            (car (nth 12
                  (fn-bs-run bs ks (fn-bs-frontier-program stage octets)
                             (fn-bs-k0-root-error-outcomes :apply)
                             groups capacity)))
            (car (nth 12
                  (fn-bs-run bs ks (fn-bs-frontier-program stage octets)
                             nil groups capacity)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-root-eio-apply-reaches-durable-cut
                 fn-bs-k0-frontier-file-cut-is-write-fence
                 fn-bs-k0-frontier-replace-cut-is-rename
                 fn-bs-k0-frontier-rename-returns-ok
                 fn-bs-k0-frontier-file-observation-source-is-new-inode)
           :in-theory (e/d (fn-bs-k0-root-error-outcomes
                            fn-bs-frontier-program fn-bs-run fn-bs-step)
                           (fn-bs-create fn-bs-write fn-bs-fsync-file
                            fn-bs-rename fn-bs-fsync-dir fn-bs-fence-file
                            fn-bs-fence-dir fn-bs-lookup
                            fn-bs-statep fn-bs-store-relation)))))

(local
 (defthm fn-bs-k0-owner-frontier-root-eio-applied-fences-related-state
   (implies
    (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
         (fn-bs-store-relation bs
                               (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
         (fn-bs-frontier-inputp
          (fn-sn-files (fn-own-store (fn-ocfg-owner oc))) stage octets)
         (not (fn-bs-lookup bs :staging stage)))
    (let* ((s (fn-own-store (fn-ocfg-owner oc)))
           (run (fn-bs-run bs (fn-sn-files s)
                           (fn-bs-frontier-program stage octets)
                           nil groups capacity))
           (file (car (nth 6 run)))
           (renamed (mv-nth 1 (fn-bs-rename file :staging stage :root
                                             *fn-bs-frontier-name* :ok)))
           (result (mv-nth 0 (fn-bs-fsync-dir renamed :root '(:eio :apply))))
           (failed (mv-nth 1 (fn-bs-fsync-dir renamed :root '(:eio :apply))))
           (oc1 (fn-ocfg-step oc '(:store (:io :start-frontier :ok))))
           (oc2 (fn-ocfg-step oc1 '(:store (:io :frontier-file :ok))))
           (oc3 (fn-ocfg-step oc2 '(:store (:io :frontier-replace :ok))))
           (oc4 (fn-ocfg-step oc3 '(:store (:io :frontier-directory :error))))
           (k3 (fn-sn-files (fn-own-store (fn-ocfg-owner oc3))))
           (k4 (fn-sn-files (fn-own-store (fn-ocfg-owner oc4)))))
      (and (equal result :eio)
           (equal failed (car (nth 12 run)))
           (fn-bs-store-relation failed k4)
           (equal (fn-sf-phase k4) :fenced-frontier)
           (equal (fn-bs-durable-frontier failed)
                  (fn-sf-frontier-candidate k3)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-k0-frontier-node-root-eio-applied-fences-related-state
                   (s (fn-own-store (fn-ocfg-owner oc)))))
            :in-theory (union-theories
                        '(fn-bs-k0-owner-io-store-is-node-io fn-bs-fsync-dir)
                        (theory 'minimal-theory))))))

; The public K0 error bridge names the actual owner callback and the actual
; failing byte-program cut.  It promises a recovery fence, not reservation.
(defthm fn-bs-k0-owner-frontier-root-eio-applied-run-fences-related-state
  (implies
   (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
        (fn-bs-store-relation bs
                              (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))
        (fn-bs-frontier-inputp
         (fn-sn-files (fn-own-store (fn-ocfg-owner oc))) stage octets)
        (not (fn-bs-lookup bs :staging stage)))
   (let* ((s (fn-own-store (fn-ocfg-owner oc)))
          (run (fn-bs-run bs (fn-sn-files s)
                          (fn-bs-frontier-program stage octets)
                          (fn-bs-k0-root-error-outcomes :apply)
                          groups capacity))
          (failed (car (nth 12 run)))
          (oc1 (fn-ocfg-step oc '(:store (:io :start-frontier :ok))))
          (oc2 (fn-ocfg-step oc1 '(:store (:io :frontier-file :ok))))
          (oc3 (fn-ocfg-step oc2 '(:store (:io :frontier-replace :ok))))
          (oc4 (fn-ocfg-step oc3 '(:store (:io :frontier-directory :error))))
          (k3 (fn-sn-files (fn-own-store (fn-ocfg-owner oc3))))
          (k4 (fn-sn-files (fn-own-store (fn-ocfg-owner oc4)))))
     (and (fn-bs-store-relation failed k4)
          (equal (fn-sf-phase k4) :fenced-frontier)
          (equal (fn-bs-durable-frontier failed)
                 (fn-sf-frontier-candidate k3)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-owner-frontier-root-eio-applied-fences-related-state)
                 (:instance fn-bs-k0-frontier-eio-applied-run-has-actual-failed-cut
                  (ks (fn-sn-files (fn-own-store (fn-ocfg-owner oc))))))
           :in-theory (theory 'minimal-theory))))
