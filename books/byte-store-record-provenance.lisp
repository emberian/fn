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
