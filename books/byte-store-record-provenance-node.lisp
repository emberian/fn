; K0 byte provenance joined to the Store node: books/byte-store-record-provenance
; includes this book after its byte-store part.
(in-package "ACL2")
(include-book "byte-store-record-provenance-bytes")
(local (in-theory (enable fn-bs-k6-created-stage-lookup-without-namep
                           fn-bs-k6-fresh-create-returns-ok
                           fn-bs-k6-write-created-inode-returns-ok-without-namep
                           fn-bs-k6-write-keeps-lookup
                           fn-bs-k6-lookup-is-entry-after
                           fn-bs-k6-file-fence-keeps-valid-name-lookup
                           fn-bs-k6-created-stage-lookup
                           fn-bs-k0-append-associative
                           fn-bs-k6-empty-true-list
                           fn-bs-k6-state-next-ino-is-fenced
                           fn-bs-k6-take-all
                           fn-bs-k0-durable-state-content-is-durable-content
                           fn-bs-k6-filter-inode-writes-keeps-dir-ops
                           fn-bs-k6-file-fence-pending-is-filter
                           fn-bs-k6-filter-writes-keeps-entry-after
                           fn-bs-k0-all-fencedp-append
                           fn-bs-k0-inode-list-knownp-append)))

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
                             fn-bs-store-relation fn-bs-ops-for-dir)))))

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
                             fn-bs-replay-matches-scan)))))

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
                            fn-bs-fence-file fn-bs-lookup fn-bs-rename)))))

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
                            fn-bs-lookup fn-bs-inop)))))

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
                            fn-bs-fence-file fn-bs-fence-dir fn-bs-lookup fn-bs-rename)))))

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
                               fn-bs-lookup))))

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

; Proof steps the owner part reuses; exported disabled.
(in-theory (disable fn-bs-k0-frontier-rename-returns-ok))
