; A barrier certifies its captured prefix. A later aligned write can remain
; pending even when the barrier returns :ok. Keep the existing byte-store
; semantics for that prefix, including fsyncgate's uncertain failure.
(in-package "ACL2")
(include-book "store-log-pipeline")
(local (in-theory (disable (tau-system))))

(defun fn-bs-pipe-with-pending (bs pending)
  (declare (xargs :guard t))
  (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs)
              pending (fn-bs-next-ino bs)))

(defun fn-bs-pipe-fsync-prefix (bs ino n outcome)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((pending (fn-bs-pending bs))
         (prefix (fn-bs-pipe-with-pending bs (fn-bs-take n pending))))
    (mv-let (word after) (fn-bs-fsync-file prefix ino outcome)
      (mv word (fn-bs-pipe-with-pending
                after (append (fn-bs-pending after) (nthcdr (nfix n) pending)))))))

; BASE has the existing one-batch relation. TAIL is the later write,
; whose pending status conservatively includes every possible crash landing.
; This representation extends R; it does not change any old R theorem.
(defun fn-lgk-pipe-store-linkp (bs base ks tail ino genesis max)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bs-shapep base) (true-listp (fn-bs-pending base))
       (fn-lgk-relp base ks ino genesis max)
       (equal bs (fn-bs-pipe-with-pending base (append (fn-bs-pending base) tail)))
       (fn-lgu-writes-at-or-above tail ino
          (fn-lgk-frontier (fn-lgk-fence ks (fn-bs-unit base))))))

(local
 (defthm fn-bs-pipe-take-append-prefix
  (implies (true-listp a) (equal (fn-bs-take (len a) (append a b)) a))
  :hints (("Goal" :induct (len a)))))
(local
 (defthm fn-bs-pipe-nthcdr-append-prefix
  (equal (nthcdr (len a) (append a b)) b)
  :hints (("Goal" :induct (len a)
           :in-theory (disable fn-lgc-nthcdr-of-append-shorter)))))
(local
 (defthm fn-bs-pipe-rebuild
  (implies (fn-bs-shapep bs)
    (equal (fn-bs-pipe-with-pending bs (fn-bs-pending bs)) bs))
  :hints (("Goal" :in-theory
           (enable fn-bs-shapep fn-bs-pipe-with-pending fn-bs-make
                   fn-bs-unit fn-bs-inodes fn-bs-dirs fn-bs-pending fn-bs-next-ino)))))

(defthm fn-bs-pipe-prefix-barrier-keeps-the-late-tail
  (implies (and (fn-bs-shapep base) (true-listp (fn-bs-pending base)))
    (equal
     (fn-bs-pipe-fsync-prefix
       (fn-bs-pipe-with-pending base (append (fn-bs-pending base) tail))
       ino (len (fn-bs-pending base)) outcome)
     (let ((after (mv-nth 1 (fn-bs-fsync-file base ino outcome))))
       (list (mv-nth 0 (fn-bs-fsync-file base ino outcome))
             (fn-bs-pipe-with-pending after (append (fn-bs-pending after) tail))))))
  :hints (("Goal" :use ((:instance fn-bs-pipe-rebuild (bs base)))
           :in-theory
           (e/d (fn-bs-pipe-fsync-prefix fn-bs-pipe-with-pending)
                (fn-bs-pipe-rebuild fn-bs-fsync-file fn-bs-make fn-bs-unit fn-bs-inodes
                 fn-bs-dirs fn-bs-pending fn-bs-next-ino fn-bs-take nthcdr)))))

(local
 (defthm fn-bs-pipe-writes-append
  (equal (fn-lgu-writes-at-or-above (append a b) ino f)
         (and (fn-lgu-writes-at-or-above a ino f)
              (fn-lgu-writes-at-or-above b ino f)))
  :hints (("Goal" :induct (append a b) :in-theory (enable fn-lgu-writes-at-or-above)))))

(defthm fn-bs-pipe-late-tail-keeps-safe
  (implies (and (fn-lgu-safep base ks ino genesis max)
                (fn-lgu-writes-at-or-above tail ino (fn-lgk-frontier ks)))
    (fn-lgu-safep
      (fn-bs-pipe-with-pending base (append (fn-bs-pending base) tail))
      ks ino genesis max))
  :hints (("Goal" :in-theory
           (e/d (fn-lgu-safep fn-bs-pipe-with-pending fn-bs-durable-content)
                (fn-lg-scan fn-bs-take fn-lgk-frontier fn-lgk-committed fn-lgk-acked
                 fn-lgu-writes-at-or-above)))))

(defthm fn-lgk-pipe-prefix-fence-safe
  (implies (fn-lgk-pipe-store-linkp bs base ks tail ino genesis max)
    (fn-lgu-safep
      (mv-nth 1 (fn-bs-pipe-fsync-prefix bs ino (len (fn-bs-pending base)) :ok))
      (fn-lgk-fence ks (fn-bs-unit base)) ino genesis max))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgk-fence-preserves-relation (bs base))
                 (:instance fn-lgu-related-state-is-safe
                    (bs (mv-nth 1 (fn-bs-fsync-file base ino :ok)))
                    (ks (fn-lgk-fence ks (fn-bs-unit base)))))
           :in-theory (e/d (fn-lgk-pipe-store-linkp)
                            (fn-bs-pipe-fsync-prefix fn-lgk-relp fn-lgu-safep
                             fn-lgk-fence fn-bs-fsync-file fn-bs-pipe-with-pending)))))

(defthm fn-lgk-pipe-prefix-fence-crash-recovers-acknowledged
  (implies (and (fn-lgk-pipe-store-linkp bs base ks tail ino genesis max) (fn-bs-crash-imagep (mv-nth 1 (fn-bs-pipe-fsync-prefix bs ino (len (fn-bs-pending base)) :ok)) image))
    (and (<= (fn-lgk-acked (fn-lgk-fence ks (fn-bs-unit base))) (len (fn-lgk-committed (fn-lgk-recover (fn-bs-durable-content image ino) genesis (fn-bs-unit (mv-nth 1 (fn-bs-pipe-fsync-prefix bs ino (len (fn-bs-pending base)) :ok))) max next-txid)))) (equal (take (fn-lgk-acked (fn-lgk-fence ks (fn-bs-unit base))) (fn-lgk-committed (fn-lgk-recover (fn-bs-durable-content image ino) genesis (fn-bs-unit (mv-nth 1 (fn-bs-pipe-fsync-prefix bs ino (len (fn-bs-pending base)) :ok))) max next-txid))) (take (fn-lgk-acked (fn-lgk-fence ks (fn-bs-unit base))) (fn-lgk-committed (fn-lgk-fence ks (fn-bs-unit base)))))))
  :rule-classes nil
  :hints (("Goal" :use (fn-lgk-pipe-prefix-fence-safe
                        (:instance fn-lgu-safe-image-recovers-the-acknowledged-records
                          (bs (mv-nth 1 (fn-bs-pipe-fsync-prefix bs ino (len (fn-bs-pending base)) :ok)))
                          (ks (fn-lgk-fence ks (fn-bs-unit base)))))
           :in-theory (disable fn-lgk-pipe-store-linkp fn-bs-pipe-fsync-prefix fn-lgu-safep
                                fn-lgk-pipe-prefix-fence-safe fn-lgu-safe-image-recovers-the-acknowledged-records
                                fn-lgk-fence fn-lgk-recover fn-lgk-committed fn-lgk-acked
                                fn-bs-durable-content fn-bs-crash-imagep fn-bs-unit take))))

(local
 (defthm fn-lgk-pipe-fence-frontier-monotone
  (<= (fn-lgk-frontier ks) (fn-lgk-frontier (fn-lgk-fence ks unit)))
  :hints (("Goal" :in-theory (e/d (fn-lgk-fence fn-lgk-frontier)
                                  (fn-lg-log fn-lg-last-trailer))))))
 (defthm fn-lgk-pipe-writes-weaken
  (implies (and (fn-lgu-writes-at-or-above ops ino high) (<= (nfix low) (nfix high)))
           (fn-lgu-writes-at-or-above ops ino low))
  :hints (("Goal" :induct (fn-lgu-writes-at-or-above ops ino high)
           :in-theory (enable fn-lgu-writes-at-or-above))))

(defthm fn-lgk-pipe-prefix-failure-keeps-durable-prefix
  (implies (fn-lgk-pipe-store-linkp bs base ks tail ino genesis max)
    (fn-lgu-safep
      (mv-nth 1 (fn-bs-pipe-fsync-prefix bs ino (len (fn-bs-pending base)) outcome))
      ks ino genesis max))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgu-related-state-is-safe (bs base))
                 (:instance fn-lgu-fsync-keeps-safe (bs base))
                 (:instance fn-lgk-pipe-fence-frontier-monotone (unit (fn-bs-unit base)))
                 (:instance fn-lgk-pipe-writes-weaken (ops tail)
                    (low (fn-lgk-frontier ks))
                    (high (fn-lgk-frontier (fn-lgk-fence ks (fn-bs-unit base))))))
           :in-theory (e/d (fn-lgk-pipe-store-linkp)
                            (fn-lgk-relp fn-lgu-safep fn-bs-pipe-fsync-prefix
                             fn-bs-fsync-file fn-bs-pipe-with-pending fn-lgk-fence
                             fn-lgk-frontier fn-lgu-writes-at-or-above)))))

(local
 (defthm fn-lgk-pipe-okp-ack-limit
  (implies (fn-lgk-pipe-okp p h)
    (<= (fn-lgk-acked (fn-lgk-pipe-ks p))
        (len (fn-lgk-committed (fn-lgk-pipe-ks p)))))
  :hints (("Goal" :in-theory (e/d (fn-lgk-pipe-okp)
                                (fn-lgk-pipe-ks fn-lgk-acked fn-lgk-committed))))))

(defthm fn-lgk-pipe-ack-keeps-store-safe
  (implies (and (fn-lgk-pipe-okp p h)
                (fn-lgu-safep bs (fn-lgk-pipe-ks p) ino genesis max))
    (fn-lgu-safep bs (fn-lgk-pipe-ks (fn-lgk-pipe-ack p n)) ino genesis max))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgk-pipe-okp-ack-limit (p (fn-lgk-pipe-ack p n)))
                 (:instance fn-lgu-safep-when-fields-agree
                            (ks (fn-lgk-pipe-ks p))
                            (k2 (fn-lgk-pipe-ks (fn-lgk-pipe-ack p n)))))
           :in-theory (disable fn-lgk-pipe-okp fn-lgu-safep fn-lgk-pipe-ks
                             fn-lgk-pipe-okp-ack-limit fn-lgk-pipe-ack
                             fn-lgk-frontier fn-lgk-committed fn-lgk-acked))))

; The host executes this write plan, not a separately computed offset.
(defun fn-lgk-pipe-physical-append (bs p ino extent outcome)
  (declare (xargs :guard t :verify-guards nil))
  (let ((plan (fn-lgk-behind-effect p (fn-bs-unit bs) extent)))
    (if (equal (car plan) :write)
        (fn-bs-write bs ino (nth 1 plan) (nth 2 plan) outcome)
      (mv :refused bs))))

(defthm fn-lgk-behind-write-starts-after-captured-prefix
  (implies (and (fn-lgk-pipe-okp p h)
                (equal (fn-lgk-phase (fn-lgk-pipe-ks p)) :appended)
                (fn-lgk-behind-admitsp p unit extent))
    (equal (nth 1 (fn-lgk-behind-effect p unit extent))
           (fn-lgk-frontier (fn-lgk-fence (fn-lgk-pipe-ks p) unit))))
  :hints (("Goal" :in-theory
           (e/d (fn-lgk-behind-effect fn-lgk-append-behind fn-lgk-behind-write
                  fn-lgk-pipe-fence fn-lgk-pipe-kernel-fence fn-lgk-pipe-ks
                  fn-lgk-pipe-make fn-lgk-pipe-countedp fn-lgk-pipe-okp)
                (fn-lgk-fence fn-lgc-fence fn-lgk-frontier fn-lgk-phase)))))

(local
 (defthm fn-bs-pipe-nthcdr-end
  (implies (true-listp a) (equal (nthcdr (len a) a) nil))
  :hints (("Goal" :induct (len a)))))

(defthm fn-lgk-pipe-physical-append-establishes-link
  (implies (and (fn-bs-shapep bs) (true-listp (fn-bs-pending bs)) (fn-lgk-pipe-okp p h) (fn-lgk-relp bs (fn-lgk-pipe-ks p) ino genesis max) (equal (fn-lgk-phase (fn-lgk-pipe-ks p)) :appended) (fn-lgk-behind-admitsp p (fn-bs-unit bs) extent))
    (fn-lgk-pipe-store-linkp (mv-nth 1 (fn-lgk-pipe-physical-append bs p ino extent outcome)) bs (fn-lgk-pipe-ks p) (nthcdr (len (fn-bs-pending bs)) (fn-bs-pending (mv-nth 1 (fn-lgk-pipe-physical-append bs p ino extent outcome)))) ino genesis max))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgk-behind-write-starts-after-captured-prefix
                             (unit (fn-bs-unit bs)))
                 (:instance fn-bs-pipe-rebuild (bs bs)))
           :in-theory
           (e/d (fn-lgk-pipe-physical-append fn-lgk-pipe-store-linkp
                  fn-bs-write fn-bs-pipe-with-pending fn-lgu-writes-at-or-above)
                (fn-lgk-relp fn-lgk-pipe-okp fn-lgk-pipe-ks fn-lgk-phase
                 fn-lgk-behind-effect fn-lgk-behind-admitsp fn-lgk-fence
                 fn-lgk-frontier fn-bs-shapep fn-bs-take fn-bs-pipe-rebuild)))))

(local
 (defthm fn-bs-pipe-fsync-shapedp
  (fn-bs-shapep (mv-nth 1 (fn-bs-fsync-file bs ino outcome)))
  :hints (("Goal" :in-theory (enable fn-bs-fsync-file fn-bs-fence-file)))))
(local
 (defthm fn-bs-pipe-take-end
  (implies (true-listp a) (equal (fn-bs-take (len a) a) a))
  :hints (("Goal" :induct (len a) :in-theory (enable fn-bs-take)))))
(local
 (defthm fn-bs-pipe-full-prefix
  (implies (and (fn-bs-shapep bs) (true-listp (fn-bs-pending bs)))
    (equal (fn-bs-pipe-fsync-prefix bs ino (len (fn-bs-pending bs)) outcome)
           (fn-bs-fsync-file bs ino outcome)))
  :hints (("Goal" :in-theory
            (e/d (fn-bs-pipe-fsync-prefix fn-bs-fsync-file fn-bs-fence-file
                   fn-bs-pipe-with-pending)
                 (fn-bs-take fn-bs-ops-for-ino fn-bs-ops-not-for-ino fn-bs-apply-ops))))))

; The successful captured barrier can be commuted before the later append:
; it yields the same abstract byte store, with B still pending. This is the
; equation that lets promotion reuse the existing single-batch relation.
(defthm fn-bs-pipe-prefix-write-commutes
  (implies (and (fn-bs-shapep bs) (true-listp (fn-bs-pending bs))
                (assoc-equal ino (fn-bs-inodes bs))
                (assoc-equal ino (fn-bs-inodes (mv-nth 1 (fn-bs-fsync-file bs ino :ok)))))
    (equal
     (mv-nth 1
       (fn-bs-pipe-fsync-prefix
         (mv-nth 1 (fn-bs-write bs ino off octets :ok))
         ino (len (fn-bs-pending bs)) :ok))
     (mv-nth 1
       (fn-bs-write (mv-nth 1 (fn-bs-fsync-file bs ino :ok))
                    ino off octets :ok))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-pipe-rebuild (bs bs))
                 (:instance fn-bs-pipe-prefix-barrier-keeps-the-late-tail
                   (base bs) (tail (list (list :write ino off (fn-bs-take (len octets) octets))))
                   (outcome :ok)))
           :in-theory
           (e/d (fn-bs-write fn-bs-pipe-with-pending)
                (fn-bs-pipe-fsync-prefix fn-bs-fsync-file fn-bs-pipe-rebuild
                 fn-bs-take fn-bs-shapep fn-bs-pipe-prefix-barrier-keeps-the-late-tail)))))

(local
 (defthm fn-bs-pipe-fsync-unit
  (equal (fn-bs-unit (mv-nth 1 (fn-bs-fsync-file bs ino outcome))) (fn-bs-unit bs))
  :hints (("Goal" :in-theory (enable fn-bs-fsync-file fn-bs-fence-file)))))

(local
 (defthm fn-lgk-pipe-physical-fence-fields
  (and (equal (fn-lgk-phase (fn-lgk-fence ks unit)) :fenced)
       (not (fn-lgk-inflight (fn-lgk-fence ks unit))))
  :hints (("Goal" :in-theory (e/d (fn-lgk-fence fn-lgk-phase fn-lgk-inflight)
                                (fn-lg-log fn-lg-last-trailer))))))
(local
 (defthm fn-lgk-pipe-physical-write-plan
  (implies (and (fn-lgk-pipe-okp p h)
                (equal (fn-lgk-phase (fn-lgk-pipe-ks p)) :appended)
                (fn-lgk-behind-admitsp p unit extent))
    (equal (fn-lgk-behind-effect p unit extent)
           (let ((ks (fn-lgk-fence (fn-lgk-pipe-ks p) unit)))
             (list :write (fn-lgk-frontier ks) (fn-lgk-append-octets ks unit)))))
  :hints (("Goal" :use (fn-lgk-behind-promotion-keeps-write-plan)
           :in-theory
           (e/d (fn-lgk-pipe-fence fn-lgk-pipe-kernel-fence fn-lgk-pipe-ks
                  fn-lgk-pipe-make fn-lgk-pipe-countedp fn-lgk-pipe-okp)
                (fn-lgk-fence fn-lgc-fence fn-lgk-frontier fn-lgk-phase
                 fn-lgk-append-octets fn-lgk-behind-effect fn-lgk-behind-admitsp))))))

(defthm fn-lgk-pipe-promotion-restores-relation
  (implies (and (fn-bs-shapep bs) (true-listp (fn-bs-pending bs)) (fn-lgk-pipe-okp p h) (fn-lgk-relp bs (fn-lgk-pipe-ks p) ino genesis max) (equal (fn-lgk-phase (fn-lgk-pipe-ks p)) :appended) (fn-lgk-behind-admitsp p (fn-bs-unit bs) extent) (fn-lgk-fitsp (fn-lgk-fence (fn-lgk-pipe-ks p) (fn-bs-unit bs)) (fn-bs-unit bs) (len (fn-bs-durable-content (mv-nth 1 (fn-bs-fsync-file bs ino :ok)) ino))))
    (fn-lgk-relp (mv-nth 1 (fn-bs-pipe-fsync-prefix (mv-nth 1 (fn-lgk-pipe-physical-append bs p ino extent :ok)) ino (len (fn-bs-pending bs)) :ok)) (fn-lgk-append (fn-lgk-fence (fn-lgk-pipe-ks p) (fn-bs-unit bs)) (fn-bs-unit bs) (len (fn-bs-durable-content (mv-nth 1 (fn-bs-fsync-file bs ino :ok)) ino))) ino genesis max))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-pipe-prefix-write-commutes
                   (off (fn-lgk-frontier (fn-lgk-fence (fn-lgk-pipe-ks p) (fn-bs-unit bs))))
                   (octets (fn-lgk-append-octets (fn-lgk-fence (fn-lgk-pipe-ks p) (fn-bs-unit bs)) (fn-bs-unit bs))))
                 (:instance fn-lg-relp-names-an-inode (ks (fn-lgk-pipe-ks p)))
                 (:instance fn-lg-relp-names-an-inode
                   (bs (mv-nth 1 (fn-bs-fsync-file bs ino :ok)))
                   (ks (fn-lgk-fence (fn-lgk-pipe-ks p) (fn-bs-unit bs))))
                 (:instance fn-lgk-pipe-physical-write-plan (unit (fn-bs-unit bs)))
                 (:instance fn-lgk-fence-preserves-relation (ks (fn-lgk-pipe-ks p)))
                 (:instance fn-lgk-append-preserves-relation
                   (bs (mv-nth 1 (fn-bs-fsync-file bs ino :ok)))
                   (ks (fn-lgk-fence (fn-lgk-pipe-ks p) (fn-bs-unit bs)))))
           :in-theory
           (e/d (fn-lgk-pipe-physical-append)
                (fn-bs-pipe-prefix-write-commutes fn-lgk-fence-preserves-relation
                 fn-lg-relp-names-an-inode fn-lgk-pipe-physical-write-plan
                 fn-lgk-pipe-ks fn-lgk-pipe-okp fn-lgk-relp fn-bs-fsync-file fn-bs-write
                 fn-bs-pipe-fsync-prefix fn-lgk-behind-effect fn-lgk-behind-admitsp
                 fn-lgk-append fn-lgk-fence fn-lgk-fitsp fn-lgk-frontier fn-lgk-phase
                 fn-lgk-append-octets fn-bs-durable-content)))))
