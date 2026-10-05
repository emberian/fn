; fn: recovery that never writes below the frontier (RL-01, option A2; lane
; m1-durable-2, 2026-10-04; ember's GO 2026-10-04; design
; build/coordinator/lanedumps/m1-durable.md, "A2 design v3").
;
; THE DEFECT.  After a failed log barrier Linux marks the unwritten pages
; clean and keeps them readable; the restarted open reads the failed batch
; as history, acknowledges later batches after it, and a power loss leaves a
; hole under the batch with acknowledged entries beyond it.  The byte model
; (books/byte-store.lisp) cannot say this: its process view is the durable
; tables with the pending operations applied, and a failed fsync discards
; what it did not land.  This book adds the missing state.
;
; THE CACHE MODEL (fn-bsc).  A store with a cache is the byte store BS and
; the VISIBLE tables, what read(2) and lookup observe:
;   a syscall changes BS as books/byte-store.lisp says and the visible
;     tables at once (the page and dentry caches);
;   a successful fsync changes BS only (what was visible becomes durable);
;   a FAILED fsync changes BS only: it lands the environment's selection and
;     drops the rest from pending, while the visible tables keep every
;     operation -- readable, not durable, not dirty;
;   an unlink, like a rename, resolves its name in the VISIBLE namespace
;     and leaves a pending :del-entry: the name is gone from the cache at
;     once and from the durable table only once its directory is fenced;
;   :evict-ino / :evict-dir drop clean cache: the visible inode or directory
;     becomes its durable value, allowed only with nothing pending for it;
;   :exit is a process death that keeps the cache (the restart's case);
;   :lose-cache is a power loss: BS becomes a crash image and the visible
;     tables become the image's.
;
; THE PROGRAM (fn-lgrc-program, hosted by host/native/io.lisp
; fnn-log-recover).  The open reads the active segment K through journal/'s
; VISIBLE binding, validates it (the kernel fn-lgt-recover of the read O,
; frontier F), and publishes the validated prefix into a fresh inode: create
; it in staging/, write (take F O) ++ zeros to O's length, fence the file,
; rename it over journal/K, fence journal/, fence staging/.  The inode the
; old name bound is never written.
;
; THE INVARIANT (fn-lgrc-invp, over an acknowledged prefix A: octets that
; scan completely to the acknowledged records).  Every inode a crash could
; leave bound to journal/K -- the durable binding and the target of every
; pending :set-entry for it (fn-bs-entry-outcomes, no :del-entry pending,
; since NIL is no good inode) -- and the visible binding hold A at offset 0
; durably and visibly, and every pending write to them starts at or above
; (len A).  Kept by every step of every recovery attempt under any outcomes,
; by evictions, exits and cache loss, and by any write above (len A).
;
; KEYSTONES:
;   fn-lgrc-every-image-binds-the-acknowledged-prefix   (discoverable) from
;       the invariant, in every crash image the inode journal/K durably
;       names holds A first, and its scan reads the acknowledged records
;       first;
;   fn-lgrc-attempt-keeps-the-invariant   every cut of an attempt, any
;       outcomes;
;   fn-lgrc-world-keeps-the-invariant     any sequence of attempts, cache
;       evictions, exits and cache losses (K2: through failed directory
;       barriers and repeated recoveries);
;   fn-lgrc-attempt-makes-the-read-prefix-durable   (K1) an attempt that
;       completes from a quiet store leaves journal/K durably bound to an
;       inode R-related to the read's kernel.
;   fn-lgrc-open-unlinks-no-segment   (section 10) every journal/ name that
;       every crash image binds stays bound at every state of the open, any
;       outcomes: the open never drops (RL-01-CHECKPOINT-NAME-BEFORE-DROP).
; Assumptions: none new.  A-CRASH-IMAGE's tear model and A-DURABILITY are
; the byte model's; A-WRITE-ISOLATION's cross-inode reading
; (specs/failures.md) is what lets the old inode's blocks survive its unlink.
(in-package "ACL2")
(include-book "store-log-durable")
(include-book "store-log-damage")
(include-book "store-log-route-programs")

; -----------------------------------------------------------------------------
; 1. The cache model.

(defun fn-bsc-make (bs vinodes vdirs)
  (declare (xargs :guard t))
  (list :bsc bs vinodes vdirs))
(defun fn-bsc-bs (s) (declare (xargs :guard t :verify-guards nil)) (if (consp s) (nth 1 s) nil))
(defun fn-bsc-vinodes (s) (declare (xargs :guard t :verify-guards nil)) (if (consp s) (nth 2 s) nil))
(defun fn-bsc-vdirs (s) (declare (xargs :guard t :verify-guards nil)) (if (consp s) (nth 3 s) nil))

(defthm fn-bsc-accessors-of-make
  (and (equal (fn-bsc-bs (fn-bsc-make bs vi vd)) bs)
       (equal (fn-bsc-vinodes (fn-bsc-make bs vi vd)) vi)
       (equal (fn-bsc-vdirs (fn-bsc-make bs vi vd)) vd)))

; A store whose cache is exactly its view: no failure is outstanding.
(defun fn-bsc-of (bs)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (vi vd) (fn-bs-apply-ops (fn-bs-inodes bs) (fn-bs-dirs bs) (fn-bs-pending bs))
    (fn-bsc-make bs vi vd)))

; What read(2) and lookup observe.
(defun fn-bsc-content (s ino)
  (declare (xargs :guard t :verify-guards nil))
  (cdr (assoc-equal ino (fn-bsc-vinodes s))))
(defun fn-bsc-lookup (s dir name)
  (declare (xargs :guard t :verify-guards nil))
  (cdr (assoc-equal name (cdr (assoc-equal dir (fn-bsc-vdirs s))))))

; The visible tables after one operation.
(defun fn-bsc-vapply (s op)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (vi vd) (fn-bs-apply-op (fn-bsc-vinodes s) (fn-bsc-vdirs s) op)
    (fn-bsc-make (fn-bsc-bs s) vi vd)))

; The steps.  Each answers (mv RESULT STATE); RESULT is :ok or an errno.
;   (:create DIR NAME OUTCOME)       a fresh inode, durable and empty, its
;                                    name pending and visible
;   (:write INO OFFSET OCTETS OUTCOME)
;   (:fsync-file INO OUTCOME)  (:fsync-dir DIR OUTCOME)
;   (:rename SDIR SNAME DDIR DNAME OUTCOME)   the source resolved in the
;                                    VISIBLE namespace
;   (:unlink DIR NAME OUTCOME)       the name resolved in the VISIBLE
;                                    namespace (fn-bs-unlink's outcomes)
;   (:evict-ino INO)  (:evict-dir DIR)  (:exit)  (:lose-cache CHOICES)
(defun fn-bsc-step (s op)
  (declare (xargs :guard t :verify-guards nil))
  (let ((bs (fn-bsc-bs s)) (kind (if (consp op) (car op) nil)))
    (case kind
      (:create
       (let ((dir (nth 1 op)) (name (nth 2 op)) (outcome (nth 3 op)))
         (cond ((fn-bsc-lookup s dir name) (mv :eexist s))
               ((not (equal outcome :ok)) (mv outcome s))
               (t (let ((ino (fn-bs-next-ino bs)))
                    (mv :ok
                        (fn-bsc-make
                         ;; the byte store as fn-bs-create leaves it
                         (fn-bs-make (fn-bs-unit bs)
                                     (cons (cons ino nil) (fn-bs-inodes bs))
                                     (fn-bs-dirs bs)
                                     (append (fn-bs-pending bs)
                                             (list (list :set-entry dir name ino)))
                                     (1+ ino))
                         (fn-bs-put-assoc ino nil (fn-bsc-vinodes s))
                         (mv-let (vi vd)
                           (fn-bs-apply-op nil (fn-bsc-vdirs s)
                                           (list :set-entry dir name ino))
                           (declare (ignore vi))
                           vd))))))))
      (:write
       (let ((ino (nth 1 op)) (off (nth 2 op)) (octets (nth 3 op)) (outcome (nth 4 op)))
         (mv-let (r bs1) (fn-bs-write bs ino off octets outcome)
           (if (equal r :ebadf)
               (mv r s)
             (let ((n (if (equal outcome :ok) (len octets) (nfix (cdr outcome)))))
               (mv r (fn-bsc-vapply (fn-bsc-make bs1 (fn-bsc-vinodes s) (fn-bsc-vdirs s))
                                    (list :write ino off (fn-bs-take n octets)))))))))
      (:fsync-file
       (mv-let (r bs1) (fn-bs-fsync-file bs (nth 1 op) (nth 2 op))
         (mv r (fn-bsc-make bs1 (fn-bsc-vinodes s) (fn-bsc-vdirs s)))))
      (:fsync-dir
       (mv-let (r bs1) (fn-bs-fsync-dir bs (nth 1 op) (nth 2 op))
         (mv r (fn-bsc-make bs1 (fn-bsc-vinodes s) (fn-bsc-vdirs s)))))
      (:rename
       (let* ((sdir (nth 1 op)) (sname (nth 2 op)) (ddir (nth 3 op)) (dname (nth 4 op))
              (outcome (nth 5 op)) (ino (fn-bsc-lookup s sdir sname)))
         (cond ((not (fn-bs-inop ino)) (mv :enoent s))
               ((not (or (equal outcome :ok)
                         (and (consp outcome) (equal (cdr outcome) :issued))))
                (mv (if (consp outcome) (car outcome) outcome) s))
               (t (let ((ops (list (list :set-entry ddir dname ino)
                                   (list :del-entry sdir sname))))
                    (mv (if (equal outcome :ok) :ok (car outcome))
                        (fn-bsc-vapply
                         (fn-bsc-vapply
                          (fn-bsc-make (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs)
                                                   (fn-bs-dirs bs)
                                                   (append (fn-bs-pending bs) ops)
                                                   (fn-bs-next-ino bs))
                                       (fn-bsc-vinodes s) (fn-bsc-vdirs s))
                          (car ops))
                         (cadr ops))))))))
      (:unlink
       (let* ((dir (nth 1 op)) (name (nth 2 op)) (outcome (nth 3 op))
              (del (list :del-entry dir name)))
         (cond ((not (fn-bsc-lookup s dir name)) (mv :enoent s))
               ((not (or (equal outcome :ok)
                         (and (consp outcome) (equal (cdr outcome) :issued))))
                (mv (if (consp outcome) (car outcome) outcome) s))
               (t (mv (if (equal outcome :ok) :ok (car outcome))
                      (fn-bsc-vapply
                       (fn-bsc-make (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs)
                                                (append (fn-bs-pending bs) (list del))
                                                (fn-bs-next-ino bs))
                                    (fn-bsc-vinodes s) (fn-bsc-vdirs s))
                       del))))))
      (:evict-ino
       (let ((ino (nth 1 op)))
         (if (fn-bs-ops-for-ino (fn-bs-pending bs) ino)
             (mv :busy s)
           (mv :ok (fn-bsc-make bs
                                (fn-bs-put-assoc ino (fn-bs-durable-content bs ino)
                                                 (fn-bsc-vinodes s))
                                (fn-bsc-vdirs s))))))
      (:evict-dir
       (let ((dir (nth 1 op)))
         (if (fn-bs-ops-for-dir (fn-bs-pending bs) dir)
             (mv :busy s)
           (mv :ok (fn-bsc-make bs (fn-bsc-vinodes s)
                                (fn-bs-put-assoc dir (cdr (assoc-equal dir (fn-bs-dirs bs)))
                                                 (fn-bsc-vdirs s)))))))
      (:lose-cache
       (let ((image (fn-bs-crash bs (nth 1 op))))
         (mv :ok (fn-bsc-make image (fn-bs-inodes image) (fn-bs-dirs image)))))
      (otherwise (mv :ok s)))))

; -----------------------------------------------------------------------------
; 2. The invariant over an acknowledged prefix A, and what it gives a crash.

; Octets C hold A at offset 0.
(defun fn-lgrc-holdsp (c a)
  (declare (xargs :guard t :verify-guards nil))
  (and (<= (len a) (len c))
       (equal (fn-bs-take (len a) c) a)))

; Inode I holds A at offset 0 durably and visibly, and every pending write to
; it starts at or above (len A).  I is below the next inode number, so no
; create returns it.
(defun fn-lgrc-goodp (s i a)
  (declare (xargs :guard t :verify-guards nil))
  (let ((bs (fn-bsc-bs s)))
    (and (fn-bs-inop i)
         (< i (nfix (fn-bs-next-ino bs)))
         (fn-lgrc-holdsp (fn-bs-durable-content bs i) a)
         (fn-lgrc-holdsp (fn-bsc-content s i) a)
         (fn-lgu-writes-at-or-above (fn-bs-pending bs) i (len a)))))

(defun fn-lgrc-all-goodp (s is a)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp is)
      (and (fn-lgrc-goodp s (car is) a) (fn-lgrc-all-goodp s (cdr is) a))
    t))

(defthm fn-lgrc-all-goodp-member
  (implies (and (fn-lgrc-all-goodp s is a) (member-equal i is))
           (fn-lgrc-goodp s i a))
  :hints (("Goal" :in-theory (disable fn-lgrc-goodp))))

(defthm fn-lgrc-all-goodp-of-append
  (equal (fn-lgrc-all-goodp s (append x y) a)
         (and (fn-lgrc-all-goodp s x a) (fn-lgrc-all-goodp s y a)))
  :hints (("Goal" :in-theory (disable fn-lgrc-goodp))))

; Every inode a crash can leave journal/K (DIR J, NAME K) durably bound to:
; the durable binding, or the target of a pending :set-entry for it, in any
; order the pending entries land (books/byte-store-invariants.lisp
; fn-bs-crash-entry-is-old-or-a-pending-target).  A pending :del-entry would
; make NIL an outcome, which no good inode is.
(defun fn-lgrc-candidates (bs j k)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-entry-outcomes (fn-bs-ops-for-name (fn-bs-pending bs) j k)
                        (fn-bs-durable-entry bs j k)))

(defun fn-lgrc-invp (s j k a)
  (declare (xargs :guard t :verify-guards nil))
  (let ((bs (fn-bsc-bs s)))
    (and (fn-bs-dir-idp j) (fn-bs-namep k)
         (fn-lgrc-all-goodp s (fn-lgrc-candidates bs j k) a)
         (fn-lgrc-goodp s (fn-bsc-lookup s j k) a))))

; KEYSTONE (discoverable).  From the invariant, in the image any crash
; leaves (any choices), the inode journal/K durably names holds A at offset
; 0.  The open's plan is a function of journal/'s names
; (books/store-log-segments.lisp fn-lgs-open-plan), which A2 never changes:
; K is where it was.
(defthm fn-lgrc-every-image-binds-the-acknowledged-prefix
  (implies (fn-lgrc-invp s j k a)
           (let* ((image (fn-bs-crash (fn-bsc-bs s) choices))
                  (i (fn-bs-durable-entry image j k))
                  (c (fn-bs-durable-content image i)))
             (and (fn-bs-inop i)
                  (<= (len a) (len c))
                  (equal (fn-bs-take (len a) c) a))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d () (fn-bs-crash fn-bs-durable-entry fn-bs-durable-content
                               fn-bs-take fn-lgrc-all-goodp-member
                               fn-lgu-crash-with-choices-keeps-the-prefix
                               fn-bs-crash-with-choices-entry-is-old-or-a-pending-target))
           :use ((:instance fn-bs-crash-with-choices-entry-is-old-or-a-pending-target
                            (s (fn-bsc-bs s)) (dir j) (name k))
                 (:instance fn-lgrc-all-goodp-member
                            (is (fn-lgrc-candidates (fn-bsc-bs s) j k))
                            (i (fn-bs-durable-entry (fn-bs-crash (fn-bsc-bs s) choices) j k)))
                 (:instance fn-lgu-crash-with-choices-keeps-the-prefix
                            (s (fn-bsc-bs s)) (f (len a))
                            (ino (fn-bs-durable-entry (fn-bs-crash (fn-bsc-bs s) choices) j k)))))))

; -----------------------------------------------------------------------------
; 3. Every step keeps the invariant.
;
; Per step kind: what it does to an inode's durable and visible content and
; to its pending writes (fn-lgrc-goodp-after-step: only a write below (len A)
; to the inode breaks it), and what it does to journal/K's candidates and
; visible binding (fn-lgrc-names-after-*).  The candidates after a step are
; the old ones (writes, file fences, creates, evictions, an unlink of
; another name), one of the old
; ones (a fence of journal/, a cache loss), or the old ones with a rename's
; source (a rename onto journal/K); the visible binding is the old one, a
; candidate (evict-dir, lose-cache) or the rename's source.

(local
 (defthm fn-lgrc-take-of-append-short
   (implies (and (natp f) (<= f (len x)))
            (equal (fn-bs-take f (append x y)) (fn-bs-take f x)))
   :hints (("Goal" :in-theory (enable fn-bs-take)))))
(local
 (defthm fn-lgrc-take-of-take
   (implies (and (natp f) (natp n) (<= f n))
            (equal (fn-bs-take f (fn-bs-take n x)) (fn-bs-take f x)))
   :hints (("Goal" :in-theory (enable fn-bs-take)))))
(local
 (defthm fn-lgrc-len-of-take
   (equal (len (fn-bs-take n x)) (nfix n))
   :hints (("Goal" :in-theory (enable fn-bs-take)))))
(local
 (defthm fn-lgrc-holdsp-of-splice
   (implies (and (fn-lgrc-holdsp old a) (<= (len a) (nfix off)))
            (fn-lgrc-holdsp (fn-bs-splice old off oct) a))
   :hints (("Goal" :in-theory (e/d (fn-bs-splice) (fn-bs-take))
            :use ((:instance fn-lgrc-take-of-append-short (f (len a))
                             (x (fn-bs-take (nfix off) old))
                             (y (append oct (nthcdr (+ (nfix off) (len oct)) old))))
                  (:instance fn-lgrc-take-of-take (f (len a)) (n (nfix off)) (x old)))))))
(local
 (defthm fn-lgrc-holdsp-of-put-splice
   (implies (and (fn-bs-inop i) (fn-lgrc-holdsp (cdr (assoc-equal i inodes)) a)
                 (or (not (equal k i)) (<= (len a) (nfix off))))
            (fn-lgrc-holdsp (cdr (assoc-equal i (fn-bs-put-assoc k (fn-bs-splice (cdr (assoc-equal k inodes)) off oct) inodes))) a))
   :hints (("Goal" :cases ((equal k i))
            :in-theory (e/d (fn-bs-assoc-of-put-assoc-same fn-bs-assoc-of-put-assoc-other)
                            (fn-lgrc-holdsp fn-bs-splice fn-bs-put-assoc))))))
(local
 (defthm fn-lgrc-holdsp-of-apply-writes
   (implies (and (fn-bs-inop i) (fn-lgu-writes-at-or-above ops i (len a))
                 (fn-lgrc-holdsp (cdr (assoc-equal i inodes)) a))
            (fn-lgrc-holdsp (cdr (assoc-equal i (fn-bs-apply-writes inodes ops))) a))
   :hints (("Goal" :induct (fn-bs-apply-writes inodes ops)
            :in-theory (e/d () (fn-lgrc-holdsp fn-bs-splice fn-bs-put-assoc fn-bs-inop))))))
(local
 (defthm fn-lgrc-ops-not-for-dir-writes-at-or-above
   (implies (fn-lgu-writes-at-or-above ops ino f)
            (and (fn-lgu-writes-at-or-above (fn-bs-ops-not-for-dir ops d) ino f)
                 (fn-lgu-writes-at-or-above (fn-bs-ops-for-dir ops d) ino f)))))
(local
 (defthm fn-lgrc-writes-at-or-above-of-entry-op
   (implies (not (equal (car op) :write))
            (fn-lgu-writes-at-or-above (list op) ino f))))

(defthm fn-lgrc-goodp-after-write
  (implies (and (fn-lgrc-goodp s i a)
                (equal (car op) :write)
                (or (not (equal i (nth 1 op))) (<= (len a) (nfix (nth 2 op)))))
           (fn-lgrc-goodp (mv-nth 1 (fn-bsc-step s op)) i a))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-write fn-bsc-vapply fn-bsc-content fn-bs-durable-content
                            fn-bs-apply-op)
                           (fn-bs-take fn-bs-splice fn-lgrc-holdsp fn-bs-put-assoc)))))

(defthm fn-lgrc-goodp-after-fsync-file
  (implies (and (fn-lgrc-goodp s i a) (equal (car op) :fsync-file))
           (fn-lgrc-goodp (mv-nth 1 (fn-bsc-step s op)) i a))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-fsync-file fn-bs-fence-file fn-bsc-content fn-bs-durable-content
                            fn-bs-apply-ops-inodes-are-apply-writes)
                           (fn-bs-take fn-bs-splice fn-lgrc-holdsp fn-bs-put-assoc fn-bs-apply-ops
                            fn-bs-apply-writes fn-bs-crash-select fn-bs-ops-for-ino fn-bs-ops-not-for-ino)))))

(defthm fn-lgrc-goodp-after-fsync-dir
  (implies (and (fn-lgrc-goodp s i a) (equal (car op) :fsync-dir))
           (fn-lgrc-goodp (mv-nth 1 (fn-bsc-step s op)) i a))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-fsync-dir fn-bs-fence-dir fn-bsc-content fn-bs-durable-content
                            fn-bs-apply-ops-inodes-are-apply-writes)
                           (fn-bs-take fn-bs-splice fn-lgrc-holdsp fn-bs-put-assoc fn-bs-apply-ops
                            fn-bs-apply-writes fn-bs-crash-select fn-bs-ops-for-dir fn-bs-ops-not-for-dir)))))
(defthm fn-lgrc-goodp-after-create
  (implies (and (fn-lgrc-goodp s i a) (equal (car op) :create))
           (fn-lgrc-goodp (mv-nth 1 (fn-bsc-step s op)) i a))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bsc-content fn-bs-durable-content
                            fn-bs-assoc-of-put-assoc-other)
                           (fn-bs-take fn-lgrc-holdsp fn-bs-put-assoc fn-bs-apply-op)))))

(defthm fn-lgrc-goodp-after-rename
  (implies (and (fn-lgrc-goodp s i a) (equal (car op) :rename))
           (fn-lgrc-goodp (mv-nth 1 (fn-bsc-step s op)) i a))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bsc-content fn-bsc-vapply fn-bs-durable-content fn-bs-apply-op)
                           (fn-bs-take fn-lgrc-holdsp fn-bs-put-assoc fn-bs-del-assoc)))))

(defthm fn-lgrc-goodp-after-unlink
  (implies (and (fn-lgrc-goodp s i a) (equal (car op) :unlink))
           (fn-lgrc-goodp (mv-nth 1 (fn-bsc-step s op)) i a))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bsc-content fn-bsc-vapply fn-bs-durable-content fn-bs-apply-op)
                           (fn-bs-take fn-lgrc-holdsp fn-bs-put-assoc fn-bs-del-assoc)))))

(defthm fn-lgrc-goodp-after-evict-ino
  (implies (and (fn-lgrc-goodp s i a) (equal (car op) :evict-ino))
           (fn-lgrc-goodp (mv-nth 1 (fn-bsc-step s op)) i a))
  :hints (("Goal" :do-not-induct t
           :cases ((equal i (nth 1 op)))
           :in-theory (e/d (fn-bsc-content fn-bs-assoc-of-put-assoc-other fn-bs-assoc-of-put-assoc-same)
                           (fn-bs-take fn-lgrc-holdsp fn-bs-put-assoc fn-bs-durable-content)))))

(defthm fn-lgrc-goodp-after-evict-dir
  (implies (and (fn-lgrc-goodp s i a) (equal (car op) :evict-dir))
           (fn-lgrc-goodp (mv-nth 1 (fn-bsc-step s op)) i a))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bsc-content)
                           (fn-bs-take fn-lgrc-holdsp fn-bs-put-assoc fn-bs-durable-content)))))

(local
 (defthm fn-lgrc-inodes-entry-is-durable-content
   (equal (cdr (assoc-equal i (fn-bs-inodes x))) (fn-bs-durable-content x i))
   :hints (("Goal" :in-theory (enable fn-bs-durable-content)))))
(local
 (defthm fn-lgrc-crash-keeps-next-ino-and-unit
   (and (equal (fn-bs-next-ino (fn-bs-crash x choices)) (fn-bs-next-ino x))
        (equal (fn-bs-unit (fn-bs-crash x choices)) (fn-bs-unit x))
        (equal (fn-bs-pending (fn-bs-crash x choices)) nil))
   :hints (("Goal" :in-theory (enable fn-bs-crash)))))
(defthm fn-lgrc-goodp-after-lose-cache
  (implies (and (fn-lgrc-goodp s i a) (equal (car op) :lose-cache))
           (fn-lgrc-goodp (mv-nth 1 (fn-bsc-step s op)) i a))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bsc-content)
                           (fn-bs-take fn-bs-crash fn-bs-durable-content
                            fn-lgu-crash-with-choices-keeps-the-prefix))
           :use ((:instance fn-lgu-crash-with-choices-keeps-the-prefix
                            (s (fn-bsc-bs s)) (ino i) (f (len a)) (choices (nth 1 op)))))))
; --- the name algebra
(local
 (defthm fn-lgrc-ops-for-name-of-append
   (equal (fn-bs-ops-for-name (append x y) d n)
          (append (fn-bs-ops-for-name x d n) (fn-bs-ops-for-name y d n)))))
(local
 (defthm fn-lgrc-ops-for-name-of-ops-for-ino
   (equal (fn-bs-ops-for-name (fn-bs-ops-for-ino ops ino) d n) nil)))
(local
 (defthm fn-lgrc-ops-for-name-of-ops-not-for-ino
   (equal (fn-bs-ops-for-name (fn-bs-ops-not-for-ino ops ino) d n)
          (fn-bs-ops-for-name ops d n))))
(local
 (defthm fn-lgrc-ops-for-name-of-ops-for-dir
   (equal (fn-bs-ops-for-name (fn-bs-ops-for-dir ops dir) d n)
          (if (equal dir d) (fn-bs-ops-for-name ops d n) nil))))
(local
 (defthm fn-lgrc-ops-for-name-of-ops-not-for-dir
   (equal (fn-bs-ops-for-name (fn-bs-ops-not-for-dir ops dir) d n)
          (if (equal dir d) nil (fn-bs-ops-for-name ops d n)))))
(local
 (defthm fn-lgrc-ops-for-name-when-dir-quiet
   (implies (not (fn-bs-ops-for-dir ops d))
            (equal (fn-bs-ops-for-name ops d n) nil))))
(local
 (defthm fn-lgrc-entry-outcomes-of-nil
   (equal (fn-bs-entry-outcomes nil old) (list old))))
(local
 (defthm fn-lgrc-entry-after-is-an-outcome
   (member-equal (fn-bs-entry-after ops old d n)
                 (fn-bs-entry-outcomes (fn-bs-ops-for-name ops d n) old))
   :hints (("Goal" :induct (fn-bs-entry-after ops old d n)
            :in-theory (enable fn-bs-entry-after fn-bs-member-of-append)))))
(local
 (defthm fn-lgrc-all-goodp-of-outcomes-of-append-set
   (implies (and (fn-lgrc-all-goodp s (fn-bs-entry-outcomes ops old) a) (fn-lgrc-goodp s v a))
            (fn-lgrc-all-goodp s (fn-bs-entry-outcomes (append ops (list (list :set-entry d n v))) old) a))
   :hints (("Goal" :induct (fn-bs-entry-outcomes ops old)
            :in-theory (disable fn-lgrc-goodp)))))
(defthm fn-bsc-step-of-another-kind
  (implies (not (member-equal (car op) '(:create :write :fsync-file :fsync-dir :rename
                                         :unlink :evict-ino :evict-dir :lose-cache)))
           (equal (mv-nth 1 (fn-bsc-step s op)) s)))

; A step keeps inode I good unless it writes I below (len A).
(defthm fn-lgrc-goodp-after-step
  (implies (and (fn-lgrc-goodp s i a)
                (or (not (equal (car op) :write)) (not (equal i (nth 1 op)))
                    (<= (len a) (nfix (nth 2 op)))))
           (fn-lgrc-goodp (mv-nth 1 (fn-bsc-step s op)) i a))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d () (fn-lgrc-goodp fn-bsc-step))
           :cases ((equal (car op) :write) (equal (car op) :fsync-file) (equal (car op) :fsync-dir)
                   (equal (car op) :create) (equal (car op) :rename) (equal (car op) :unlink)
                   (equal (car op) :evict-ino) (equal (car op) :evict-dir)
                   (equal (car op) :lose-cache)))
))

(defthm fn-lgrc-all-goodp-after-step
  (implies (and (fn-lgrc-all-goodp s is a)
                (or (not (equal (car op) :write)) (not (member-equal (nth 1 op) is))
                    (<= (len a) (nfix (nth 2 op)))))
           (fn-lgrc-all-goodp (mv-nth 1 (fn-bsc-step s op)) is a))
  :hints (("Goal" :induct (fn-lgrc-all-goodp s is a)
           :in-theory (disable fn-lgrc-goodp fn-bsc-step))))
(local
 (defthm fn-lgrc-ops-for-name-of-write
   (equal (fn-bs-ops-for-name (list (list :write i o x)) d n) nil)))
(local
 (defthm fn-lgrc-durable-entry-of-make
   (equal (fn-bs-durable-entry (fn-bs-make u in dirs p nx) d n)
          (cdr (assoc-equal n (cdr (assoc-equal d dirs)))))
   :hints (("Goal" :in-theory (enable fn-bs-durable-entry)))))

(defthm fn-lgrc-names-after-write
  (implies (equal (car op) :write)
           (and (equal (fn-lgrc-candidates (fn-bsc-bs (mv-nth 1 (fn-bsc-step s op))) j k)
                       (fn-lgrc-candidates (fn-bsc-bs s) j k))
                (equal (fn-bsc-lookup (mv-nth 1 (fn-bsc-step s op)) j k)
                       (fn-bsc-lookup s j k))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-write fn-bsc-vapply fn-bs-apply-op fn-bs-durable-entry)
                           (fn-bs-take fn-bs-splice fn-bs-put-assoc fn-bs-entry-outcomes
                            fn-bs-ops-for-name)))))

(defthm fn-lgrc-names-after-fsync-file
  (implies (and (equal (car op) :fsync-file) (fn-bs-dir-idp j) (fn-bs-namep k))
           (and (equal (fn-lgrc-candidates (fn-bsc-bs (mv-nth 1 (fn-bsc-step s op))) j k)
                       (fn-lgrc-candidates (fn-bsc-bs s) j k))
                (equal (fn-bsc-lookup (mv-nth 1 (fn-bsc-step s op)) j k)
                       (fn-bsc-lookup s j k))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-fsync-file fn-bs-fence-file fn-bs-durable-entry
                            fn-bs-apply-ops-dirs-are-apply-entries fn-bs-apply-entries-of-ops-for-ino)
                           (fn-bs-entry-outcomes fn-bs-ops-for-name fn-bs-crash-select
                            fn-bs-ops-for-ino fn-bs-ops-not-for-ino fn-bs-apply-entries
                            fn-bs-apply-ops))
           :use ((:instance fn-bs-crash-select-entry-is-an-outcome
                            (ops (fn-bs-ops-for-ino (fn-bs-pending (fn-bsc-bs s)) (nth 1 op)))
                            (choices (cdr (nth 2 op))) (unit (fn-bs-unit (fn-bsc-bs s)))
                            (old (fn-bs-durable-entry (fn-bsc-bs s) j k)) (dir j) (name k))
                 (:instance fn-bs-apply-entries-entry-is-entry-after
                            (dirs (fn-bs-dirs (fn-bsc-bs s))) (dir j) (name k)
                            (ops (fn-bs-crash-select (fn-bs-ops-for-ino (fn-bs-pending (fn-bsc-bs s)) (nth 1 op))
                                                     (cdr (nth 2 op)) (fn-bs-unit (fn-bsc-bs s)))))))))
(local
 (defthm fn-lgrc-old-is-an-outcome
   (member-equal old (fn-bs-entry-outcomes ops old))
   :hints (("Goal" :induct (fn-bs-entry-outcomes ops old)
            :in-theory (enable fn-bs-member-of-append)))))
(defthm fn-lgrc-names-after-fsync-dir
  (implies (and (equal (car op) :fsync-dir) (fn-bs-dir-idp j) (fn-bs-namep k))
           (let ((s1 (mv-nth 1 (fn-bsc-step s op))))
             (and (equal (fn-bsc-lookup s1 j k) (fn-bsc-lookup s j k))
                  (member-equal (fn-bs-durable-entry (fn-bsc-bs s1) j k)
                                (fn-lgrc-candidates (fn-bsc-bs s) j k))
                  (equal (fn-lgrc-candidates (fn-bsc-bs s1) j k)
                         (if (equal (nth 1 op) j)
                             (list (fn-bs-durable-entry (fn-bsc-bs s1) j k))
                           (fn-lgrc-candidates (fn-bsc-bs s) j k))))))
  :hints (("Goal" :do-not-induct t
           :cases ((equal (nth 1 op) j))
           :in-theory (e/d (fn-bs-fsync-dir fn-bs-fence-dir fn-bs-durable-entry
                            fn-bs-apply-ops-dirs-are-apply-entries)
                           (fn-bs-entry-outcomes fn-bs-ops-for-name fn-bs-crash-select
                            fn-bs-ops-for-dir fn-bs-ops-not-for-dir fn-bs-apply-entries
                            fn-bs-apply-ops fn-lgrc-entry-after-is-an-outcome
                            fn-bs-crash-select-entry-is-an-outcome))
           :use ((:instance fn-bs-crash-select-entry-is-an-outcome
                            (ops (fn-bs-ops-for-dir (fn-bs-pending (fn-bsc-bs s)) (nth 1 op)))
                            (choices (cdr (nth 2 op))) (unit (fn-bs-unit (fn-bsc-bs s)))
                            (old (fn-bs-durable-entry (fn-bsc-bs s) j k)) (dir j) (name k))
                 (:instance fn-lgrc-entry-after-is-an-outcome
                            (ops (fn-bs-ops-for-dir (fn-bs-pending (fn-bsc-bs s)) (nth 1 op)))
                            (old (fn-bs-durable-entry (fn-bsc-bs s) j k)) (d j) (n k))
                 (:instance fn-bs-apply-entries-entry-is-entry-after
                            (dirs (fn-bs-dirs (fn-bsc-bs s))) (dir j) (name k)
                            (ops (fn-bs-crash-select (fn-bs-ops-for-dir (fn-bs-pending (fn-bsc-bs s)) (nth 1 op))
                                                     (cdr (nth 2 op)) (fn-bs-unit (fn-bsc-bs s)))))
                 (:instance fn-bs-apply-entries-entry-is-entry-after
                            (dirs (fn-bs-dirs (fn-bsc-bs s))) (dir j) (name k)
                            (ops (fn-bs-ops-for-dir (fn-bs-pending (fn-bsc-bs s)) (nth 1 op))))))))
(local
 (defthm fn-lgrc-entry-of-set
   (implies (and j k)
            (equal (cdr (assoc-equal k (cdr (assoc-equal j (fn-bs-put-assoc d (fn-bs-put-assoc n v (cdr (assoc-equal d dirs))) dirs)))))
                   (if (and (equal d j) (equal n k)) v (cdr (assoc-equal k (cdr (assoc-equal j dirs)))))))
   :hints (("Goal" :cases ((equal d j) (equal n k))
            :in-theory (enable fn-bs-assoc-of-put-assoc-other fn-bs-assoc-of-put-assoc-same)))))
(local
 (defthm fn-lgrc-entry-of-del
   (implies (and j k)
            (equal (cdr (assoc-equal k (cdr (assoc-equal j (fn-bs-put-assoc d (fn-bs-del-assoc n (cdr (assoc-equal d dirs))) dirs)))))
                   (if (and (equal d j) (equal n k)) nil (cdr (assoc-equal k (cdr (assoc-equal j dirs)))))))
   :hints (("Goal" :cases ((equal d j) (equal n k))
            :in-theory (enable fn-bs-assoc-of-put-assoc-other fn-bs-assoc-of-put-assoc-same
                               fn-bs-assoc-of-del-assoc-other fn-bs-assoc-of-del-assoc-same)))))
(local
 (defthm fn-lgrc-dir-idp-is-not-nil
   (implies (fn-bs-dir-idp j) (and j (keywordp j)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-bs-dir-idp)))))
(defthm fn-lgrc-names-after-create
  (implies (and (equal (car op) :create) (fn-bs-dir-idp j) (fn-bs-namep k)
                (fn-bsc-lookup s j k))
           (and (equal (fn-lgrc-candidates (fn-bsc-bs (mv-nth 1 (fn-bsc-step s op))) j k)
                       (fn-lgrc-candidates (fn-bsc-bs s) j k))
                (equal (fn-bsc-lookup (mv-nth 1 (fn-bsc-step s op)) j k)
                       (fn-bsc-lookup s j k))))
  :hints (("Goal" :do-not-induct t
           :cases ((and (equal (nth 1 op) j) (equal (nth 2 op) k)))
           :in-theory (e/d (fn-bs-apply-op fn-bs-durable-entry fn-bs-assoc-of-put-assoc-other
                            fn-bs-assoc-of-put-assoc-same)
                           (fn-bs-entry-outcomes fn-bs-put-assoc)))))

(defthm fn-lgrc-names-after-rename
  (implies (and (equal (car op) :rename) (fn-bs-dir-idp j) (fn-bs-namep k)
                (not (and (equal (nth 1 op) j) (equal (nth 2 op) k))))
           (let* ((s1 (mv-nth 1 (fn-bsc-step s op)))
                  (bs (fn-bsc-bs s))
                  (src (fn-bsc-lookup s (nth 1 op) (nth 2 op))))
             (and (or (equal (fn-lgrc-candidates (fn-bsc-bs s1) j k)
                             (fn-lgrc-candidates bs j k))
                      (and (equal (nth 3 op) j) (equal (nth 4 op) k)
                           (equal (fn-lgrc-candidates (fn-bsc-bs s1) j k)
                                  (fn-bs-entry-outcomes
                                   (append (fn-bs-ops-for-name (fn-bs-pending bs) j k)
                                           (list (list :set-entry j k src)))
                                   (fn-bs-durable-entry bs j k)))))
                  (or (equal (fn-bsc-lookup s1 j k) (fn-bsc-lookup s j k))
                      (and (equal (nth 3 op) j) (equal (nth 4 op) k)
                           (equal (fn-bsc-lookup s1 j k) src))))))
  :hints (("Goal" :do-not-induct t
           :cases ((and (equal (nth 3 op) j) (equal (nth 4 op) k)))
           :in-theory (e/d (fn-bsc-vapply fn-bs-apply-op fn-bs-durable-entry
                            fn-bs-assoc-of-put-assoc-other fn-bs-assoc-of-put-assoc-same
                            fn-bs-assoc-of-del-assoc-other)
                           (fn-bs-entry-outcomes fn-bs-put-assoc fn-bs-del-assoc)))))

; An unlink of another name leaves journal/K's candidates and visible
; binding as they were.
(defthm fn-lgrc-names-after-unlink
  (implies (and (equal (car op) :unlink) (fn-bs-dir-idp j) (fn-bs-namep k)
                (not (and (equal (nth 1 op) j) (equal (nth 2 op) k))))
           (and (equal (fn-lgrc-candidates (fn-bsc-bs (mv-nth 1 (fn-bsc-step s op))) j k)
                       (fn-lgrc-candidates (fn-bsc-bs s) j k))
                (equal (fn-bsc-lookup (mv-nth 1 (fn-bsc-step s op)) j k)
                       (fn-bsc-lookup s j k))))
  :hints (("Goal" :do-not-induct t
           :cases ((equal (nth 1 op) j))
           :in-theory (e/d (fn-bsc-vapply fn-bs-apply-op fn-bs-durable-entry
                            fn-bs-assoc-of-put-assoc-other fn-bs-assoc-of-put-assoc-same
                            fn-bs-assoc-of-del-assoc-other)
                           (fn-bs-entry-outcomes fn-bs-put-assoc fn-bs-del-assoc)))))

(defthm fn-lgrc-names-after-evict
  (implies (and (or (equal (car op) :evict-ino) (equal (car op) :evict-dir))
                (fn-bs-dir-idp j) (fn-bs-namep k))
           (and (equal (fn-lgrc-candidates (fn-bsc-bs (mv-nth 1 (fn-bsc-step s op))) j k)
                       (fn-lgrc-candidates (fn-bsc-bs s) j k))
                (or (equal (fn-bsc-lookup (mv-nth 1 (fn-bsc-step s op)) j k)
                           (fn-bsc-lookup s j k))
                    (member-equal (fn-bsc-lookup (mv-nth 1 (fn-bsc-step s op)) j k)
                                  (fn-lgrc-candidates (fn-bsc-bs s) j k)))))
  :hints (("Goal" :do-not-induct t
           :cases ((equal (nth 1 op) j))
           :in-theory (e/d (fn-bs-durable-entry fn-bs-assoc-of-put-assoc-other
                            fn-bs-assoc-of-put-assoc-same)
                           (fn-bs-entry-outcomes fn-bs-put-assoc fn-bs-ops-for-name fn-bs-ops-for-dir)))))

(defthm fn-lgrc-names-after-lose-cache
  (implies (and (equal (car op) :lose-cache) (fn-bs-dir-idp j) (fn-bs-namep k))
           (let* ((s1 (mv-nth 1 (fn-bsc-step s op)))
                  (d (fn-bs-durable-entry (fn-bsc-bs s1) j k)))
             (and (equal (fn-lgrc-candidates (fn-bsc-bs s1) j k) (list d))
                  (equal (fn-bsc-lookup s1 j k) d)
                  (member-equal d (fn-lgrc-candidates (fn-bsc-bs s) j k)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-durable-entry)
                           (fn-bs-entry-outcomes fn-bs-crash fn-bs-ops-for-name
                            fn-bs-crash-with-choices-entry-is-old-or-a-pending-target))
           :use ((:instance fn-bs-crash-with-choices-entry-is-old-or-a-pending-target
                            (s (fn-bsc-bs s)) (choices (nth 1 op)) (dir j) (name k))))))
(defun fn-lgrc-op-okp (s op j k a)
  (declare (xargs :guard t :verify-guards nil))
  (let ((kind (if (consp op) (car op) nil)))
    (cond ((equal kind :write)
           (or (<= (len a) (nfix (nth 2 op)))
               (and (not (member-equal (nth 1 op) (fn-lgrc-candidates (fn-bsc-bs s) j k)))
                    (not (equal (nth 1 op) (fn-bsc-lookup s j k))))))
          ((equal kind :rename)
           (and (not (and (equal (nth 1 op) j) (equal (nth 2 op) k)))
                (or (not (and (equal (nth 3 op) j) (equal (nth 4 op) k)))
                    (fn-lgrc-goodp s (fn-bsc-lookup s (nth 1 op) (nth 2 op)) a))))
          ((equal kind :unlink)
           (not (and (equal (nth 1 op) j) (equal (nth 2 op) k))))
          (t t))))

(local
 (defthm fn-lgrc-goodp-is-an-inode
   (implies (fn-lgrc-goodp s i a) (natp i))
   :rule-classes :forward-chaining))

(defthm fn-lgrc-names-after-evict-ino
  (implies (equal (car op) :evict-ino)
           (and (equal (fn-bsc-bs (mv-nth 1 (fn-bsc-step s op))) (fn-bsc-bs s))
                (equal (fn-bsc-lookup (mv-nth 1 (fn-bsc-step s op)) j k)
                       (fn-bsc-lookup s j k))))
  :hints (("Goal" :in-theory (enable fn-bsc-step fn-bsc-bs fn-bsc-lookup))))

(local (in-theory (disable fn-lgrc-goodp fn-bsc-step fn-lgrc-candidates fn-bsc-lookup fn-bsc-bs)))

(local
 (defthm fn-lgrc-invp-after-unnaming-step
   (implies (and (fn-lgrc-invp s j k a)
                 (member-equal (car op) '(:write :fsync-file :create :evict-ino))
                 (fn-lgrc-op-okp s op j k a))
            (fn-lgrc-invp (mv-nth 1 (fn-bsc-step s op)) j k a))
   :hints (("Goal" :do-not-induct t))))
(local
 (defthm fn-lgrc-invp-after-fsync-dir
   (implies (and (fn-lgrc-invp s j k a) (equal (car op) :fsync-dir))
            (fn-lgrc-invp (mv-nth 1 (fn-bsc-step s op)) j k a))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-lgrc-all-goodp-member
                             (is (fn-lgrc-candidates (fn-bsc-bs s) j k))
                             (i (fn-bs-durable-entry (fn-bsc-bs (mv-nth 1 (fn-bsc-step s op))) j k))))))))
(local
 (defthm fn-lgrc-invp-after-lose-cache
   (implies (and (fn-lgrc-invp s j k a) (equal (car op) :lose-cache))
            (fn-lgrc-invp (mv-nth 1 (fn-bsc-step s op)) j k a))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-lgrc-all-goodp-member
                             (is (fn-lgrc-candidates (fn-bsc-bs s) j k))
                             (i (fn-bs-durable-entry (fn-bsc-bs (mv-nth 1 (fn-bsc-step s op))) j k))))))))
(local
 (defthm fn-lgrc-invp-after-evict-dir
   (implies (and (fn-lgrc-invp s j k a) (equal (car op) :evict-dir))
            (fn-lgrc-invp (mv-nth 1 (fn-bsc-step s op)) j k a))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-lgrc-all-goodp-member
                             (is (fn-lgrc-candidates (fn-bsc-bs s) j k))
                             (i (fn-bsc-lookup (mv-nth 1 (fn-bsc-step s op)) j k)))
                  (:instance fn-lgrc-names-after-evict))))))
(local
 (defthm fn-lgrc-invp-after-rename
   (implies (and (fn-lgrc-invp s j k a) (equal (car op) :rename) (fn-lgrc-op-okp s op j k a))
            (fn-lgrc-invp (mv-nth 1 (fn-bsc-step s op)) j k a))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lgrc-candidates) (fn-bs-entry-outcomes fn-bs-ops-for-name
                                                  fn-lgrc-names-after-rename))
            :use ((:instance fn-lgrc-names-after-rename)
                  (:instance fn-lgrc-all-goodp-of-outcomes-of-append-set
                             (s (mv-nth 1 (fn-bsc-step s op)))
                             (ops (fn-bs-ops-for-name (fn-bs-pending (fn-bsc-bs s)) j k))
                             (old (fn-bs-durable-entry (fn-bsc-bs s) j k))
                             (v (fn-bsc-lookup s (nth 1 op) (nth 2 op))) (d j) (n k))
                  (:instance fn-lgrc-all-goodp-after-step
                             (is (fn-lgrc-candidates (fn-bsc-bs s) j k)))
                  (:instance fn-lgrc-goodp-after-step (i (fn-bsc-lookup s (nth 1 op) (nth 2 op))))
                  (:instance fn-lgrc-goodp-after-step (i (fn-bsc-lookup s j k))))))))
(local
 (defthm fn-lgrc-invp-after-unlink
   (implies (and (fn-lgrc-invp s j k a) (equal (car op) :unlink) (fn-lgrc-op-okp s op j k a))
            (fn-lgrc-invp (mv-nth 1 (fn-bsc-step s op)) j k a))
   :hints (("Goal" :do-not-induct t))))
; Every step keeps the invariant under its side condition.
(defthm fn-lgrc-step-keeps-the-invariant
  (implies (and (fn-lgrc-invp s j k a) (fn-lgrc-op-okp s op j k a))
           (fn-lgrc-invp (mv-nth 1 (fn-bsc-step s op)) j k a))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lgrc-invp fn-lgrc-op-okp)
           :cases ((member-equal (car op) '(:write :fsync-file :create :evict-ino))
                   (equal (car op) :fsync-dir) (equal (car op) :lose-cache)
                   (equal (car op) :evict-dir) (equal (car op) :rename)
                   (equal (car op) :unlink)))))

; -----------------------------------------------------------------------------
; 4. The attempt (P-LOG-RECOVER-COPY).

; A scans completely: its chained entries end exactly at its end.
(defun fn-lgrc-completep (a genesis unit max)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp a)
       (equal (cdr (fn-lg-scan a genesis unit max)) (len a))))

(local
 (defthm fn-lgrc-take-then-nthcdr
   (implies (and (natp n) (<= n (len x)))
            (equal (append (fn-bs-take n x) (nthcdr n x)) x))
   :hints (("Goal" :in-theory (enable fn-bs-take)))))

(defthm fn-lgrc-frontier-of-recover
  (equal (fn-lgk-frontier (fn-lgt-recover o genesis unit max floor))
         (nfix (cdr (fn-lg-scan o genesis unit max))))
  :hints (("Goal" :in-theory (e/d (fn-lgt-recover fn-lgk-recover) (fn-lg-scan fn-lg-scan-last)))))

; The open's frontier is at or above a complete prefix of what it reads, and
; the records it reads begin with the prefix's.
(defthm fn-lgrc-scan-of-a-read-holding-a-complete-prefix
  (implies (and (fn-lgrc-completep a genesis unit max) (fn-lgrc-holdsp o a))
           (let ((scan (fn-lg-scan o genesis unit max)))
             (and (<= (len a) (cdr scan))
                  (equal (take (len (car (fn-lg-scan a genesis unit max))) (car scan))
                         (car (fn-lg-scan a genesis unit max))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d () (fn-lg-scan fn-lg-scan-last fn-bs-take fn-lg-scan-of-complete-append
                               fn-lgrc-take-then-nthcdr))
           :use ((:instance fn-lgrc-take-then-nthcdr (n (len a)) (x o))
                 (:instance fn-lg-scan-of-complete-append (d a) (x (nthcdr (len a) o))
                            (prev genesis))))))

; Run steps to the first error, as the host does: the state after each step.
(defun fn-bsc-run (s ops)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (mv-let (r s1) (fn-bsc-step s (car ops))
        (cons s1 (if (equal r :ok) (fn-bsc-run s1 (cdr ops)) nil)))
    nil))

(defun fn-lgrc-out (outs i)
  (declare (xargs :guard t :verify-guards nil))
  (let ((x (nth i (if (true-listp outs) outs nil)))) (if x x :ok)))

; The octets the copy writes: the read's validated prefix [0, F), then zeros
; to the read's length.
(defun fn-lgrc-copy-octets (o f)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-bs-take f o) (fn-bs-zeros (- (len o) (nfix f)))))

; One attempt from S: read journal/K through the VISIBLE namespace (a name
; an earlier attempt published but never fenced is read like any other: it
; is not trusted, it is copied again), validate, create STG/STAGE, write the
; copy, fence it, rename it over journal/K, fence journal/, fence STG/.
; OUTS: the environment's outcome of each of the six syscalls.
(defun fn-lgrc-attempt-ops (s j k stg stage genesis max floor outs)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((bs (fn-bsc-bs s))
         (o (fn-bsc-content s (fn-bsc-lookup s j k)))
         (f (fn-lgk-frontier (fn-lgt-recover o genesis (fn-bs-unit bs) max floor)))
         (ino (fn-bs-next-ino bs)))
    (list (list :create stg stage (fn-lgrc-out outs 0))
          (list :write ino 0 (fn-lgrc-copy-octets o f) (fn-lgrc-out outs 1))
          (list :fsync-file ino (fn-lgrc-out outs 2))
          (list :rename stg stage j k (fn-lgrc-out outs 3))
          (list :fsync-dir j (fn-lgrc-out outs 4))
          (list :fsync-dir stg (fn-lgrc-out outs 5)))))

(defun fn-lgrc-attempt (s j k stg stage genesis max floor outs)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bsc-run s (fn-lgrc-attempt-ops s j k stg stage genesis max floor outs)))

; The program as the host runs it (host/native/io.lisp fnn-log-recover),
; in the step language tests/campaign/native_cuts.py reads (LOG_PROGRAM_HOSTS,
; verify_log_program_steps): the staged file's create, the copy's write
; (fnn-log-copy-entry once per validated entry, from the walk's buffer; the
; zeros past F are the staged file's preallocation, A-HOST), its fence, the
; rename over journal/K, then journal/'s and staging/'s fences, each followed
; by its cut.  fn-lgrc-attempt-ops is this program over a store.
(defun fn-lgrc-program ()
  (declare (xargs :guard t))
  (list (list :create :staging :stage-recover)
        (list :write :staged 0 :validated-prefix)
        (list :cut "log-copied")
        (list :fsync-file :staged)
        (list :cut "log-copy-fenced")
        (list :rename :staging :stage-recover :journal :segment)
        (list :cut "log-swapped")
        (list :fsync-dir :journal)
        (list :fsync-dir :staging)
        (list :cut "log-recovered")))

(defun fn-lgrc-all-invp (states j k a)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp states)
      (and (fn-lgrc-invp (car states) j k a) (fn-lgrc-all-invp (cdr states) j k a))
    t))

; Each step's side condition, at the state it runs in.
(defun fn-lgrc-run-okp (s ops j k a)
  (declare (xargs :guard t :verify-guards nil :measure (len ops)))
  (if (consp ops)
      (and (fn-lgrc-op-okp s (car ops) j k a)
           (mv-let (r s1) (fn-bsc-step s (car ops))
             (if (equal r :ok) (fn-lgrc-run-okp s1 (cdr ops) j k a) t)))
    t))

(defthm fn-lgrc-run-keeps-the-invariant
  (implies (and (fn-lgrc-invp s j k a) (fn-lgrc-run-okp s ops j k a))
           (fn-lgrc-all-invp (fn-bsc-run s ops) j k a))
  :hints (("Goal" :induct (fn-bsc-run s ops)
           :in-theory (disable fn-lgrc-invp fn-lgrc-op-okp))))
(local
 (defthm fn-lgrc-goodp-is-below-next-ino
   (implies (fn-lgrc-goodp s i a)
            (not (equal i (fn-bs-next-ino (fn-bsc-bs s)))))
   :hints (("Goal" :in-theory (enable fn-lgrc-goodp)))))
(local
 (defthm fn-lgrc-all-goodp-excludes-next-ino
   (implies (fn-lgrc-all-goodp s is a)
            (not (member-equal (fn-bs-next-ino (fn-bsc-bs s)) is)))
   :hints (("Goal" :induct (fn-lgrc-all-goodp s is a)))))
(local
 (defthm fn-lgrc-holdsp-of-splice-at-0
   (implies (fn-lgrc-holdsp x a)
            (fn-lgrc-holdsp (fn-bs-splice old 0 x) a))
   :hints (("Goal" :expand ((fn-bs-take 0 old))
            :in-theory (e/d (fn-bs-splice fn-lgrc-holdsp) (fn-bs-take))))))

(local
 (defthm fn-lgrc-take-of-len
   (implies (true-listp x) (equal (fn-bs-take (len x) x) x))
   :hints (("Goal" :in-theory (enable fn-bs-take)))))

(local
 (defthm fn-lgrc-after-create-ok
   (let ((ino (fn-bs-next-ino (fn-bsc-bs s)))
         (s1 (mv-nth 1 (fn-bsc-step s (list :create stg stage :ok)))))
     (implies (and (not (fn-bsc-lookup s stg stage)) (fn-bs-dir-idp stg) (fn-bs-namep stage) (natp ino))
              (and (equal (car (fn-bsc-step s (list :create stg stage :ok))) :ok)
                   (equal (fn-bsc-lookup s1 stg stage) ino)
                   (equal (fn-bsc-content s1 ino) nil)
                   (equal (assoc-equal ino (fn-bs-inodes (fn-bsc-bs s1))) (cons ino nil))
                   (equal (fn-bs-next-ino (fn-bsc-bs s1)) (+ 1 ino))
                   (equal (fn-bs-pending (fn-bsc-bs s1))
                          (append (fn-bs-pending (fn-bsc-bs s)) (list (list :set-entry stg stage ino)))))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bsc-step fn-bsc-bs fn-bsc-lookup fn-bsc-content fn-bs-apply-op
                             fn-bs-assoc-of-put-assoc-same)
                            (fn-bs-put-assoc))))))

(local
 (defthm fn-lgrc-after-write-ok
   (let ((s2 (mv-nth 1 (fn-bsc-step s (list :write ino 0 x :ok)))))
     (implies (and (assoc-equal ino (fn-bs-inodes (fn-bsc-bs s))) (true-listp x) (consp x) ino)
              (and (equal (car (fn-bsc-step s (list :write ino 0 x :ok))) :ok)
                   (equal (fn-bsc-content s2 ino) (fn-bs-splice (fn-bsc-content s ino) 0 x))
                   (equal (fn-bs-inodes (fn-bsc-bs s2)) (fn-bs-inodes (fn-bsc-bs s)))
                   (equal (fn-bs-next-ino (fn-bsc-bs s2)) (fn-bs-next-ino (fn-bsc-bs s)))
                   (equal (fn-bs-pending (fn-bsc-bs s2))
                          (append (fn-bs-pending (fn-bsc-bs s)) (list (list :write ino 0 x)))))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bsc-step fn-bsc-bs fn-bsc-content fn-bs-write fn-bsc-vapply
                             fn-bs-apply-op fn-bs-assoc-of-put-assoc-same)
                            (fn-bs-put-assoc fn-bs-splice fn-bs-take))))))

(local
 (defthm fn-lgrc-after-fsync-file-ok
   (let ((s3 (mv-nth 1 (fn-bsc-step s (list :fsync-file ino :ok)))))
     (and (equal (car (fn-bsc-step s (list :fsync-file ino :ok))) :ok)
          (equal (fn-bsc-content s3 i) (fn-bsc-content s i))
          (equal (fn-bs-durable-content (fn-bsc-bs s3) ino)
                 (cdr (assoc-equal ino (fn-bs-apply-writes (fn-bs-inodes (fn-bsc-bs s))
                                                           (fn-bs-ops-for-ino (fn-bs-pending (fn-bsc-bs s)) ino)))))
          (equal (fn-bs-next-ino (fn-bsc-bs s3)) (fn-bs-next-ino (fn-bsc-bs s)))
          (equal (fn-bs-pending (fn-bsc-bs s3))
                 (fn-bs-ops-not-for-ino (fn-bs-pending (fn-bsc-bs s)) ino))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bsc-step fn-bsc-bs fn-bsc-content fn-bs-fsync-file fn-bs-fence-file
                             fn-bs-durable-content fn-bs-apply-ops-inodes-are-apply-writes)
                            (fn-bs-apply-writes fn-bs-ops-for-ino fn-bs-ops-not-for-ino fn-bs-apply-ops
                             fn-lgrc-inodes-entry-is-durable-content))))))
(local
 (defthm fn-lgrc-ops-not-for-ino-has-no-writes-to-it
   (fn-lgu-writes-at-or-above (fn-bs-ops-not-for-ino ops ino) ino f)))
(local
 (defthm fn-lgrc-apply-writes-ending-in-a-write-at-0
   (implies ino
            (equal (cdr (assoc-equal ino (fn-bs-apply-writes inodes (append ops (list (list :write ino 0 x))))))
                   (fn-bs-splice (cdr (assoc-equal ino (fn-bs-apply-writes inodes ops))) 0 x)))
   :hints (("Goal" :in-theory (e/d (fn-bs-apply-writes-of-append fn-bs-assoc-of-put-assoc-same)
                                   (fn-bs-splice fn-bs-put-assoc))
            :expand ((:free (in) (fn-bs-apply-writes in (list (list :write ino 0 x))))
                     (:free (in) (fn-bs-apply-writes in nil)))))))

(local
 (defthm fn-lgrc-ops-for-ino-of-create-then-write
   (equal (fn-bs-ops-for-ino (list (list :set-entry d n v) (list :write ino o x)) ino)
          (list (list :write ino o x)))))
;  The empty copy (an empty read, only with an empty prefix).
(local
 (defthm fn-lgrc-write-keeps-next-ino
   (equal (fn-bs-next-ino (fn-bsc-bs (mv-nth 1 (fn-bsc-step s (list :write i o x out)))))
          (fn-bs-next-ino (fn-bsc-bs s)))
   :hints (("Goal" :in-theory (enable fn-bsc-step fn-bsc-bs fn-bs-write fn-bsc-vapply)))))
(local
 (defthm fn-lgrc-writes-at-or-above-0
   (fn-lgu-writes-at-or-above ops ino 0)))
(local
 (defthm fn-lgrc-holdsp-of-an-atom
   (implies (and (fn-lgrc-holdsp x a) (not (consp x)))
            (equal a nil))
   :rule-classes :forward-chaining
   :hints (("Goal" :expand ((fn-bs-take 0 x)) :in-theory (enable fn-lgrc-holdsp)))))
(local
 (defthm fn-lgrc-holdsp-of-nil
   (fn-lgrc-holdsp c nil)
   :hints (("Goal" :expand ((fn-bs-take 0 c)) :in-theory (enable fn-lgrc-holdsp)))))
(local
 (defthm fn-lgrc-staged-inode-is-good-when-empty
   (let* ((ino (fn-bs-next-ino (fn-bsc-bs s)))
          (s1 (mv-nth 1 (fn-bsc-step s (list :create stg stage :ok))))
          (s2 (mv-nth 1 (fn-bsc-step s1 (list :write ino 0 x :ok))))
          (s3 (mv-nth 1 (fn-bsc-step s2 (list :fsync-file ino :ok)))))
     (implies (and (natp ino) (not (fn-bsc-lookup s stg stage))
                   (fn-bs-dir-idp stg) (fn-bs-namep stage))
              (and (equal (fn-bsc-lookup s3 stg stage) ino)
                   (fn-lgrc-goodp s3 ino nil))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lgrc-goodp)
                            (fn-lgrc-holdsp fn-bs-splice fn-bs-take fn-bsc-content fn-bs-durable-content
                             fn-bs-apply-writes fn-bs-ops-for-ino fn-bs-ops-not-for-ino
                             fn-lgrc-inodes-entry-is-durable-content fn-lgu-writes-at-or-above))))))

; The staged inode, written and fenced, is good and visibly named STG/STAGE.
(defthm fn-lgrc-staged-inode-is-good
  (let* ((ino (fn-bs-next-ino (fn-bsc-bs s)))
         (s1 (mv-nth 1 (fn-bsc-step s (list :create stg stage :ok))))
         (s2 (mv-nth 1 (fn-bsc-step s1 (list :write ino 0 x :ok))))
         (s3 (mv-nth 1 (fn-bsc-step s2 (list :fsync-file ino :ok)))))
    (implies (and (natp ino) (not (fn-bsc-lookup s stg stage)) (fn-lgrc-holdsp x a)
                  (true-listp x) (fn-bs-dir-idp stg) (fn-bs-namep stage))
             (and (equal (fn-bsc-lookup s3 stg stage) ino)
                  (fn-lgrc-goodp s3 ino a))))
  :hints (("Goal" :do-not-induct t :cases ((consp x))
           :in-theory (e/d (fn-lgrc-goodp fn-bs-ops-for-ino-of-append)
                           (fn-lgrc-holdsp fn-bs-splice fn-bs-take fn-bsc-content fn-bs-durable-content
                            fn-bs-apply-writes fn-bs-ops-for-ino fn-bs-ops-not-for-ino
                            fn-lgrc-inodes-entry-is-durable-content)))))
; The environment's outcomes are syscall outcomes: success is exactly :ok;
; a failure is (errno . progress) with an errno other than :ok.
(defun fn-lgrc-outcomep (x)
  (declare (xargs :guard t))
  (or (null x) (equal x :ok)
      (and (consp x) (keywordp (car x)) (not (equal (car x) :ok)))))
(defun fn-lgrc-outcomesp (outs)
  (declare (xargs :guard t))
  (if (consp outs)
      (and (fn-lgrc-outcomep (car outs)) (fn-lgrc-outcomesp (cdr outs)))
    t))

(local
 (defthm fn-lgrc-outcomep-of-nth
   (implies (fn-lgrc-outcomesp outs) (fn-lgrc-outcomep (nth i outs)))
   :hints (("Goal" :induct (nth i outs) :in-theory (disable fn-lgrc-outcomep)))))
(local
 (defthm fn-lgrc-out-of-okp
   (implies (fn-lgrc-outcomesp outs)
            (let ((x (fn-lgrc-out outs i)))
              (or (equal x :ok)
                  (and (consp x) (keywordp (car x)) (not (equal (car x) :ok))))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-lgrc-outcomep-of-nth)
            :use ((:instance fn-lgrc-outcomep-of-nth))))))

(local
 (defthm fn-lgrc-zeros-true-listp
   (true-listp (fn-bs-zeros n))
   :hints (("Goal" :in-theory (enable fn-bs-zeros)))))
(local
 (defthm fn-lgrc-consp-of-copy
   (implies (consp o) (consp (fn-lgrc-copy-octets o f)))
   :hints (("Goal" :cases ((zp f))
            :expand ((fn-bs-take f o) (fn-bs-zeros (len o)))
            :in-theory (disable fn-bs-take fn-bs-zeros)))))
(local
 (defthm fn-lgrc-holdsp-of-copy
   (implies (and (fn-lgrc-holdsp o a) (natp f) (<= (len a) f))
            (and (fn-lgrc-holdsp (fn-lgrc-copy-octets o f) a)
                 (true-listp (fn-lgrc-copy-octets o f))))
   :hints (("Goal" :in-theory (e/d (fn-lgrc-holdsp) (fn-bs-take fn-bs-zeros fn-lgrc-take-of-append-short
                                                     fn-lgrc-take-of-take))
            :use ((:instance fn-lgrc-take-of-append-short (f (len a)) (x (fn-bs-take f o))
                             (y (fn-bs-zeros (- (len o) f))))
                  (:instance fn-lgrc-take-of-take (f (len a)) (n f) (x o)))))))
(local
 (defthm fn-lgrc-create-ok-means
   (implies (equal (car (fn-bsc-step s (list :create d n out))) :ok)
            (and (equal out :ok) (not (fn-bsc-lookup s d n))))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-bsc-step)))))
(local
 (defthm fn-lgrc-write-ok-means
   (implies (and (equal (car (fn-bsc-step s (list :write i o x out))) :ok)
                 (fn-lgrc-outcomep out))
            (equal out :ok))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-bsc-step fn-bs-write)))))
(local
 (defthm fn-lgrc-fsync-file-ok-means
   (implies (and (equal (car (fn-bsc-step s (list :fsync-file i out))) :ok)
                 (fn-lgrc-outcomep out))
            (equal out :ok))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-bsc-step fn-bs-fsync-file)))))
(local
 (defthm fn-lgrc-outcomep-of-out
   (implies (fn-lgrc-outcomesp outs) (fn-lgrc-outcomep (fn-lgrc-out outs i)))
   :hints (("Goal" :use ((:instance fn-lgrc-out-of-okp)) :in-theory (disable fn-lgrc-out)))))

(local
 (defthm fn-lgrc-visible-binding-holds-the-prefix
   (implies (fn-lgrc-invp s j k a)
            (and (fn-lgrc-holdsp (fn-bsc-content s (fn-bsc-lookup s j k)) a)
                 (natp (fn-bsc-lookup s j k))))
   :hints (("Goal" :in-theory (enable fn-lgrc-goodp)))))

(local
 (defthm fn-lgrc-invp-has-a-natural-next-ino
   (implies (fn-lgrc-invp s j k a) (natp (fn-bs-next-ino (fn-bsc-bs s))))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-lgrc-goodp)))))
(local
 (defthm fn-lgrc-write-fails-unless-ok
   (implies (and (fn-lgrc-outcomep out) (not (equal out :ok)))
            (not (equal (car (fn-bsc-step s (list :write i o x out))) :ok)))
   :hints (("Goal" :in-theory (enable fn-bsc-step fn-bs-write)))))
(local
 (defthm fn-lgrc-fsync-file-fails-unless-ok
   (implies (and (fn-lgrc-outcomep out) (not (equal out :ok)))
            (not (equal (car (fn-bsc-step s (list :fsync-file i out))) :ok)))
   :hints (("Goal" :in-theory (enable fn-bsc-step fn-bs-fsync-file)))))
(defthm fn-lgrc-attempt-is-within-the-side-conditions
  (implies (and (fn-lgrc-invp s j k a)
                (fn-lgrc-completep a genesis (fn-bs-unit (fn-bsc-bs s)) max)
                (fn-bs-dir-idp stg) (fn-bs-namep stage)
                (not (and (equal stg j) (equal stage k)))
                (fn-lgrc-outcomesp outs))
           (fn-lgrc-run-okp s (fn-lgrc-attempt-ops s j k stg stage genesis max floor outs) j k a))
  :hints (("Goal" :do-not-induct t
           :cases ((not (equal (fn-lgrc-out outs 1) :ok)) (not (equal (fn-lgrc-out outs 2) :ok)))
           :in-theory (e/d () (fn-lgrc-out fn-lgrc-copy-octets fn-lgrc-completep fn-lgrc-holdsp
                               fn-lgt-recover fn-lgk-frontier fn-bsc-content fn-bsc-vinodes))
           :use ((:instance fn-lgrc-scan-of-a-read-holding-a-complete-prefix
                            (o (fn-bsc-content s (fn-bsc-lookup s j k)))
                            (unit (fn-bs-unit (fn-bsc-bs s))))
                 (:instance fn-lgrc-staged-inode-is-good
                            (x (fn-lgrc-copy-octets
                                (fn-bsc-content s (fn-bsc-lookup s j k))
                                (fn-lgk-frontier (fn-lgt-recover (fn-bsc-content s (fn-bsc-lookup s j k))
                                                                 genesis (fn-bs-unit (fn-bsc-bs s)) max floor)))))))))
; KEYSTONE (the attempt).  From the invariant over a complete acknowledged
; prefix A, every state of an attempt -- at every cut, under any outcomes
; the environment chooses -- keeps the invariant: the old inode is never
; written, the staged inode is named journal/K only after its own fence
; succeeded, and journal/K is never unnamed.
(defthm fn-lgrc-attempt-keeps-the-invariant
  (implies (and (fn-lgrc-invp s j k a)
                (fn-lgrc-completep a genesis (fn-bs-unit (fn-bsc-bs s)) max)
                (fn-bs-dir-idp stg) (fn-bs-namep stage)
                (not (and (equal stg j) (equal stage k)))
                (fn-lgrc-outcomesp outs))
           (fn-lgrc-all-invp (fn-lgrc-attempt s j k stg stage genesis max floor outs) j k a))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lgrc-attempt-ops fn-lgrc-invp fn-lgrc-completep)
           :use ((:instance fn-lgrc-attempt-is-within-the-side-conditions)
                 (:instance fn-lgrc-run-keeps-the-invariant
                            (ops (fn-lgrc-attempt-ops s j k stg stage genesis max floor outs)))))))

; -----------------------------------------------------------------------------
; 5. K2: the world -- any number of attempts, interrupted anywhere, with
; evictions, exits, cache losses and anyone else's steps in between.

(defthm fn-bsc-step-keeps-the-unit
  (equal (fn-bs-unit (fn-bsc-bs (mv-nth 1 (fn-bsc-step s op)))) (fn-bs-unit (fn-bsc-bs s)))
  :hints (("Goal" :in-theory (enable fn-bsc-step fn-bsc-bs fn-bsc-vapply fn-bs-write fn-bs-fsync-file
                                     fn-bs-fsync-dir fn-bs-fence-file fn-bs-fence-dir fn-bs-crash))))

(defthm fn-bsc-run-keeps-the-unit
  (implies (member-equal x (fn-bsc-run s ops))
           (equal (fn-bs-unit (fn-bsc-bs x)) (fn-bs-unit (fn-bsc-bs s))))
  :hints (("Goal" :induct (fn-bsc-run s ops) :in-theory (disable fn-bsc-step))))

(defthm fn-lgrc-all-invp-of-last
  (implies (and (fn-lgrc-all-invp states j k a) (consp states))
           (fn-lgrc-invp (car (last states)) j k a))
  :hints (("Goal" :induct (fn-lgrc-all-invp states j k a) :in-theory (disable fn-lgrc-invp))))

(defthm fn-lgrc-all-invp-of-append
  (equal (fn-lgrc-all-invp (append x y) j k a)
         (and (fn-lgrc-all-invp x j k a) (fn-lgrc-all-invp y j k a)))
  :hints (("Goal" :in-theory (disable fn-lgrc-invp))))
; The world: any sequence of events from S.  An event is an attempt
; (:attempt STG STAGE OUTS), or one step of the cache model by anyone else:
; the served run's appends and barriers, other files' writes, creates,
; renames and fences, cache evictions, process exits (:exit) and cache
; losses (:lose-cache).  Answers every state, in order.
(defun fn-lgrc-world (s events j k genesis max floor)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (let ((e (car events)))
        (if (and (consp e) (equal (car e) :attempt))
            (let* ((run (fn-lgrc-attempt s j k (nth 1 e) (nth 2 e) genesis max floor (nth 3 e)))
                   (s1 (if (consp run) (car (last run)) s)))
              (append run (fn-lgrc-world s1 (cdr events) j k genesis max floor)))
          (mv-let (r s1) (fn-bsc-step s e)
            (declare (ignore r))
            (cons s1 (fn-lgrc-world s1 (cdr events) j k genesis max floor)))))
    nil))

; What the world may do: an attempt stages under a name that is not
; journal/K, with syscall outcomes; any other step keeps its side condition
; (fn-lgrc-op-okp) at the state it runs in.
(defun fn-lgrc-world-okp (s events j k a genesis max floor)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (let ((e (car events)))
        (if (and (consp e) (equal (car e) :attempt))
            (let* ((run (fn-lgrc-attempt s j k (nth 1 e) (nth 2 e) genesis max floor (nth 3 e)))
                   (s1 (if (consp run) (car (last run)) s)))
              (and (fn-bs-dir-idp (nth 1 e)) (fn-bs-namep (nth 2 e))
                   (not (and (equal (nth 1 e) j) (equal (nth 2 e) k)))
                   (fn-lgrc-outcomesp (nth 3 e))
                   (fn-lgrc-world-okp s1 (cdr events) j k a genesis max floor)))
          (mv-let (r s1) (fn-bsc-step s e)
            (declare (ignore r))
            (and (fn-lgrc-op-okp s e j k a)
                 (fn-lgrc-world-okp s1 (cdr events) j k a genesis max floor)))))
    t))

(local
 (defthm fn-lgrc-last-is-a-member
   (implies (consp x) (member-equal (car (last x)) x))))

(local
 (defthm fn-lgrc-attempt-keeps-the-unit
   (implies (consp (fn-lgrc-attempt s j k stg stage genesis max floor outs))
            (equal (fn-bs-unit (fn-bsc-bs (car (last (fn-lgrc-attempt s j k stg stage genesis max floor outs)))))
                   (fn-bs-unit (fn-bsc-bs s))))
   :hints (("Goal" :in-theory (disable fn-lgrc-attempt-ops fn-bsc-run-keeps-the-unit)
            :use ((:instance fn-bsc-run-keeps-the-unit
                             (x (car (last (fn-lgrc-attempt s j k stg stage genesis max floor outs))))
                             (ops (fn-lgrc-attempt-ops s j k stg stage genesis max floor outs))))))))
(local
 (defthm fn-lgrc-attempt-ends-in-the-invariant
   (implies (and (fn-lgrc-invp s j k a)
                 (fn-lgrc-completep a genesis (fn-bs-unit (fn-bsc-bs s)) max)
                 (fn-bs-dir-idp stg) (fn-bs-namep stage)
                 (not (and (equal stg j) (equal stage k)))
                 (fn-lgrc-outcomesp outs)
                 (consp (fn-lgrc-attempt s j k stg stage genesis max floor outs)))
            (fn-lgrc-invp (car (last (fn-lgrc-attempt s j k stg stage genesis max floor outs))) j k a))
   :hints (("Goal" :in-theory (disable fn-lgrc-attempt fn-lgrc-invp fn-lgrc-completep)
            :use ((:instance fn-lgrc-attempt-keeps-the-invariant))))))
; KEYSTONE (K2, the world).  From the invariant over a complete
; acknowledged prefix A, every state of any world -- any number of
; attempts, each interrupted at any cut or failing at any syscall
; (a failed journal/ fence, then :exit, then another attempt that reads a
; visible-but-not-durable replacement and copies it again, ...), other
; files' activity, evictions, exits and cache losses -- keeps the
; invariant.
(defthm fn-lgrc-world-keeps-the-invariant
  (implies (and (fn-lgrc-invp s j k a)
                (fn-lgrc-completep a genesis (fn-bs-unit (fn-bsc-bs s)) max)
                (fn-lgrc-world-okp s events j k a genesis max floor))
           (fn-lgrc-all-invp (fn-lgrc-world s events j k genesis max floor) j k a))
  :hints (("Goal" :induct (fn-lgrc-world-okp s events j k a genesis max floor)
           :in-theory (disable fn-lgrc-invp fn-lgrc-completep fn-lgrc-attempt fn-bsc-step
                               fn-lgrc-op-okp))))
(local
 (defthm fn-lgrc-all-invp-member
   (implies (and (fn-lgrc-all-invp states j k a) (member-equal x states))
            (fn-lgrc-invp x j k a))
   :hints (("Goal" :in-theory (disable fn-lgrc-invp)))))

(local
 (defthm fn-lgrc-attempt-member-keeps-the-unit
   (implies (member-equal x (fn-lgrc-attempt s j k stg stage genesis max floor outs))
            (equal (fn-bs-unit (fn-bsc-bs x)) (fn-bs-unit (fn-bsc-bs s))))
   :hints (("Goal" :in-theory (disable fn-lgrc-attempt-ops)))))
(defthm fn-lgrc-world-keeps-the-unit
  (implies (member-equal x (fn-lgrc-world s events j k genesis max floor))
           (equal (fn-bs-unit (fn-bsc-bs x)) (fn-bs-unit (fn-bsc-bs s))))
  :hints (("Goal" :induct (fn-lgrc-world s events j k genesis max floor)
           :in-theory (e/d (fn-bs-member-of-append) (fn-lgrc-attempt fn-bsc-step)))))

; KEYSTONE (K2, discoverable).  At every state of any world, in every
; image a cache loss can leave, the inode journal/K DURABLY names holds the
; acknowledged prefix A, and the open's scan of it reads A's records first.
; The quantity is the durable binding (fn-bs-durable-entry of the image),
; never the visible one.
(defthm fn-lgrc-world-binds-the-acknowledged-records-in-every-image
  (implies (and (fn-lgrc-invp s j k a)
                (fn-lgrc-completep a genesis (fn-bs-unit (fn-bsc-bs s)) max)
                (fn-lgrc-world-okp s events j k a genesis max floor)
                (member-equal x (fn-lgrc-world s events j k genesis max floor))
                (fn-bs-crash-imagep (fn-bsc-bs x) image))
           (let* ((i (fn-bs-durable-entry image j k))
                  (c (fn-bs-durable-content image i))
                  (unit (fn-bs-unit (fn-bsc-bs s)))
                  (acked (car (fn-lg-scan a genesis unit max)))
                  (scan (fn-lg-scan c genesis unit max)))
             (and (fn-bs-inop i)
                  (fn-lgrc-holdsp c a)
                  (<= (len a) (cdr scan))
                  (equal (take (len acked) (car scan)) acked))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-crash-imagep fn-lgrc-holdsp)
                           (fn-lgrc-invp fn-lgrc-completep fn-lgrc-world fn-lgrc-world-okp
                            fn-bs-crash fn-bs-durable-entry fn-bs-durable-content fn-lg-scan
                            fn-bs-take fn-lgrc-every-image-binds-the-acknowledged-prefix))
           :use ((:instance fn-lgrc-world-keeps-the-invariant)
                 (:instance fn-lgrc-all-invp-member (states (fn-lgrc-world s events j k genesis max floor)))
                 (:instance fn-lgrc-world-keeps-the-unit)
                 (:instance fn-lgrc-every-image-binds-the-acknowledged-prefix
                            (s x) (choices (fn-bs-crash-imagep-witness (fn-bsc-bs x) image)))
                 (:instance fn-lgrc-scan-of-a-read-holding-a-complete-prefix
                            (o (fn-bs-durable-content image (fn-bs-durable-entry image j k)))
                            (unit (fn-bs-unit (fn-bsc-bs s))))))))

; -----------------------------------------------------------------------------
; 6. K1: an attempt that succeeds makes the READ prefix durable.

(local
 (defthm fn-lgrc-after-rename-ok
   (let ((s4 (mv-nth 1 (fn-bsc-step s (list :rename sd sn dd dn :ok))))
         (ino (fn-bsc-lookup s sd sn)))
     (implies (fn-bs-inop ino)
              (and (equal (car (fn-bsc-step s (list :rename sd sn dd dn :ok))) :ok)
                   (equal (fn-bs-inodes (fn-bsc-bs s4)) (fn-bs-inodes (fn-bsc-bs s)))
                   (equal (fn-bs-dirs (fn-bsc-bs s4)) (fn-bs-dirs (fn-bsc-bs s)))
                   (equal (fn-bs-unit (fn-bsc-bs s4)) (fn-bs-unit (fn-bsc-bs s)))
                   (equal (fn-bs-next-ino (fn-bsc-bs s4)) (fn-bs-next-ino (fn-bsc-bs s)))
                   (equal (fn-bs-pending (fn-bsc-bs s4))
                          (append (fn-bs-pending (fn-bsc-bs s))
                                  (list (list :set-entry dd dn ino) (list :del-entry sd sn)))))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bsc-step fn-bsc-bs fn-bsc-vapply) (fn-bs-apply-op fn-bsc-lookup))))))
(local
 (defthm fn-lgrc-after-fsync-dir-ok
   (let ((s5 (mv-nth 1 (fn-bsc-step s (list :fsync-dir d :ok)))))
     (and (equal (car (fn-bsc-step s (list :fsync-dir d :ok))) :ok)
          (equal (fn-bs-inodes (fn-bsc-bs s5)) (fn-bs-inodes (fn-bsc-bs s)))
          (equal (fn-bs-dirs (fn-bsc-bs s5))
                 (fn-bs-apply-entries (fn-bs-dirs (fn-bsc-bs s))
                                      (fn-bs-ops-for-dir (fn-bs-pending (fn-bsc-bs s)) d)))
          (equal (fn-bs-unit (fn-bsc-bs s5)) (fn-bs-unit (fn-bsc-bs s)))
          (equal (fn-bs-next-ino (fn-bsc-bs s5)) (fn-bs-next-ino (fn-bsc-bs s)))
          (equal (fn-bs-pending (fn-bsc-bs s5))
                 (fn-bs-ops-not-for-dir (fn-bs-pending (fn-bsc-bs s)) d))
          (equal (fn-bsc-lookup s5 dd nn) (fn-bsc-lookup s dd nn))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bsc-step fn-bsc-bs fn-bsc-lookup fn-bs-fsync-dir fn-bs-fence-dir
                             fn-bs-apply-ops-inodes-are-apply-writes fn-bs-apply-ops-dirs-are-apply-entries
                             fn-bs-apply-writes-of-ops-for-dir)
                            (fn-bs-apply-entries fn-bs-ops-for-dir fn-bs-ops-not-for-dir fn-bs-apply-ops))))))
(local
 (defthm fn-lgrc-after-fsync-file-keeps-names
   (let ((s3 (mv-nth 1 (fn-bsc-step s (list :fsync-file ino :ok)))))
     (and (equal (fn-bs-dirs (fn-bsc-bs s3)) (fn-bs-dirs (fn-bsc-bs s)))
          (equal (fn-bs-unit (fn-bsc-bs s3)) (fn-bs-unit (fn-bsc-bs s)))
          (equal (fn-bsc-lookup s3 dd nn) (fn-bsc-lookup s dd nn))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bsc-step fn-bsc-bs fn-bsc-lookup fn-bs-fsync-file fn-bs-fence-file
                             fn-bs-apply-ops-dirs-are-apply-entries fn-bs-apply-entries-of-ops-for-ino)
                            (fn-bs-apply-entries fn-bs-ops-for-ino fn-bs-ops-not-for-ino fn-bs-apply-ops))))))
(local
 (defthm fn-lgrc-create-keeps-dirs-and-unit
   (let ((s1 (mv-nth 1 (fn-bsc-step s (list :create d n out)))))
     (and (equal (fn-bs-dirs (fn-bsc-bs s1)) (fn-bs-dirs (fn-bsc-bs s)))
          (equal (fn-bs-unit (fn-bsc-bs s1)) (fn-bs-unit (fn-bsc-bs s)))))
   :hints (("Goal" :in-theory (enable fn-bsc-step fn-bsc-bs)))))
(local
 (defthm fn-lgrc-write-keeps-dirs-and-unit
   (let ((s1 (mv-nth 1 (fn-bsc-step s (list :write i o x out)))))
     (and (equal (fn-bs-dirs (fn-bsc-bs s1)) (fn-bs-dirs (fn-bsc-bs s)))
          (equal (fn-bs-unit (fn-bsc-bs s1)) (fn-bs-unit (fn-bsc-bs s)))))
   :hints (("Goal" :in-theory (enable fn-bsc-step fn-bsc-bs fn-bs-write fn-bsc-vapply)))))
(local
 (defthm fn-lgrc-splice-into-nothing
   (implies (true-listp x) (equal (fn-bs-splice nil 0 x) x))
   :hints (("Goal" :expand ((fn-bs-take 0 nil)) :in-theory (enable fn-bs-splice)))))

(local
 (defthm fn-lgrc-after-fsync-file-ok-inodes
   (equal (cdr (assoc-equal ino (fn-bs-inodes (fn-bsc-bs (mv-nth 1 (fn-bsc-step s (list :fsync-file ino :ok)))))))
          (cdr (assoc-equal ino (fn-bs-apply-writes (fn-bs-inodes (fn-bsc-bs s))
                                                    (fn-bs-ops-for-ino (fn-bs-pending (fn-bsc-bs s)) ino)))))
   :hints (("Goal" :in-theory (e/d (fn-bs-durable-content) (fn-lgrc-after-fsync-file-ok fn-bsc-step fn-lgrc-inodes-entry-is-durable-content))
            :use ((:instance fn-lgrc-after-fsync-file-ok))))))
; The six steps under :ok from a quiet store publish the copy: journal/K
; durably names the staged inode, which durably holds the copy, and
; nothing is pending.
(defthm fn-lgrc-copy-chain-publishes
  (let* ((ino (fn-bs-next-ino (fn-bsc-bs s)))
         (s1 (mv-nth 1 (fn-bsc-step s (list :create stg stage :ok))))
         (s2 (mv-nth 1 (fn-bsc-step s1 (list :write ino 0 x :ok))))
         (s3 (mv-nth 1 (fn-bsc-step s2 (list :fsync-file ino :ok))))
         (s4 (mv-nth 1 (fn-bsc-step s3 (list :rename stg stage j k :ok))))
         (s5 (mv-nth 1 (fn-bsc-step s4 (list :fsync-dir j :ok))))
         (s6 (mv-nth 1 (fn-bsc-step s5 (list :fsync-dir stg :ok))))
         (bs6 (fn-bsc-bs s6)))
    (implies (and (natp ino) (not (fn-bsc-lookup s stg stage))
                  (fn-bs-dir-idp stg) (fn-bs-namep stage) (fn-bs-dir-idp j) (fn-bs-namep k)
                  (not (and (equal stg j) (equal stage k)))
                  (true-listp x) (consp x)
                  (null (fn-bs-pending (fn-bsc-bs s))))
             (and (equal (fn-bs-durable-entry bs6 j k) ino)
                  (equal (fn-bs-durable-content bs6 ino) x)
                  (equal (fn-bs-unit bs6) (fn-bs-unit (fn-bsc-bs s)))
                  (null (fn-bs-pending bs6)))))
  :hints (("Goal" :do-not-induct t
           :cases ((equal stg j))
           :in-theory (e/d (fn-bs-durable-entry fn-bs-durable-content fn-bs-ops-for-ino-of-append
                            fn-bs-apply-entries-entry-is-entry-after fn-bs-entry-after
                            fn-bs-assoc-of-put-assoc-same fn-bs-assoc-of-put-assoc-other
                            fn-bs-assoc-of-del-assoc-other fn-bs-assoc-of-del-assoc-same)
                           (fn-bsc-step fn-bsc-lookup fn-bsc-content fn-bs-splice fn-bs-put-assoc
                            fn-lgrc-inodes-entry-is-durable-content)))))

(local
 (defthm fn-lgrc-durable-content-names-an-inode
   (implies (consp (fn-bs-durable-content bs i)) (assoc-equal i (fn-bs-inodes bs)))
   :hints (("Goal" :in-theory (e/d (fn-bs-durable-content) (fn-lgrc-inodes-entry-is-durable-content)))))
)
(local
 (defthm fn-lgrc-zerosp-of-zeros
   (fn-lg-zerosp (fn-bs-zeros n))
   :hints (("Goal" :in-theory (enable fn-bs-zeros fn-lg-zerosp)))))
(local
 (defthm fn-lgrc-len-of-zeros
   (equal (len (fn-bs-zeros n)) (nfix n))
   :hints (("Goal" :in-theory (enable fn-bs-zeros)))))
(local
 (defthm fn-lgrc-nthcdr-of-append-exact
   (implies (equal n (len x))
            (equal (nthcdr n (append x y)) y))))
(local
 (defthm fn-lgrc-copy-octets-shape
   (implies (and (natp f) (<= f (len o)))
            (let ((x (fn-lgrc-copy-octets o f)))
              (and (true-listp x)
                   (equal (len x) (len o))
                   (equal (fn-bs-take f x) (fn-bs-take f o))
                   (fn-lg-zerosp (nthcdr f x)))))
   :hints (("Goal" :in-theory (e/d () (fn-bs-take fn-bs-zeros fn-lg-zerosp))))))

(defun fn-lgrc-final (run s)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp run) (car (last run)) s))

(local
 (defthm fn-lgrc-six-ok-steps-publish
   (let* ((ino (fn-bs-next-ino (fn-bsc-bs s)))
          (run (fn-bsc-run s (list (list :create stg stage :ok)
                                   (list :write ino 0 x :ok)
                                   (list :fsync-file ino :ok)
                                   (list :rename stg stage j k :ok)
                                   (list :fsync-dir j :ok)
                                   (list :fsync-dir stg :ok))))
          (final (fn-bsc-bs (fn-lgrc-final run s))))
     (implies (and (natp ino) (not (fn-bsc-lookup s stg stage))
                   (fn-bs-dir-idp stg) (fn-bs-namep stage) (fn-bs-dir-idp j) (fn-bs-namep k)
                   (not (and (equal stg j) (equal stage k)))
                   (true-listp x) (consp x)
                   (null (fn-bs-pending (fn-bsc-bs s))))
              (and (equal (len run) 6)
                   (equal (fn-bs-durable-entry final j k) ino)
                   (equal (fn-bs-durable-content final ino) x)
                   (equal (fn-bs-unit final) (fn-bs-unit (fn-bsc-bs s)))
                   (null (fn-bs-pending final)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d () (fn-bsc-step fn-lgrc-copy-chain-publishes fn-lgrc-staged-inode-is-good
                                fn-bsc-lookup fn-bs-durable-entry fn-bs-durable-content))
            :use ((:instance fn-lgrc-copy-chain-publishes)
                  (:instance fn-lgrc-staged-inode-is-good (a nil)))))))

(local
 (defthm fn-lgrc-attempt-ops-with-no-failures
   (equal (fn-lgrc-attempt-ops s j k stg stage genesis max floor nil)
          (let ((ino (fn-bs-next-ino (fn-bsc-bs s)))
                (x (fn-lgrc-copy-octets
                    (fn-bsc-content s (fn-bsc-lookup s j k))
                    (fn-lgk-frontier (fn-lgt-recover (fn-bsc-content s (fn-bsc-lookup s j k))
                                                     genesis (fn-bs-unit (fn-bsc-bs s)) max floor)))))
            (list (list :create stg stage :ok)
                  (list :write ino 0 x :ok)
                  (list :fsync-file ino :ok)
                  (list :rename stg stage j k :ok)
                  (list :fsync-dir j :ok)
                  (list :fsync-dir stg :ok))))
   :hints (("Goal" :in-theory (disable fn-lgrc-copy-octets fn-lgt-recover fn-lgk-frontier
                                       fn-bsc-content fn-bsc-lookup fn-lgrc-frontier-of-recover)))))
(local
 (defthm fn-lgrc-read-frontier-is-within
   (implies (and (posp unit) (true-listp o) (equal (mod (len o) unit) 0))
            (let ((f (fn-lgk-frontier (fn-lgt-recover o genesis unit max floor))))
              (and (natp f) (<= f (len o)))))
   :hints (("Goal" :in-theory (disable fn-lg-scan fn-lg-scan-last fn-lgt-recover)
            :use ((:instance fn-lg-recovered-frontier-is-the-last-complete-record (c o)))))))

; KEYSTONE (K1).  An attempt whose six syscalls all succeed, from a store
; with nothing pending, leaves journal/K DURABLY naming the staged inode,
; which durably holds the read's validated prefix [0, F) and zeros to the
; read's length, with nothing pending; the store is R-related to the
; kernel of what the open READ (by fn-lg-durable-read-prefix-establishes-
; the-relation).  No hypothesis relates the read to the durable content
; before the open: the read may hold a failed barrier's clean pages.
(defthm fn-lgrc-attempt-makes-the-read-prefix-durable
  (let* ((bs (fn-bsc-bs s))
         (unit (fn-bs-unit bs))
         (o (fn-bsc-content s (fn-bsc-lookup s j k)))
         (ks (fn-lgt-recover o genesis unit max floor))
         (ino (fn-bs-next-ino bs))
         (run (fn-lgrc-attempt s j k stg stage genesis max floor nil))
         (final (fn-bsc-bs (fn-lgrc-final run s))))
    (implies (and (natp ino) (fn-bs-dir-idp j) (fn-bs-namep k)
                  (fn-bs-dir-idp stg) (fn-bs-namep stage)
                  (not (and (equal stg j) (equal stage k)))
                  (not (fn-bsc-lookup s stg stage))
                  (null (fn-bs-pending bs))
                  (posp unit) (true-listp o) (consp o) (equal (mod (len o) unit) 0)
                  (fn-frame-digestp genesis))
             (and (equal (len run) 6)
                  (equal (fn-bs-durable-entry final j k) ino)
                  (equal (fn-bs-durable-content final ino)
                         (fn-lgrc-copy-octets o (fn-lgk-frontier ks)))
                  (null (fn-bs-pending final))
                  (fn-lgk-relp final ks ino genesis max))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgrc-durable-content-names-an-inode)
                           (fn-bsc-step fn-bsc-run fn-lgrc-final fn-lgrc-copy-octets fn-lgt-recover
                            fn-lgk-frontier fn-lgrc-frontier-of-recover mod
                            fn-lgk-relp fn-lg-scan fn-bsc-content fn-bsc-lookup
                            fn-bs-durable-content fn-bs-durable-entry fn-lgrc-inodes-entry-is-durable-content
                            fn-lg-durable-read-prefix-establishes-the-relation
                            fn-lgrc-six-ok-steps-publish fn-lgrc-copy-octets-shape))
           :use ((:instance fn-lgrc-read-frontier-is-within
                            (o (fn-bsc-content s (fn-bsc-lookup s j k)))
                            (unit (fn-bs-unit (fn-bsc-bs s))))
                 (:instance fn-lgrc-copy-octets-shape
                            (o (fn-bsc-content s (fn-bsc-lookup s j k)))
                            (f (fn-lgk-frontier (fn-lgt-recover (fn-bsc-content s (fn-bsc-lookup s j k))
                                                                genesis (fn-bs-unit (fn-bsc-bs s)) max floor))))
                 (:instance fn-lgrc-consp-of-copy
                            (o (fn-bsc-content s (fn-bsc-lookup s j k)))
                            (f (fn-lgk-frontier (fn-lgt-recover (fn-bsc-content s (fn-bsc-lookup s j k))
                                                                genesis (fn-bs-unit (fn-bsc-bs s)) max floor))))
                 (:instance fn-lgrc-six-ok-steps-publish
                            (x (fn-lgrc-copy-octets
                                (fn-bsc-content s (fn-bsc-lookup s j k))
                                (fn-lgk-frontier (fn-lgt-recover (fn-bsc-content s (fn-bsc-lookup s j k))
                                                                 genesis (fn-bs-unit (fn-bsc-bs s)) max floor)))))
                 (:instance fn-lg-durable-read-prefix-establishes-the-relation
                            (o (fn-bsc-content s (fn-bsc-lookup s j k)))
                            (ino (fn-bs-next-ino (fn-bsc-bs s)))
                            (bs (fn-bsc-bs (fn-lgrc-final (fn-lgrc-attempt s j k stg stage genesis max floor nil) s))))))))

; -----------------------------------------------------------------------------
; 7. No space: the open refuses by name, before any write.
;
; The copy needs room for the read's length (the segment's extent); the
; host observes the filesystem's free octets (statvfs) before creating the
; staged inode.  Without the room the WRITABLE open refuses
; :recover-copy-no-space: no step is taken, the old basis is untouched,
; and there is no fallback to rewriting in place.  The read-only open
; (readers) is not this program.  An ENOSPC the observation did not
; predict (another writer, delayed allocation) fails the copy's write or
; its fence, and the attempt stops there: fn-lgrc-attempt-keeps-the-
; invariant covers it like any other failed syscall.
(defun fn-lgrc-copy-verdict (free need)
  (declare (xargs :guard t))
  (if (and (natp free) (natp need) (<= need free)) :copy :recover-copy-no-space))

(defthm fn-lgrc-copy-verdict-copies-exactly-with-room
  (equal (equal (fn-lgrc-copy-verdict free need) :copy)
         (and (natp free) (natp need) (<= need free))))

; The refusal's line (host/native/io.lisp fnn-log-recover signals it as the
; open's refusal): SEGMENT the segment's file name, NEED the octets the copy
; needs (the segment's extent), FREE the observation (NIL: unobserved).
(defun fn-lgrc-copy-refusal-text (free need segment)
  (declare (xargs :guard t))
  (concatenate 'string
               "open refused reason=recover-copy-no-space segment="
               (if (stringp segment) segment "?")
               " need=" (fn-lgdm-dec need)
               " free=" (if (natp free) (fn-lgdm-dec free) "unobserved")
               ": the writable open publishes the log segment's validated prefix into a new"
               " file before it serves, and the store's filesystem has not the room; nothing"
               " was written.  Free space on it and open again (read-only commands are unaffected)."))

; The writable open: the verdict over the read's length, then the attempt
; or nothing.  Answers (mv verdict states).
(defun fn-lgrc-open (s j k stg stage genesis max floor free outs)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((o (fn-bsc-content s (fn-bsc-lookup s j k)))
         (verdict (fn-lgrc-copy-verdict free (len o))))
    (if (equal verdict :copy)
        (mv :copy (fn-lgrc-attempt s j k stg stage genesis max floor outs))
      (mv verdict nil))))

; KEYSTONE.  A refused open takes no step (the store is the one it found:
; journal/K, its inodes and its pending operations untouched), and refuses
; by name exactly when the free octets are short of the read's length.
(defthm fn-lgrc-open-refuses-without-room-and-takes-no-step
  (mv-let (verdict states) (fn-lgrc-open s j k stg stage genesis max floor free outs)
    (and (iff (equal verdict :recover-copy-no-space)
              (not (and (natp free)
                        (<= (len (fn-bsc-content s (fn-bsc-lookup s j k))) free))))
         (implies (equal verdict :recover-copy-no-space) (null states))
         (implies (not (equal verdict :recover-copy-no-space))
                  (equal states (fn-lgrc-attempt s j k stg stage genesis max floor outs)))))
  :hints (("Goal" :in-theory (disable fn-lgrc-attempt fn-bsc-content fn-bsc-lookup))))
; -----------------------------------------------------------------------------
; 8. K3: epochs.
;
; While the service runs on journal/K (SERVED), the visible binding V is the
; only inode journal/K can name (no entry operation for it is pending and it
; is the durable binding) and V is good for the kernel's COMMITTED octets
; CM.  A successful attempt establishes it over what the open read; a
; fenced append extends it; an acknowledgement moves the acknowledged
; prefix up to CM; any failure, exit or cache loss ends it.
(defun fn-lgrc-servedp (s j k cm)
  (declare (xargs :guard t :verify-guards nil))
  (let ((v (fn-bsc-lookup s j k)))
    (and (fn-bs-dir-idp j) (fn-bs-namep k)
         (equal (fn-lgrc-candidates (fn-bsc-bs s) j k) (list v))
         (fn-lgrc-goodp s v cm))))

(defthm fn-lgrc-servedp-is-the-invariant
  (implies (fn-lgrc-servedp s j k cm) (fn-lgrc-invp s j k cm))
  :hints (("Goal" :in-theory (disable fn-lgrc-goodp fn-lgrc-candidates))))

(local
 (defthm fn-lgrc-after-rename-ok-visible
   (implies (and (fn-bs-inop (fn-bsc-lookup s sd sn)) (fn-bs-dir-idp dd) (fn-bs-namep dn)
                 (not (and (equal sd dd) (equal sn dn))))
            (let ((s4 (mv-nth 1 (fn-bsc-step s (list :rename sd sn dd dn :ok)))))
              (and (equal (fn-bsc-lookup s4 dd dn) (fn-bsc-lookup s sd sn))
                   (equal (fn-bsc-content s4 i) (fn-bsc-content s i)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bsc-step fn-bsc-vapply fn-bsc-lookup fn-bsc-content fn-bs-apply-op)
                            (fn-bs-put-assoc fn-bs-del-assoc))))))
(local
 (defthm fn-lgrc-fsync-dir-keeps-visible-content
   (equal (fn-bsc-content (mv-nth 1 (fn-bsc-step s (list :fsync-dir d out))) i)
          (fn-bsc-content s i))
   :hints (("Goal" :in-theory (enable fn-bsc-step fn-bsc-content)))))
(local
 (defthm fn-lgrc-write-ok-visible-content
   (implies (and (assoc-equal ino (fn-bs-inodes (fn-bsc-bs s))) (true-listp x) (consp x) ino)
            (equal (fn-bsc-content (mv-nth 1 (fn-bsc-step s (list :write ino 0 x :ok))) ino)
                   (fn-bs-splice (fn-bsc-content s ino) 0 x)))
   :hints (("Goal" :use ((:instance fn-lgrc-after-write-ok))))))
(local
 (defthm fn-lgrc-next-ino-after-rename-and-fsync-dir
   (and (equal (fn-bs-next-ino (fn-bsc-bs (mv-nth 1 (fn-bsc-step s (list :fsync-dir d out)))))
               (fn-bs-next-ino (fn-bsc-bs s)))
        (equal (fn-bs-next-ino (fn-bsc-bs (mv-nth 1 (fn-bsc-step s (list :rename sd sn dd dn out)))))
               (fn-bs-next-ino (fn-bsc-bs s))))
   :hints (("Goal" :in-theory (enable fn-bsc-step fn-bsc-bs fn-bsc-vapply fn-bs-fsync-dir fn-bs-fence-dir)))))
(local
 (defthm fn-lgrc-candidates-when-quiet
   (implies (null (fn-bs-pending bs))
            (equal (fn-lgrc-candidates bs j k) (list (fn-bs-durable-entry bs j k))))
   :hints (("Goal" :in-theory (enable fn-lgrc-candidates)
            :expand ((fn-bs-ops-for-name nil j k))))))

(local
 (defthm fn-lgrc-fsync-of-another-dir-keeps-the-entry
   (implies (and (not (equal d j)) (fn-bs-dir-idp j) (fn-bs-namep k))
            (equal (fn-bs-durable-entry (fn-bsc-bs (mv-nth 1 (fn-bsc-step s (list :fsync-dir d out)))) j k)
                   (fn-bs-durable-entry (fn-bsc-bs s) j k)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bsc-step fn-bsc-bs fn-bs-fsync-dir fn-bs-fence-dir fn-bs-durable-entry
                             fn-bs-apply-ops-dirs-are-apply-entries)
                            (fn-bs-entry-outcomes fn-bs-ops-for-name fn-bs-crash-select
                             fn-bs-ops-for-dir fn-bs-ops-not-for-dir fn-bs-apply-entries
                             fn-bs-apply-ops fn-lgrc-entry-after-is-an-outcome
                             fn-bs-crash-select-entry-is-an-outcome))
            :use ((:instance fn-bs-crash-select-entry-is-an-outcome
                             (ops (fn-bs-ops-for-dir (fn-bs-pending (fn-bsc-bs s)) d))
                             (choices (cdr out)) (unit (fn-bs-unit (fn-bsc-bs s)))
                             (old (fn-bs-durable-entry (fn-bsc-bs s) j k)) (dir j) (name k))
                  (:instance fn-lgrc-entry-after-is-an-outcome
                             (ops (fn-bs-ops-for-dir (fn-bs-pending (fn-bsc-bs s)) d))
                             (old (fn-bs-durable-entry (fn-bsc-bs s) j k)) (d j) (n k))
                  (:instance fn-bs-apply-entries-entry-is-entry-after
                             (dirs (fn-bs-dirs (fn-bsc-bs s))) (dir j) (name k)
                             (ops (fn-bs-crash-select (fn-bs-ops-for-dir (fn-bs-pending (fn-bsc-bs s)) d)
                                                      (cdr out) (fn-bs-unit (fn-bsc-bs s)))))
                  (:instance fn-bs-apply-entries-entry-is-entry-after
                             (dirs (fn-bs-dirs (fn-bsc-bs s))) (dir j) (name k)
                             (ops (fn-bs-ops-for-dir (fn-bs-pending (fn-bsc-bs s)) d))))))))
(local
 (defthm fn-lgrc-six-ok-steps-serve
   (let* ((ino (fn-bs-next-ino (fn-bsc-bs s)))
          (s1 (mv-nth 1 (fn-bsc-step s (list :create stg stage :ok))))
          (s2 (mv-nth 1 (fn-bsc-step s1 (list :write ino 0 x :ok))))
          (s3 (mv-nth 1 (fn-bsc-step s2 (list :fsync-file ino :ok))))
          (s4 (mv-nth 1 (fn-bsc-step s3 (list :rename stg stage j k :ok))))
          (s5 (mv-nth 1 (fn-bsc-step s4 (list :fsync-dir j :ok))))
          (s6 (mv-nth 1 (fn-bsc-step s5 (list :fsync-dir stg :ok)))))
     (implies (and (natp ino) (not (fn-bsc-lookup s stg stage))
                   (fn-bs-dir-idp stg) (fn-bs-namep stage) (fn-bs-dir-idp j) (fn-bs-namep k)
                   (not (and (equal stg j) (equal stage k)))
                   (true-listp x) (consp x) (fn-lgrc-holdsp x p)
                   (null (fn-bs-pending (fn-bsc-bs s))))
              (fn-lgrc-servedp s6 j k p)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lgrc-goodp)
                            (fn-bsc-step fn-lgrc-copy-chain-publishes fn-lgrc-staged-inode-is-good
                             fn-lgrc-candidates fn-bs-durable-content fn-bs-durable-entry fn-lgrc-holdsp
                             fn-lgrc-inodes-entry-is-durable-content))
            :use ((:instance fn-lgrc-copy-chain-publishes)
                  (:instance fn-lgrc-staged-inode-is-good (a nil)))))))
(local
 (defthm fn-lgrc-holdsp-of-splice-at-the-end
   (implies (and (fn-lgrc-holdsp d cm) (true-listp b))
            (fn-lgrc-holdsp (fn-bs-splice d (len cm) b) (append cm b)))
   :hints (("Goal" :in-theory (e/d (fn-bs-splice fn-lgrc-holdsp) (fn-bs-take fn-lgrc-take-of-append-short))
            :use ((:instance fn-lgrc-take-of-append-short (f (+ (len cm) (len b)))
                             (x (append cm b))
                             (y (nthcdr (+ (len cm) (len b)) d))))))))
(local
 (defthm fn-lgrc-apply-writes-ending-in-a-write
   (implies ino
            (equal (cdr (assoc-equal ino (fn-bs-apply-writes inodes (append ops (list (list :write ino o x))))))
                   (fn-bs-splice (cdr (assoc-equal ino (fn-bs-apply-writes inodes ops))) o x)))
   :hints (("Goal" :in-theory (e/d (fn-bs-apply-writes-of-append fn-bs-assoc-of-put-assoc-same)
                                   (fn-bs-splice fn-bs-put-assoc))
            :expand ((:free (in) (fn-bs-apply-writes in (list (list :write ino o x))))
                     (:free (in) (fn-bs-apply-writes in nil)))))))
(local
 (defthm fn-lgrc-after-append-ok
   (let ((s2 (mv-nth 1 (fn-bsc-step s (list :write ino o x :ok)))))
     (implies (and (assoc-equal ino (fn-bs-inodes (fn-bsc-bs s))) (true-listp x) (consp x) ino)
              (and (equal (car (fn-bsc-step s (list :write ino o x :ok))) :ok)
                   (equal (fn-bsc-content s2 ino) (fn-bs-splice (fn-bsc-content s ino) o x))
                   (equal (fn-bs-inodes (fn-bsc-bs s2)) (fn-bs-inodes (fn-bsc-bs s)))
                   (equal (fn-bs-pending (fn-bsc-bs s2))
                          (append (fn-bs-pending (fn-bsc-bs s)) (list (list :write ino o x)))))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bsc-step fn-bsc-bs fn-bsc-content fn-bs-write fn-bsc-vapply
                             fn-bs-apply-op fn-bs-assoc-of-put-assoc-same)
                            (fn-bs-put-assoc fn-bs-splice fn-bs-take))))))

(local
 (defthm fn-lgrc-ops-for-ino-of-one-write
   (equal (fn-bs-ops-for-ino (list (list :write ino o x)) ino) (list (list :write ino o x)))))
; A fenced append extends the served prefix: the batch written at the end
; of CM and fenced :ok makes CM ++ B durable in the bound inode.
(defthm fn-lgrc-fenced-append-extends-the-served-prefix
  (let* ((v (fn-bsc-lookup s j k))
         (s1 (mv-nth 1 (fn-bsc-step s (list :write v (len cm) b :ok))))
         (s2 (mv-nth 1 (fn-bsc-step s1 (list :fsync-file v :ok)))))
    (implies (and (fn-lgrc-servedp s j k cm) (true-listp b) (consp b)
                  (assoc-equal v (fn-bs-inodes (fn-bsc-bs s))))
             (fn-lgrc-servedp s2 j k (append cm b))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgrc-goodp fn-bs-ops-for-ino-of-append)
                           (fn-bsc-step fn-lgrc-holdsp fn-bs-splice fn-bs-take fn-lgrc-candidates
                            fn-bsc-content fn-bsc-lookup fn-bs-durable-content fn-bs-apply-writes
                            fn-bs-ops-for-ino fn-bs-ops-not-for-ino fn-lgrc-inodes-entry-is-durable-content))
           :use ((:instance fn-lgrc-holdsp-of-apply-writes
                            (i (fn-bsc-lookup s j k)) (a cm)
                            (inodes (fn-bs-inodes (fn-bsc-bs s)))
                            (ops (fn-bs-ops-for-ino (fn-bs-pending (fn-bsc-bs s)) (fn-bsc-lookup s j k))))
                 (:instance fn-lgrc-inodes-entry-is-durable-content
                            (x (fn-bsc-bs s)) (i (fn-bsc-lookup s j k)))))))
; While served, anyone else's step under the side condition over CM, other
; than a rename onto journal/K, keeps it served.
(defun fn-lgrc-served-op-okp (s op j k cm)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-lgrc-op-okp s op j k cm)
       (not (and (consp op) (equal (car op) :rename)
                 (equal (nth 3 op) j) (equal (nth 4 op) k)))))

(defthm fn-lgrc-step-keeps-it-served
  (implies (and (fn-lgrc-servedp s j k cm) (fn-lgrc-served-op-okp s op j k cm))
           (fn-lgrc-servedp (mv-nth 1 (fn-bsc-step s op)) j k cm))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d () (fn-lgrc-goodp fn-bsc-step fn-lgrc-candidates fn-bsc-lookup
                               fn-bs-durable-entry fn-lgrc-names-after-evict
                               fn-lgrc-names-after-rename fn-lgrc-names-after-lose-cache
                               fn-lgrc-names-after-fsync-dir))
           :cases ((member-equal (car op) '(:write :fsync-file :create :evict-ino))
                   (equal (car op) :fsync-dir) (equal (car op) :lose-cache)
                   (equal (car op) :evict-dir) (equal (car op) :rename)
                   (equal (car op) :unlink))
           :use ((:instance fn-lgrc-names-after-fsync-dir)
                 (:instance fn-lgrc-names-after-lose-cache)
                 (:instance fn-lgrc-names-after-evict)
                 (:instance fn-lgrc-names-after-rename)))))(local
 (defthm fn-lgrc-copy-holds-the-read-prefix
   (implies (and (natp f) (<= f (len o)))
            (fn-lgrc-holdsp (fn-lgrc-copy-octets o f) (fn-bs-take f o)))
   :hints (("Goal" :in-theory (e/d (fn-lgrc-holdsp) (fn-lgrc-copy-octets fn-bs-take))
            :use ((:instance fn-lgrc-copy-octets-shape))))))

; What an open must see to serve afterwards: the attempt's six syscalls
; succeed, from a store with nothing pending, over a read of whole units.
(defun fn-lgrc-open-servesp (s j k stg stage outs)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((bs (fn-bsc-bs s)) (o (fn-bsc-content s (fn-bsc-lookup s j k))) (unit (fn-bs-unit bs)))
    (and (equal (fn-lgrc-out outs 0) :ok) (equal (fn-lgrc-out outs 1) :ok)
         (equal (fn-lgrc-out outs 2) :ok) (equal (fn-lgrc-out outs 3) :ok)
         (equal (fn-lgrc-out outs 4) :ok) (equal (fn-lgrc-out outs 5) :ok)
         (not (fn-bsc-lookup s stg stage))
         (null (fn-bs-pending bs))
         (posp unit) (true-listp o) (consp o) (equal (mod (len o) unit) 0))))

(defun fn-lgrc-read-prefix (s j k genesis max floor)
  (declare (xargs :guard t :verify-guards nil))
  (let ((o (fn-bsc-content s (fn-bsc-lookup s j k))))
    (fn-bs-take (fn-lgk-frontier (fn-lgt-recover o genesis (fn-bs-unit (fn-bsc-bs s)) max floor)) o)))

(local
 (defthm fn-lgrc-attempt-ops-are-ok-ops
   (implies (and (syntaxp (not (equal outs ''nil))) (fn-lgrc-open-servesp s j k stg stage outs))
            (equal (fn-lgrc-attempt-ops s j k stg stage genesis max floor outs)
                   (fn-lgrc-attempt-ops s j k stg stage genesis max floor nil)))
   :hints (("Goal" :in-theory (disable fn-lgrc-copy-octets fn-lgt-recover fn-lgk-frontier fn-bsc-content
                                       fn-bsc-lookup fn-lgrc-frontier-of-recover fn-lgrc-out mod)))))

; A successful open serves the read's validated prefix.
(defthm fn-lgrc-successful-open-serves-the-read-prefix
  (implies (and (fn-lgrc-open-servesp s j k stg stage outs)
                (natp (fn-bs-next-ino (fn-bsc-bs s))) (fn-bs-dir-idp j) (fn-bs-namep k)
                (fn-bs-dir-idp stg) (fn-bs-namep stage) (not (and (equal stg j) (equal stage k))))
           (let ((run (fn-lgrc-attempt s j k stg stage genesis max floor outs)))
             (and (consp run)
                  (fn-lgrc-servedp (car (last run)) j k (fn-lgrc-read-prefix s j k genesis max floor)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d () (fn-bsc-step fn-lgrc-copy-octets fn-lgt-recover fn-lgk-frontier
                               fn-lgrc-frontier-of-recover mod fn-bsc-content fn-bsc-lookup
                               fn-lgrc-servedp fn-lgrc-out fn-lgrc-six-ok-steps-serve
                               fn-lgrc-copy-holds-the-read-prefix fn-lgrc-copy-octets-shape))
           :use ((:instance fn-lgrc-read-frontier-is-within
                            (o (fn-bsc-content s (fn-bsc-lookup s j k)))
                            (unit (fn-bs-unit (fn-bsc-bs s))))
                 (:instance fn-lgrc-copy-octets-shape
                            (o (fn-bsc-content s (fn-bsc-lookup s j k)))
                            (f (fn-lgk-frontier (fn-lgt-recover (fn-bsc-content s (fn-bsc-lookup s j k))
                                                                genesis (fn-bs-unit (fn-bsc-bs s)) max floor))))
                 (:instance fn-lgrc-consp-of-copy
                            (o (fn-bsc-content s (fn-bsc-lookup s j k)))
                            (f (fn-lgk-frontier (fn-lgt-recover (fn-bsc-content s (fn-bsc-lookup s j k))
                                                                genesis (fn-bs-unit (fn-bsc-bs s)) max floor))))
                 (:instance fn-lgrc-copy-holds-the-read-prefix
                            (o (fn-bsc-content s (fn-bsc-lookup s j k)))
                            (f (fn-lgk-frontier (fn-lgt-recover (fn-bsc-content s (fn-bsc-lookup s j k))
                                                                genesis (fn-bs-unit (fn-bsc-bs s)) max floor))))
                 (:instance fn-lgrc-six-ok-steps-serve
                            (p (fn-lgrc-read-prefix s j k genesis max floor))
                            (x (fn-lgrc-copy-octets
                                (fn-bsc-content s (fn-bsc-lookup s j k))
                                (fn-lgk-frontier (fn-lgt-recover (fn-bsc-content s (fn-bsc-lookup s j k))
                                                                 genesis (fn-bs-unit (fn-bsc-bs s)) max floor)))))))))
(local
 (defthm fn-lgrc-holdsp-of-take
   (implies (and (fn-lgrc-holdsp o a) (natp f) (<= (len a) f))
            (fn-lgrc-holdsp (fn-bs-take f o) a))
   :hints (("Goal" :in-theory (e/d (fn-lgrc-holdsp) (fn-bs-take))))))
(local
 (defthm fn-lgrc-read-prefix-holds-the-acknowledged-prefix
   (implies (and (fn-lgrc-invp s j k a)
                 (fn-lgrc-completep a genesis (fn-bs-unit (fn-bsc-bs s)) max))
            (fn-lgrc-holdsp (fn-lgrc-read-prefix s j k genesis max floor) a))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d () (fn-lgrc-invp fn-lgrc-completep fn-lg-scan fn-bs-take fn-lgrc-holdsp
                                fn-bsc-content fn-bsc-lookup fn-lgt-recover))
            :use ((:instance fn-lgrc-visible-binding-holds-the-prefix)
                  (:instance fn-lgrc-scan-of-a-read-holding-a-complete-prefix
                             (o (fn-bsc-content s (fn-bsc-lookup s j k)))
                             (unit (fn-bs-unit (fn-bsc-bs s)))))))))
(local
 (defthm fn-lgrc-read-prefix-is-complete
   (implies (and (posp (fn-bs-unit (fn-bsc-bs s)))
                 (true-listp (fn-bsc-content s (fn-bsc-lookup s j k)))
                 (equal (mod (len (fn-bsc-content s (fn-bsc-lookup s j k))) (fn-bs-unit (fn-bsc-bs s))) 0))
            (fn-lgrc-completep (fn-lgrc-read-prefix s j k genesis max floor)
                               genesis (fn-bs-unit (fn-bsc-bs s)) max))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d () (fn-lg-scan fn-lg-scan-last fn-bs-take fn-bsc-content fn-bsc-lookup mod))
            :use ((:instance fn-lg-recovered-frontier-is-the-last-complete-record
                             (c (fn-bsc-content s (fn-bsc-lookup s j k)))
                             (unit (fn-bs-unit (fn-bsc-bs s)))))))))
(defun fn-lgrc-pair-each (states ack)
  (declare (xargs :guard t))
  (if (consp states) (cons (cons (car states) ack) (fn-lgrc-pair-each (cdr states) ack)) nil))

; One batch while the service runs: written at the end of CM, then fenced.
; Answers (mv STATES STORE CM' RUNNING'): the batch joins CM only when both
; succeed; any failure ends the service.
(defun fn-lgrc-commit (s cm b wout fout j k)
  (declare (xargs :guard t :verify-guards nil))
  (let ((v (fn-bsc-lookup s j k)))
    (mv-let (r1 s1) (fn-bsc-step s (list :write v (len cm) b wout))
      (if (not (equal r1 :ok))
          (mv (list s1) s1 cm nil)
        (mv-let (r2 s2) (fn-bsc-step s1 (list :fsync-file v fout))
          (mv (list s1 s2) s2 (if (equal r2 :ok) (append cm b) cm) (equal r2 :ok)))))))

; The epochs.  The state carries, besides the store, the acknowledged
; octets ACK, the kernel's committed octets CM, and whether the service
; runs (EST: an open succeeded in this process and nothing failed since).
;   (:open STG STAGE OUTS)   an open: the attempt; the service runs after
;                            it exactly when it succeeded (CM := the read's
;                            validated prefix);
;   (:commit B WOUT FOUT)    while the service runs: the batch B written at
;                            the end of CM and fenced; both :ok extend CM,
;                            any failure ends the service (the node fences);
;   (:ack)                   while the service runs: ACK := CM (the
;                            COMPLETE's acknowledgements, before replies);
;   any other step           anyone's, under the side condition; :exit and
;                            :lose-cache end the service.
; Answers the (store . ACK) pair after every step, in order.
(defun fn-lgrc-epochs (s ack cm est events j k genesis max floor)
  (declare (xargs :guard t :verify-guards nil :measure (len events)))
  (if (consp events)
      (let ((e (car events)) (rest (cdr events)))
        (cond
         ((and (consp e) (equal (car e) :open))
          (let* ((run (fn-lgrc-attempt s j k (nth 1 e) (nth 2 e) genesis max floor (nth 3 e)))
                 (s1 (if (consp run) (car (last run)) s))
                 (serves (fn-lgrc-open-servesp s j k (nth 1 e) (nth 2 e) (nth 3 e))))
            (append (fn-lgrc-pair-each run ack)
                    (fn-lgrc-epochs s1 ack (if serves (fn-lgrc-read-prefix s j k genesis max floor) cm)
                                    serves rest j k genesis max floor))))
         ((and (consp e) (equal (car e) :commit))
          (if (not est)
              (fn-lgrc-epochs s ack cm est rest j k genesis max floor)
            (mv-let (sts s2 cm2 est2) (fn-lgrc-commit s cm (nth 1 e) (nth 2 e) (nth 3 e) j k)
              (append (fn-lgrc-pair-each sts ack)
                      (fn-lgrc-epochs s2 ack cm2 est2 rest j k genesis max floor)))))
         ((and (consp e) (equal (car e) :ack))
          (if est
              (cons (cons s cm) (fn-lgrc-epochs s cm cm est rest j k genesis max floor))
            (fn-lgrc-epochs s ack cm est rest j k genesis max floor)))
         (t (mv-let (r s1) (fn-bsc-step s e)
              (declare (ignore r))
              (cons (cons s1 ack)
                    (fn-lgrc-epochs s1 ack cm
                                    (and est (not (and (consp e) (member-equal (car e) '(:exit :lose-cache)))))
                                    rest j k genesis max floor))))))
    nil))

(defun fn-lgrc-epochs-okp (s ack cm est events j k genesis max floor)
  (declare (xargs :guard t :verify-guards nil :measure (len events)))
  (if (consp events)
      (let ((e (car events)) (rest (cdr events)) (unit (fn-bs-unit (fn-bsc-bs s))))
        (cond
         ((and (consp e) (equal (car e) :open))
          (let* ((run (fn-lgrc-attempt s j k (nth 1 e) (nth 2 e) genesis max floor (nth 3 e)))
                 (s1 (if (consp run) (car (last run)) s))
                 (serves (fn-lgrc-open-servesp s j k (nth 1 e) (nth 2 e) (nth 3 e))))
            (and (fn-bs-dir-idp (nth 1 e)) (fn-bs-namep (nth 2 e))
                 (not (and (equal (nth 1 e) j) (equal (nth 2 e) k)))
                 (fn-lgrc-outcomesp (nth 3 e))
                 (fn-lgrc-epochs-okp s1 ack (if serves (fn-lgrc-read-prefix s j k genesis max floor) cm)
                                     serves rest j k genesis max floor))))
         ((and (consp e) (equal (car e) :commit))
          (if (not est)
              (fn-lgrc-epochs-okp s ack cm est rest j k genesis max floor)
            (and (true-listp (nth 1 e)) (consp (nth 1 e))
                 (fn-lgrc-completep (append cm (nth 1 e)) genesis unit max)
                 (fn-lgrc-outcomep (nth 2 e)) (fn-lgrc-outcomep (nth 3 e))
                 (mv-let (sts s2 cm2 est2) (fn-lgrc-commit s cm (nth 1 e) (nth 2 e) (nth 3 e) j k)
                   (declare (ignore sts))
                   (fn-lgrc-epochs-okp s2 ack cm2 est2 rest j k genesis max floor)))))
         ((and (consp e) (equal (car e) :ack))
          (if est
              (fn-lgrc-epochs-okp s cm cm est rest j k genesis max floor)
            (fn-lgrc-epochs-okp s ack cm est rest j k genesis max floor)))
         (t (mv-let (r s1) (fn-bsc-step s e)
              (declare (ignore r))
              (and (fn-lgrc-op-okp s e j k ack)
                   (or (not est) (fn-lgrc-served-op-okp s e j k cm))
                   (fn-lgrc-epochs-okp s1 ack cm
                                       (and est (not (and (consp e) (member-equal (car e) '(:exit :lose-cache)))))
                                       rest j k genesis max floor))))))
    t))

(defun fn-lgrc-all-pairs-invp (pairs j k ack0)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pairs)
      (and (consp (car pairs))
           (fn-lgrc-invp (car (car pairs)) j k (cdr (car pairs)))
           (fn-lgrc-holdsp (cdr (car pairs)) ack0)
           (fn-lgrc-all-pairs-invp (cdr pairs) j k ack0))
    t))

(local
 (defthm fn-lgrc-holdsp-is-transitive
   (implies (and (fn-lgrc-holdsp x y) (fn-lgrc-holdsp y z))
            (fn-lgrc-holdsp x z))
   :hints (("Goal" :in-theory (e/d (fn-lgrc-holdsp) (fn-bs-take))
            :use ((:instance fn-lgrc-take-of-take (f (len z)) (n (len y))))))))
(local
 (defthm fn-lgrc-holdsp-of-append-right
   (implies (fn-lgrc-holdsp x y) (fn-lgrc-holdsp (append x b) y))
   :hints (("Goal" :in-theory (e/d (fn-lgrc-holdsp) (fn-bs-take))))))
(local
 (defthm fn-lgrc-holdsp-of-self
   (implies (true-listp x) (fn-lgrc-holdsp x x))
   :hints (("Goal" :in-theory (enable fn-lgrc-holdsp fn-bs-take)))))
(local
 (defthm fn-lgrc-holdsp-bounds-the-length
   (implies (fn-lgrc-holdsp x y) (<= (len y) (len x)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-lgrc-holdsp)))))
(local
 (defthm fn-lgrc-completep-is-true-list
   (implies (fn-lgrc-completep a genesis unit max) (true-listp a))
   :rule-classes :forward-chaining))
(local
 (defthm fn-lgrc-all-pairs-of-one-ack
   (implies (and (fn-lgrc-all-invp run j k ack) (fn-lgrc-holdsp ack ack0))
            (fn-lgrc-all-pairs-invp (fn-lgrc-pair-each run ack) j k ack0))
   :hints (("Goal" :induct (fn-lgrc-pair-each run ack) :in-theory (disable fn-lgrc-invp fn-lgrc-holdsp)))))
(local
 (defthm fn-lgrc-all-pairs-of-append
   (equal (fn-lgrc-all-pairs-invp (append x y) j k a0)
          (and (fn-lgrc-all-pairs-invp x j k a0) (fn-lgrc-all-pairs-invp y j k a0)))
   :hints (("Goal" :in-theory (disable fn-lgrc-invp fn-lgrc-holdsp)))))
(local
 (defthm fn-lgrc-write-ok-names-an-inode
   (implies (equal (car (fn-bsc-step s (list :write i o x out))) :ok)
            (assoc-equal i (fn-bs-inodes (fn-bsc-bs s))))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-bsc-step fn-bs-write)))))
(local
 (defthm fn-lgrc-attempt-is-not-empty
   (consp (fn-lgrc-attempt s j k stg stage genesis max floor outs))))
(local
 (defthm fn-lgrc-servedp-parts
   (implies (fn-lgrc-servedp s j k cm)
            (and (fn-bs-dir-idp j) (fn-bs-namep k)
                 (fn-lgrc-goodp s (fn-bsc-lookup s j k) cm)))
   :rule-classes :forward-chaining))
(defun fn-lgrc-epoch-invp (s ack cm est j k genesis max ack0)
  (declare (xargs :guard t :verify-guards nil))
  (let ((unit (fn-bs-unit (fn-bsc-bs s))))
    (and (fn-lgrc-invp s j k ack)
         (fn-lgrc-completep ack genesis unit max)
         (fn-lgrc-holdsp ack ack0)
         (implies est (and (fn-lgrc-servedp s j k cm)
                           (fn-lgrc-completep cm genesis unit max)
                           (fn-lgrc-holdsp cm ack))))))

(local
 (defthm fn-lgrc-open-servesp-reads-whole-units
   (implies (fn-lgrc-open-servesp s j k stg stage outs)
            (and (posp (fn-bs-unit (fn-bsc-bs s)))
                 (true-listp (fn-bsc-content s (fn-bsc-lookup s j k)))
                 (equal (mod (len (fn-bsc-content s (fn-bsc-lookup s j k))) (fn-bs-unit (fn-bsc-bs s))) 0)))
   :rule-classes :forward-chaining))
(local
 (defthm fn-lgrc-invp-names
   (implies (fn-lgrc-invp s j k a) (and (fn-bs-dir-idp j) (fn-bs-namep k)))
   :rule-classes :forward-chaining))
(local
 (defthm fn-lgrc-epoch-open
   (let* ((run (fn-lgrc-attempt s j k stg stage genesis max floor outs))
          (s1 (car (last run)))
          (serves (fn-lgrc-open-servesp s j k stg stage outs)))
     (implies (and (fn-lgrc-epoch-invp s ack cm est j k genesis max ack0)
                   (fn-bs-dir-idp stg) (fn-bs-namep stage) (not (and (equal stg j) (equal stage k)))
                   (fn-lgrc-outcomesp outs))
              (and (fn-lgrc-all-pairs-invp (fn-lgrc-pair-each run ack) j k ack0)
                   (fn-lgrc-epoch-invp s1 ack (if serves (fn-lgrc-read-prefix s j k genesis max floor) cm)
                                       serves j k genesis max ack0))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d () (fn-lgrc-attempt fn-lgrc-invp fn-lgrc-completep fn-lgrc-holdsp
                                fn-lgrc-servedp fn-lgrc-open-servesp fn-lgrc-read-prefix))
            :use ((:instance fn-lgrc-attempt-keeps-the-invariant (a ack))
                  (:instance fn-lgrc-attempt-ends-in-the-invariant (a ack))
                  (:instance fn-lgrc-successful-open-serves-the-read-prefix)
                  (:instance fn-lgrc-read-prefix-holds-the-acknowledged-prefix (a ack))
                  (:instance fn-lgrc-invp-has-a-natural-next-ino (a ack))
                  (:instance fn-lgrc-read-prefix-is-complete))
            :cases ((fn-lgrc-open-servesp s j k stg stage outs)))
           ("Subgoal 2" :in-theory (e/d (fn-lgrc-open-servesp)
                                        (fn-lgrc-attempt fn-lgrc-invp fn-lgrc-completep fn-lgrc-holdsp
                                         fn-lgrc-servedp fn-lgrc-read-prefix))))))
(local
 (defthm fn-lgrc-epoch-commit
   (let ((v (fn-bsc-lookup s j k)))
     (mv-let (r1 s1) (fn-bsc-step s (list :write v (len cm) b wout))
       (mv-let (r2 s2) (fn-bsc-step s1 (list :fsync-file v fout))
         (implies (and (fn-lgrc-epoch-invp s ack cm t j k genesis max ack0)
                       (true-listp b) (consp b)
                       (fn-lgrc-completep (append cm b) genesis (fn-bs-unit (fn-bsc-bs s)) max)
                       (fn-lgrc-outcomep wout) (fn-lgrc-outcomep fout))
                  (and (fn-lgrc-invp s1 j k ack)
                       (fn-lgrc-epoch-invp s1 ack cm nil j k genesis max ack0)
                       (implies (equal r1 :ok)
                                (and (fn-lgrc-invp s2 j k ack)
                                     (fn-lgrc-epoch-invp s2 ack cm nil j k genesis max ack0)
                                     (implies (equal r2 :ok)
                                              (fn-lgrc-epoch-invp s2 ack (append cm b) t
                                                                  j k genesis max ack0)))))))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lgrc-op-okp)
                            (fn-bsc-step fn-lgrc-invp fn-lgrc-completep fn-lgrc-holdsp fn-lgrc-servedp
                             fn-lgrc-goodp fn-lgrc-candidates fn-bsc-lookup fn-lgrc-outcomep))
            :cases ((equal wout :ok))
            :use ((:instance fn-lgrc-step-keeps-the-invariant (a ack)
                             (op (list :write (fn-bsc-lookup s j k) (len cm) b wout)))
                  (:instance fn-lgrc-step-keeps-the-invariant (a ack)
                             (s (mv-nth 1 (fn-bsc-step s (list :write (fn-bsc-lookup s j k) (len cm) b wout))))
                             (op (list :fsync-file (fn-bsc-lookup s j k) fout)))
                  (:instance fn-lgrc-fenced-append-extends-the-served-prefix)
                  (:instance fn-bsc-step-keeps-the-unit
                             (op (list :write (fn-bsc-lookup s j k) (len cm) b wout)))
                  (:instance fn-bsc-step-keeps-the-unit
                             (s (mv-nth 1 (fn-bsc-step s (list :write (fn-bsc-lookup s j k) (len cm) b wout))))
                             (op (list :fsync-file (fn-bsc-lookup s j k) fout)))))
           ("Subgoal 1" :cases ((equal fout :ok))))))
(local
 (defthm fn-lgrc-epoch-invp-parts
   (implies (fn-lgrc-epoch-invp s ack cm est j k genesis max ack0)
            (and (fn-lgrc-invp s j k ack)
                 (fn-lgrc-holdsp ack ack0)))
   :rule-classes :forward-chaining))
(local
 (defthm fn-lgrc-epoch-commit-step
   (mv-let (sts s2 cm2 est2) (fn-lgrc-commit s cm b wout fout j k)
     (implies (and (fn-lgrc-epoch-invp s ack cm t j k genesis max ack0)
                   (true-listp b) (consp b)
                   (fn-lgrc-completep (append cm b) genesis (fn-bs-unit (fn-bsc-bs s)) max)
                   (fn-lgrc-outcomep wout) (fn-lgrc-outcomep fout))
              (and (fn-lgrc-all-pairs-invp (fn-lgrc-pair-each sts ack) j k ack0)
                   (booleanp est2)
                   (fn-lgrc-epoch-invp s2 ack cm2 est2 j k genesis max ack0))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d () (fn-lgrc-epoch-invp fn-bsc-step fn-lgrc-invp fn-lgrc-holdsp
                                fn-lgrc-epoch-commit fn-bsc-lookup fn-lgrc-completep fn-lgrc-outcomep))
            :use ((:instance fn-lgrc-epoch-commit))))))
(local
 (defthm fn-lgrc-epoch-ack
   (implies (fn-lgrc-epoch-invp s ack cm t j k genesis max ack0)
            (and (fn-lgrc-invp s j k cm)
                 (fn-lgrc-holdsp cm ack0)
                 (fn-lgrc-epoch-invp s cm cm t j k genesis max ack0)))
   :hints (("Goal" :in-theory (disable fn-lgrc-invp fn-lgrc-holdsp fn-lgrc-servedp fn-lgrc-completep)))))

(local
 (defthm fn-lgrc-epoch-other
   (implies (and (fn-lgrc-epoch-invp s ack cm est j k genesis max ack0)
                 (fn-lgrc-op-okp s e j k ack)
                 (or (not est) (fn-lgrc-served-op-okp s e j k cm)))
            (and (fn-lgrc-invp (mv-nth 1 (fn-bsc-step s e)) j k ack)
                 (fn-lgrc-epoch-invp (mv-nth 1 (fn-bsc-step s e)) ack cm
                                     (and est (not (and (consp e) (member-equal (car e) '(:exit :lose-cache)))))
                                     j k genesis max ack0)))
   :hints (("Goal" :in-theory (disable fn-bsc-step fn-lgrc-invp fn-lgrc-holdsp fn-lgrc-servedp
                                       fn-lgrc-completep fn-lgrc-op-okp fn-lgrc-served-op-okp)))))
(local
 (defthm fn-lgrc-epoch-invp-of-a-running-service
   (implies (and est (not (equal est t)))
            (equal (fn-lgrc-epoch-invp s ack cm est j k genesis max ack0)
                   (fn-lgrc-epoch-invp s ack cm t j k genesis max ack0)))))
(local
 (defthm fn-lgrc-epoch-open-serves
   (implies (and (fn-lgrc-epoch-invp s ack cm est j k genesis max ack0)
                 (fn-bs-dir-idp stg) (fn-bs-namep stage) (not (and (equal stg j) (equal stage k)))
                 (fn-lgrc-outcomesp outs))
            (and (fn-lgrc-all-pairs-invp (fn-lgrc-pair-each (fn-lgrc-attempt s j k stg stage genesis max floor outs) ack) j k ack0)
                 (implies (fn-lgrc-open-servesp s j k stg stage outs)
                          (fn-lgrc-epoch-invp (car (last (fn-lgrc-attempt s j k stg stage genesis max floor outs)))
                                              ack (fn-lgrc-read-prefix s j k genesis max floor)
                                              t j k genesis max ack0))
                 (implies (not (fn-lgrc-open-servesp s j k stg stage outs))
                          (fn-lgrc-epoch-invp (car (last (fn-lgrc-attempt s j k stg stage genesis max floor outs)))
                                              ack cm nil j k genesis max ack0))))
   :hints (("Goal" :in-theory (disable fn-lgrc-epoch-invp fn-lgrc-attempt fn-lgrc-open-servesp
                                       fn-lgrc-read-prefix fn-lgrc-epoch-open)
            :use ((:instance fn-lgrc-epoch-open))))))

(local
 (defthm fn-lgrc-epoch-other-stopped
   (implies (and (fn-lgrc-epoch-invp s ack cm nil j k genesis max ack0)
                 (fn-lgrc-op-okp s e j k ack))
            (and (fn-lgrc-invp (mv-nth 1 (fn-bsc-step s e)) j k ack)
                 (fn-lgrc-epoch-invp (mv-nth 1 (fn-bsc-step s e)) ack cm nil j k genesis max ack0)))
   :hints (("Goal" :in-theory (disable fn-lgrc-epoch-invp fn-lgrc-epoch-other fn-bsc-step fn-lgrc-invp
                                       fn-lgrc-op-okp)
            :use ((:instance fn-lgrc-epoch-other (est nil)))))))
(local
 (defthm fn-lgrc-epoch-invp-stops
   (implies (fn-lgrc-epoch-invp s ack cm t j k genesis max ack0)
            (fn-lgrc-epoch-invp s ack cm nil j k genesis max ack0))))
(local
 (defthm fn-lgrc-epoch-other-running
   (implies (and (fn-lgrc-epoch-invp s ack cm t j k genesis max ack0)
                 (fn-lgrc-op-okp s e j k ack)
                 (fn-lgrc-served-op-okp s e j k cm))
            (and (fn-lgrc-invp (mv-nth 1 (fn-bsc-step s e)) j k ack)
                 (fn-lgrc-epoch-invp (mv-nth 1 (fn-bsc-step s e)) ack cm nil j k genesis max ack0)
                 (implies (not (and (consp e) (member-equal (car e) '(:exit :lose-cache))))
                          (fn-lgrc-epoch-invp (mv-nth 1 (fn-bsc-step s e)) ack cm t j k genesis max ack0))))
   :hints (("Goal" :in-theory (disable fn-lgrc-epoch-invp fn-lgrc-epoch-other fn-bsc-step fn-lgrc-invp
                                       fn-lgrc-op-okp fn-lgrc-served-op-okp)
            :use ((:instance fn-lgrc-epoch-other (est t))
                  (:instance fn-lgrc-epoch-other-stopped))))))
(local
 (defthm fn-lgrc-epoch-invp-stops-any
   (implies (fn-lgrc-epoch-invp s ack cm est j k genesis max ack0)
            (fn-lgrc-epoch-invp s ack cm nil j k genesis max ack0))))
(local
 (defthm fn-lgrc-epoch-other-any
   (implies (and (fn-lgrc-epoch-invp s ack cm est j k genesis max ack0)
                 (fn-lgrc-op-okp s e j k ack)
                 (or (not est) (fn-lgrc-served-op-okp s e j k cm)))
            (and (fn-lgrc-invp (mv-nth 1 (fn-bsc-step s e)) j k ack)
                 (fn-lgrc-epoch-invp (mv-nth 1 (fn-bsc-step s e)) ack cm nil j k genesis max ack0)
                 (implies (and est (not (and (consp e) (member-equal (car e) '(:exit :lose-cache)))))
                          (fn-lgrc-epoch-invp (mv-nth 1 (fn-bsc-step s e)) ack cm t j k genesis max ack0))))
   :hints (("Goal" :in-theory (disable fn-lgrc-epoch-invp fn-lgrc-epoch-other fn-bsc-step fn-lgrc-invp
                                       fn-lgrc-op-okp fn-lgrc-served-op-okp fn-lgrc-epoch-other-running
                                       fn-lgrc-epoch-other-stopped)
            :cases (est)
            :use ((:instance fn-lgrc-epoch-other-running)
                  (:instance fn-lgrc-epoch-other-stopped)
                  (:instance fn-lgrc-epoch-invp-of-a-running-service)
                  (:instance fn-lgrc-epoch-invp-stops-any))))))
(local
 (defthm fn-lgrc-epoch-commit-step-pairs
   (implies (and (fn-lgrc-epoch-invp s ack cm t j k genesis max ack0)
                 (true-listp b) (consp b)
                 (fn-lgrc-completep (append cm b) genesis (fn-bs-unit (fn-bsc-bs s)) max)
                 (fn-lgrc-outcomep wout) (fn-lgrc-outcomep fout))
            (fn-lgrc-all-pairs-invp (fn-lgrc-pair-each (car (fn-lgrc-commit s cm b wout fout j k)) ack)
                                    j k ack0))
   :hints (("Goal" :in-theory (disable fn-lgrc-epoch-commit-step fn-lgrc-commit fn-lgrc-epoch-invp
                                       fn-lgrc-completep fn-lgrc-outcomep)
            :use ((:instance fn-lgrc-epoch-commit-step))))))
(local
 (defthm fn-lgrc-epochs-keep-the-epoch-invariant
   (implies (and (booleanp est)
                 (fn-lgrc-epoch-invp s ack cm est j k genesis max ack0)
                 (fn-lgrc-epochs-okp s ack cm est events j k genesis max floor))
            (fn-lgrc-all-pairs-invp (fn-lgrc-epochs s ack cm est events j k genesis max floor) j k ack0))
   :hints (("Goal" :induct (fn-lgrc-epochs s ack cm est events j k genesis max floor)
            :in-theory (disable fn-lgrc-epoch-invp fn-lgrc-attempt fn-bsc-step fn-lgrc-invp
                                fn-lgrc-holdsp fn-lgrc-open-servesp fn-lgrc-read-prefix
                                fn-lgrc-completep fn-lgrc-op-okp fn-lgrc-served-op-okp fn-lgrc-outcomep
                                fn-bsc-lookup fn-lgrc-epoch-open fn-lgrc-epoch-other fn-lgrc-epoch-other-running
                                fn-lgrc-epoch-other-stopped fn-lgrc-commit fn-lgrc-epoch-commit)))))

(local
 (defthm fn-lgrc-all-pairs-invp-member
   (implies (and (fn-lgrc-all-pairs-invp pairs j k ack0) (member-equal pair pairs))
            (and (fn-lgrc-invp (car pair) j k (cdr pair))
                 (fn-lgrc-holdsp (cdr pair) ack0)))
   :hints (("Goal" :in-theory (disable fn-lgrc-invp fn-lgrc-holdsp)))))

(local
 (defthm fn-lgrc-every-image-holds-the-prefix
   (implies (fn-lgrc-invp s j k a)
            (let ((image (fn-bs-crash (fn-bsc-bs s) choices)))
              (and (fn-bs-inop (fn-bs-durable-entry image j k))
                   (fn-lgrc-holdsp (fn-bs-durable-content image (fn-bs-durable-entry image j k)) a))))
   :hints (("Goal" :in-theory (e/d (fn-lgrc-holdsp)
                                   (fn-lgrc-invp fn-bs-crash fn-bs-durable-entry fn-bs-durable-content))
            :use ((:instance fn-lgrc-every-image-binds-the-acknowledged-prefix))))))
; KEYSTONE (K3, M1 across restarts).  From an open's start -- a store whose
; durable and visible journal/K bindings hold the acknowledged octets ACK0
; (any crash image, or any state K2 reaches) -- through any number of
; epochs: opens (attempts, failing anywhere or succeeding), the service's
; fenced appends and acknowledgements, failed barriers, exits with the
; cache kept, cache losses and anyone else's steps: at every state, in
; every crash image, the inode journal/K DURABLY names holds the octets
; acknowledged at that state, those octets extend ACK0, and the open's scan
; reads ACK0's records first.  ACK0 is arbitrary, so every record
; acknowledged in any epoch survives every later one.
(defthm fn-lgrc-acknowledged-records-survive-restarts
  (implies (and (fn-lgrc-invp s j k ack0)
                (fn-lgrc-completep ack0 genesis (fn-bs-unit (fn-bsc-bs s)) max)
                (fn-lgrc-epochs-okp s ack0 cm nil events j k genesis max floor)
                (member-equal pair (fn-lgrc-epochs s ack0 cm nil events j k genesis max floor))
                (fn-bs-crash-imagep (fn-bsc-bs (car pair)) image))
           (let* ((i (fn-bs-durable-entry image j k))
                  (c (fn-bs-durable-content image i))
                  (unit (fn-bs-unit (fn-bsc-bs s)))
                  (acked0 (car (fn-lg-scan ack0 genesis unit max))))
             (and (fn-bs-inop i)
                  (fn-lgrc-holdsp c (cdr pair))
                  (fn-lgrc-holdsp (cdr pair) ack0)
                  (fn-lgrc-holdsp c ack0)
                  (equal (take (len acked0) (car (fn-lg-scan c genesis unit max))) acked0))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-crash-imagep)
                           (fn-lgrc-invp fn-lgrc-completep fn-lgrc-epochs fn-lgrc-epochs-okp fn-lgrc-holdsp
                            fn-bs-crash fn-bs-durable-entry fn-bs-durable-content fn-lg-scan fn-bs-take
                            fn-lgrc-every-image-holds-the-prefix fn-lgrc-epoch-invp
                            fn-lgrc-epochs-keep-the-epoch-invariant fn-lgrc-all-pairs-invp-member))
           :use ((:instance fn-lgrc-epochs-keep-the-epoch-invariant (ack ack0) (est nil))
                 (:instance fn-lgrc-all-pairs-invp-member
                            (pairs (fn-lgrc-epochs s ack0 cm nil events j k genesis max floor)))
                 (:instance fn-lgrc-every-image-holds-the-prefix
                            (s (car pair)) (a (cdr pair))
                            (choices (fn-bs-crash-imagep-witness (fn-bsc-bs (car pair)) image)))
                 (:instance fn-lgrc-scan-of-a-read-holding-a-complete-prefix
                            (a ack0) (unit (fn-bs-unit (fn-bsc-bs s)))
                            (o (fn-bs-durable-content image (fn-bs-durable-entry image j k))))
                 (:instance fn-lgrc-epoch-invp (est nil) (ack ack0))))))

; -----------------------------------------------------------------------------
; 9. The open, composed: the copy, then the rest of the open, then the
; served run.

(local
 (defthm fn-lgrc-final-of-the-attempt-keeps-the-unit
   (equal (fn-bs-unit (fn-bsc-bs (fn-lgrc-final (fn-lgrc-attempt s j k stg stage genesis max floor outs) s)))
          (fn-bs-unit (fn-bsc-bs s)))
   :hints (("Goal" :in-theory (e/d (fn-lgrc-final) (fn-lgrc-attempt))
            :cases ((consp (fn-lgrc-attempt s j k stg stage genesis max floor outs)))))))

; KEYSTONE (P10, the served open at every cut).  From a quiet store, the copy
; (P-LOG-RECOVER-COPY, all six syscalls :ok) leaves a store R-related to the
; kernel of what the open read, and every state of the rest of the open
; (fn-lg-open-program: recover-replayed and the three recovery barriers,
; each with its cut) is related.  The copy's own cuts, under any outcomes
; and any number of interrupted attempts, are K2 (fn-lgrc-attempt-keeps-the-
; invariant, fn-lgrc-world-keeps-the-invariant).
(defthm fn-lgrc-open-keeps-the-relation-at-every-cut
  (let* ((bs (fn-bsc-bs s))
         (o (fn-bsc-content s (fn-bsc-lookup s j k)))
         (ks (fn-lgt-recover o genesis (fn-bs-unit bs) max floor))
         (ino (fn-bs-next-ino bs))
         (final (fn-bsc-bs (fn-lgrc-final (fn-lgrc-attempt s j k stg stage genesis max floor nil) s))))
    (implies (and (natp ino) (fn-bs-dir-idp j) (fn-bs-namep k)
                  (fn-bs-dir-idp stg) (fn-bs-namep stage)
                  (not (and (equal stg j) (equal stage k)))
                  (not (fn-bsc-lookup s stg stage))
                  (null (fn-bs-pending bs))
                  (posp (fn-bs-unit bs)) (true-listp o) (consp o)
                  (equal (mod (len o) (fn-bs-unit bs)) 0)
                  (fn-frame-digestp genesis))
             (and (fn-lgk-relp final ks ino genesis max)
                  (fn-lg-all-relp (fn-lg-run final ks (fn-lg-open-program) nil ino) ino genesis max))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '() (theory 'minimal-theory))
           :use ((:instance fn-lgrc-attempt-makes-the-read-prefix-durable)
                 (:instance fn-lg-open-program-keeps-the-relation
                            (bs (fn-bsc-bs (fn-lgrc-final (fn-lgrc-attempt s j k stg stage genesis max floor nil) s)))
                            (ks (fn-lgt-recover (fn-bsc-content s (fn-bsc-lookup s j k)) genesis
                                                (fn-bs-unit (fn-bsc-bs s)) max floor))
                            (ino (fn-bs-next-ino (fn-bsc-bs s))))))))

(local
 (defthm fn-lgrc-relp-of-an-equal-read
   (implies (and (equal a b) (fn-lgk-relp bs (fn-lgt-recover a genesis unit max floor) ino genesis max))
            (fn-lgk-relp bs (fn-lgt-recover b genesis unit max floor) ino genesis max))
   :rule-classes nil))

; KEYSTONE (M1 from the open).  From a quiet store: the copy, then the served
; run over the inode it published (whatever the host's operations), then
; the COMPLETE's acknowledgements (fn-lgu-acknowledge, the host's one call).
; STR is what the open read, as the host holds it (fn-lgc-open's input).
; The count the host holds is the run's; every crash image of the store the
; run leaves recovers that many records first; and so does every crash
; image of every cut of the run.  No hypothesis relates the read to the
; durable content before the open: the read may hold a failed barrier's
; clean pages (RL-01).
(defthm fn-lgrc-acknowledge-from-the-copy
  (let* ((bs0 (fn-bsc-bs s))
         (unit (fn-bs-unit bs0))
         (o (fn-bsc-content s (fn-bsc-lookup s j k)))
         (ino (fn-bs-next-ino bs0))
         (bs (fn-bsc-bs (fn-lgrc-final (fn-lgrc-attempt s j k stg stage genesis max floor nil) s)))
         (ks0 (fn-lgt-recover (fn-lgd-octets str) genesis unit max floor))
         (run (fn-lgu-host-run bs ks0 (append ops (fn-lgu-finishes n)) ino max))
         (final (fn-lgu-host-final bs ks0 (append ops (fn-lgu-finishes n)) ino max))
         (host (fn-lgu-acknowledge
                (fn-lgc-host-run (mv-nth 1 (fn-lgc-open str genesis unit max floor))
                                 (fn-lgu-host-kops bs ks0 ops ino max))
                n)))
    (implies (and (natp ino) (fn-bs-dir-idp j) (fn-bs-namep k)
                  (fn-bs-dir-idp stg) (fn-bs-namep stage)
                  (not (and (equal stg j) (equal stage k)))
                  (not (fn-bsc-lookup s stg stage))
                  (null (fn-bs-pending bs0))
                  (posp unit) (true-listp o) (consp o) (equal (mod (len o) unit) 0)
                  (fn-frame-digestp genesis)
                  (equal o (fn-lgd-octets str)))
             (and (equal (fn-lgc-acked host) (fn-lgk-acked (cdr final)))
                  (implies (fn-bs-crash-imagep (car final) image)
                           (let ((a (fn-lgc-acked host))
                                 (recovered (fn-lgk-committed
                                             (fn-lgk-recover (fn-bs-durable-content image ino)
                                                             genesis (fn-bs-unit (car final)) max
                                                             next-txid))))
                             (and (<= a (len recovered))
                                  (equal (take a recovered) (take a (fn-lgk-committed (cdr final)))))))
                  (implies (and (member-equal pair run)
                                (fn-bs-crash-imagep (car pair) image))
                           (let ((a (fn-lgk-acked (cdr pair)))
                                 (recovered (fn-lgk-committed
                                             (fn-lgk-recover (fn-bs-durable-content image ino)
                                                             genesis (fn-bs-unit (car pair)) max
                                                             next-txid))))
                             (and (<= a (len recovered))
                                  (equal (take a recovered) (take a (fn-lgk-committed (cdr pair))))))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-lgrc-final-of-the-attempt-keeps-the-unit)
                                      (theory 'minimal-theory))
           :use ((:instance fn-lgrc-attempt-makes-the-read-prefix-durable)
                 (:instance fn-lgrc-relp-of-an-equal-read
                            (a (fn-bsc-content s (fn-bsc-lookup s j k)))
                            (b (fn-lgd-octets str))
                            (bs (fn-bsc-bs (fn-lgrc-final (fn-lgrc-attempt s j k stg stage genesis max floor nil) s)))
                            (unit (fn-bs-unit (fn-bsc-bs s)))
                            (ino (fn-bs-next-ino (fn-bsc-bs s))))
                 (:instance fn-lgu-acknowledge-acknowledges-only-recoverable-records
                            (bs (fn-bsc-bs (fn-lgrc-final (fn-lgrc-attempt s j k stg stage genesis max floor nil) s)))
                            (s str)
                            (ino (fn-bs-next-ino (fn-bsc-bs s))))))))

; -----------------------------------------------------------------------------
; 10. The open never drops (RL-01-CHECKPOINT-NAME-BEFORE-DROP; coordinator
; ruling 2026-10-05, on lane m1-durable-4's finding).
;
; THE DEFECT.  The open used to finish an interrupted drop: after its
; barriers it unlinked every segment below the first suffix segment of the
; checkpoint it READ (fn-lgs-open-plan's DROP) and fenced journal/.  That
; checkpoint's name may be visible only.  A run renames the checkpoint into
; the root and the root's fsync fails: the rename leaves pending, the cache
; keeps the name, the process exits.  The restart reads the name and plans
; the drop; its own root fence succeeds and lands nothing (nothing for the
; root is pending); the unlink and journal/'s fence land; a power loss then
; leaves neither the checkpoint nor the segments it covers
; (fn-lgrc-dropping-open-loses-a-checkpointed-history, a ground trace).
;
; THE RULING.  The open unlinks no segment.  Covered segments stay until the
; next checkpoint install's drop, which runs only after that install's own
; root fence succeeded in the same run (host/native/io.lisp
; fnn-state-checkpoint-write raises before any drop on a failed fence) and
; which names every segment below its own first suffix segment, so it
; covers what an earlier drop left (books/store-log-segments.lisp
; fn-lgs-install-drop-covers-what-the-open-left).
;
; The open's byte steps (host/native/io.lisp fnn-recover-log): the copy
; (fn-lgrc-attempt-ops, the program fn-lgrc-program) and then the three
; recovery barriers (books/store-log-route-programs.lisp fn-lg-open-program:
; journal/, the root, the root's parent), each under the environment's
; outcome.  The staging sweep unlinks staging/ names only; the byte model
; here does not carry it.
(defun fn-lgrc-open-ops (s j k stg stage root parent genesis max floor outs)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-lgrc-attempt-ops s j k stg stage genesis max floor outs)
          (list (list :fsync-dir j (fn-lgrc-out outs 6))
                (list :fsync-dir root (fn-lgrc-out outs 7))
                (list :fsync-dir parent (fn-lgrc-out outs 8)))))

(defun fn-lgrc-dir-fences-p (ops)
  (declare (xargs :guard t))
  (if (consp ops)
      (and (consp (car ops)) (equal (car (car ops)) :fsync-dir)
           (fn-lgrc-dir-fences-p (cdr ops)))
    t))

(local
 (defthm fn-lgrc-run-okp-of-dir-fences
   (implies (fn-lgrc-dir-fences-p ops)
            (fn-lgrc-run-okp s ops j n a))
   :hints (("Goal" :induct (fn-lgrc-run-okp s ops j n a)))))

(local
 (defthm fn-lgrc-run-okp-of-append-dir-fences
   (implies (and (fn-lgrc-run-okp s x j n a) (fn-lgrc-dir-fences-p y))
            (fn-lgrc-run-okp s (append x y) j n a))
   :hints (("Goal" :induct (fn-lgrc-run-okp s x j n a)))))

(local
 (defthm fn-lgrc-completep-of-nil
   (fn-lgrc-completep nil genesis unit max)
   :hints (("Goal" :in-theory (enable fn-lg-scan)))))

; KEYSTONE (RL-01-CHECKPOINT-NAME-BEFORE-DROP, the open's half).  A name N
; of journal/ that every crash image binds to an inode, and that the cache
; binds (the invariant over the empty prefix), stays so at every state of
; the open -- the copy of segment K (N = K included) and the three barriers,
; under any outcomes the environment chooses.  The open unlinks no segment.
(defthm fn-lgrc-open-unlinks-no-segment
  (implies (and (fn-lgrc-invp s j n nil)
                (fn-bs-dir-idp stg) (fn-bs-namep stage)
                (not (and (equal stg j) (equal stage k)))
                (not (and (equal stg j) (equal stage n)))
                (fn-lgrc-outcomesp outs))
           (fn-lgrc-all-invp
            (fn-bsc-run s (fn-lgrc-open-ops s j k stg stage root parent genesis max floor outs))
            j n nil))
  :hints (("Goal" :do-not-induct t
           :cases ((equal n k))
           :in-theory (e/d (fn-lgrc-open-ops)
                           (fn-lgrc-invp fn-lgrc-completep fn-lgrc-out fn-bsc-run
                            fn-lgrc-copy-octets fn-lgt-recover fn-lgk-frontier
                            fn-bsc-content))
           :use ((:instance fn-lgrc-attempt-is-within-the-side-conditions (k n) (a nil))
                 (:instance fn-lgrc-run-keeps-the-invariant (k n) (a nil)
                            (ops (fn-lgrc-open-ops s j k stg stage root parent genesis max
                                                   floor outs)))))))

; KEYSTONE (discoverable).  At every state of the open, in every image a
; power loss can leave, journal/N durably names an inode, and the open's own
; listing still sees N.
(defthm fn-lgrc-open-keeps-every-segment-name-in-every-image
  (implies (and (fn-lgrc-invp s j n nil)
                (fn-bs-dir-idp stg) (fn-bs-namep stage)
                (not (and (equal stg j) (equal stage k)))
                (not (and (equal stg j) (equal stage n)))
                (fn-lgrc-outcomesp outs)
                (member-equal x (fn-bsc-run s (fn-lgrc-open-ops s j k stg stage root parent
                                                                genesis max floor outs))))
           (and (fn-bs-inop (fn-bs-durable-entry (fn-bs-crash (fn-bsc-bs x) choices) j n))
                (fn-bs-inop (fn-bsc-lookup x j n))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgrc-goodp) (fn-lgrc-open-ops fn-bsc-run fn-bs-crash
                                            fn-bs-durable-entry fn-lgrc-all-invp
                                            fn-lgrc-every-image-binds-the-acknowledged-prefix))
           :use ((:instance fn-lgrc-open-unlinks-no-segment)
                 (:instance fn-lgrc-all-invp-member (k n) (a nil)
                            (states (fn-bsc-run s (fn-lgrc-open-ops s j k stg stage root parent
                                                                    genesis max floor outs))))
                 (:instance fn-lgrc-every-image-binds-the-acknowledged-prefix
                            (s x) (k n) (a nil))))))

; THE DEFECT, ground (the trace above).  Segment 1 holds the history
; (1 1 1 1), segment 2 is the active one; a state checkpoint (inode 5)
; covering segment 1 is staged and fenced.  The install renames it into the
; root, the root's fence fails (EIO, nothing landed), the process exits with
; the cache kept.  The restarted open reads the checkpoint's name, runs the
; copy of segment 2 and the three barriers -- every step succeeds -- then
; the old drop: unlink journal/000001.log, fence journal/.  Nothing is
; pending afterwards, so every image a power loss leaves is the durable
; tables: no checkpoint and no segment 1.  The A2 open alone (the keystone's
; premise holds at the restart: fn-lgrc-invp over journal/000001.log)
; keeps segment 1 in every image.
(defun fn-lgrc-rl01-checkpointed-store ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-bsc-of (fn-bs-make 4 '((1 . (1 1 1 1)) (2 . (0 0 0 0)) (5 . (9 9 9 9)))
                         '((:root ("journal" . :journal) ("staging" . :staging))
                           (:journal ("000001.log" . 1) ("000002.log" . 2))
                           (:staging (".checkpoint-stage" . 5)))
                         nil 6)))

(defun fn-lgrc-rl01-restarted-store ()
  (declare (xargs :guard t :verify-guards nil))
  (car (last (fn-bsc-run (fn-lgrc-rl01-checkpointed-store)
                         '((:rename :staging ".checkpoint-stage" :root "checkpoint" :ok)
                           (:fsync-dir :root (:eio))
                           (:exit))))))

(defun fn-lgrc-rl01-open-ops (drop)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-lgrc-open-ops (fn-lgrc-rl01-restarted-store) :journal "000002.log"
                            :staging ".stage-recover-000002" :root :parent
                            (fn-bs-zeros 32) 4096 0 nil)
          (if drop
              '((:unlink :journal "000001.log" :ok) (:fsync-dir :journal :ok))
            nil)))

(defthm fn-lgrc-dropping-open-loses-a-checkpointed-history
  (let* ((s1 (fn-lgrc-rl01-restarted-store))
         (run (fn-bsc-run s1 (fn-lgrc-rl01-open-ops t)))
         (bs (fn-bsc-bs (car (last run))))
         (image (fn-bs-crash bs choices)))
    (and (equal (fn-bsc-lookup s1 :root "checkpoint") 5)
         (null (fn-bs-durable-entry (fn-bsc-bs s1) :root "checkpoint"))
         (fn-lgrc-invp s1 :journal "000001.log" nil)
         (equal (len run) (len (fn-lgrc-rl01-open-ops t)))
         (null (fn-bs-pending bs))
         (null (fn-bs-durable-entry image :root "checkpoint"))
         (null (fn-bs-durable-entry image :journal "000001.log"))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bsc-step fn-bsc-lookup fn-bsc-bs fn-lgrc-goodp
                                     fn-lgrc-candidates fn-bs-crash))))
