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
; Assumptions: none new.  A-CRASH-IMAGE's tear model and A-DURABILITY are
; the byte model's; A-WRITE-ISOLATION's cross-inode reading
; (specs/failures.md) is what lets the old inode's blocks survive its unlink.
(in-package "ACL2")
(include-book "store-log-durable")

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
; the old ones (writes, file fences, creates, evictions), one of the old
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
                                         :evict-ino :evict-dir :lose-cache)))
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
                   (equal (car op) :create) (equal (car op) :rename) (equal (car op) :evict-ino)
                   (equal (car op) :evict-dir) (equal (car op) :lose-cache)))
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
; Every step keeps the invariant under its side condition.
(defthm fn-lgrc-step-keeps-the-invariant
  (implies (and (fn-lgrc-invp s j k a) (fn-lgrc-op-okp s op j k a))
           (fn-lgrc-invp (mv-nth 1 (fn-bsc-step s op)) j k a))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lgrc-invp fn-lgrc-op-okp)
           :cases ((member-equal (car op) '(:write :fsync-file :create :evict-ino))
                   (equal (car op) :fsync-dir) (equal (car op) :lose-cache)
                   (equal (car op) :evict-dir) (equal (car op) :rename)))))

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

; The program's shape for the host and its cut map (native_cuts LOG_CUTS):
; the cut after each step the host names.
(defun fn-lgrc-program ()
  (declare (xargs :guard t))
  '((:create :staging :stage-recover)
    (:write :staged 0 :validated-prefix)
    (:cut "log-copied")
    (:fsync-file :staged)
    (:cut "log-copy-fenced")
    (:rename :staging :stage-recover :journal :segment)
    (:cut "log-swapped")
    (:fsync-dir :journal)
    (:fsync-dir :staging)
    (:cut "log-recovered")))

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

