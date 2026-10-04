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

; Inode I holds A at offset 0 durably and visibly, and every pending write to
; it starts at or above (len A).  I is below the next inode number, so no
; create returns it.
(defun fn-lgrc-goodp (s i a)
  (declare (xargs :guard t :verify-guards nil))
  (let ((bs (fn-bsc-bs s)) (fa (len a)))
    (and (fn-bs-inop i)
         (< i (nfix (fn-bs-next-ino bs)))
         (<= fa (len (fn-bs-durable-content bs i)))
         (equal (fn-bs-take fa (fn-bs-durable-content bs i)) a)
         (<= fa (len (fn-bsc-content s i)))
         (equal (fn-bs-take fa (fn-bsc-content s i)) a)
         (fn-lgu-writes-at-or-above (fn-bs-pending bs) i fa))))

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
