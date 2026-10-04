; The record log's acknowledged records are recovered at every crash point of
; the run the host serves (lane m1-durable, 2026-10-04: Mini's M1; the
; restatement of PRF-936, lane byte-model, over the log kernel's own
; acknowledgement instead of the owner-batch layer no host line calls).
;
; The sentence: every record the node's log kernel has acknowledged (the
; first ACKED of its committed records; the count fnn-log-ack advances by
; fn-lgc-finish-one in the COMPLETE, before the batch's replies leave) is
; among the first records the next open recovers (fn-lgk-recover of the
; segment's durable content: fn-lg-scan), from every admissible crash image
; (fn-bs-crash-imagep: each pending write lands as any per-unit tear, or not
; at all; a failed barrier lands the environment's selection and discards
; the rest) of every cut state of the host's run of the active segment: the
; open (P-LOG-RECOVER) and then any sequence of the host's operations on the
; record log (section 3: take, prepare, reserve, the seal's capture,
; extension and write, the barrier and fence, the acknowledgements, and the
; fence-failed of every OS error), under any outcomes the environment
; chooses.  Scope: one segment, no rotation (fnn-log-rotate is not an
; operation of the run).
;
; No trailer assumption.  A record the kernel holds committed lies below
; the frontier, and every pending write of the segment starts at or above
; it (fn-lgu-safep, section 2): a crash keeps the prefix
; (fn-lgu-crash-keeps-the-prefix) and the scan reads the prefix's complete
; chained entries before whatever the tear left (fn-lg-scan-of-complete-
; append).  A-CRYPTO-TRAILER decides only what the scan reads after them.
;
; The theorems:
; section 2  fn-lgu-safe-image-recovers-the-acknowledged-records, from the
;     prefix lemmas over the byte model (fn-bs-apply-ops, fn-bs-crash-select);
;   section 3  the host's operations (fn-lgu-host-step, fn-lgu-host-run) and
;     the invariant: R (fn-lgk-relp), or a faulted kernel over a safe store
;     (fn-lgu-invp), kept by every operation (fn-lgu-host-run-is-safe);
;   section 4  fn-lgu-acknowledged-records-are-recovered-at-every-cut (a lemma
;     since 2026-10-04: the host-entry keystone of section 8 states M1);
;   section 5  fn-lgu-open-run-acknowledges-only-recoverable-records: from
;     the open, P-LOG-RECOVER's cuts under any outcomes, then the run;
;   section 6 fn-lgu-host-kernel-acknowledges-only-recoverable-records: the
;     count the host holds (fn-lgc-acked of the concrete kernel from
;     fn-lgc-open, PRF-282) is the one the keystone speaks of;
;   section 7 fn-lgu-complete-acknowledges-the-fenced-batch: the COMPLETE's
;     acknowledgements are the fenced batch's records, in order.
;   section 8 KEYSTONE fn-lgu-acknowledge-acknowledges-only-recoverable-
;     records: M1 at the host's entry (fnn-log-finish calls fn-lgu-acknowledge):
;     the host's count is the run's, recovered from every crash image, and
;     every cut of the run recovers its acknowledged records.
;
; Teeth: tests/acl2/store-log-durable-tests.lisp (a ground log recovered,
; a record taken, sealed, fenced and acknowledged, every cut under explicit
; crash choices; one witness per removed hypothesis, and the fence-only-in-
; flight rule's).

(in-package "ACL2")
(include-book "store-log-kernel-concrete")
(include-book "store-log-programs")
(include-book "store-log-extend")
(include-book "byte-store-invariants")

; -----------------------------------------------------------------------------
; 1. The open holds what the scan reads; the store's unit through its steps.

(defthm fn-lgu-recovered-kernel-holds-the-scan
  (equal (fn-lgk-committed (fn-lgk-recover c genesis unit max next-txid))
         (car (fn-lg-scan c genesis unit max)))
  :hints (("Goal" :in-theory (e/d (fn-lgk-recover)
                                  (fn-lg-scan fn-lg-scan-last fn-lgk-make fn-lgk-committed)))))


(local
 (defthm fn-lgu-unit-of-write
   (equal (fn-bs-unit (mv-nth 1 (fn-bs-write s ino offset octets outcome))) (fn-bs-unit s))
   :hints (("Goal" :in-theory (enable fn-bs-write)))))

(local
 (defthm fn-lgu-unit-of-fsync-file
   (equal (fn-bs-unit (mv-nth 1 (fn-bs-fsync-file s ino outcome))) (fn-bs-unit s))
   :hints (("Goal" :in-theory (enable fn-bs-fsync-file fn-bs-fence-file)))))

(local
 (defthm fn-lgu-unit-of-crash
   (equal (fn-bs-unit (fn-bs-crash s choices)) (fn-bs-unit s))
   :hints (("Goal" :in-theory (enable fn-bs-crash)))))


; The host's kernel at open is this kernel with the txid floor's next txid
; (books/store-log-programs.lisp fn-lg-recovered-kernel, fn-lgt-recover).
(defthm fn-lgu-recovered-kernel-is-the-recover-by-definition
  (equal (fn-lg-recovered-kernel bs ino genesis max floor)
         (fn-lgk-recover (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max
                         (fn-lgt-next-after (car (fn-lg-scan (fn-bs-durable-content bs ino)
                                                             genesis (fn-bs-unit bs) max))
                                            floor)))
  :hints (("Goal" :in-theory (e/d (fn-lg-recovered-kernel fn-lgt-recover)
                                  (fn-lg-scan fn-lgk-recover fn-lgt-next-after)))))


; -----------------------------------------------------------------------------
; 2. A committed prefix nothing pending writes below survives every crash.
;
; The failure paths of the host (a write that fails part way, a barrier
; that fails after landing a selection) leave stores no program theorem
; relates to the kernel; what they keep is weaker than R and is all the
; acknowledgement needs: the durable content's first FRONTIER octets still
; scan completely to COMMITTED, and every pending write of the segment
; starts at or above FRONTIER.  fn-lgu-safep is that; every crash image of
; such a store scans to COMMITTED first (fn-lgu-safe-image-scans-the-
; committed-records-first), whatever the tear, with no trailer assumption.

; Every pending write of the segment INO starts at or above F.
(defun fn-lgu-writes-at-or-above (ops ino f)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom ops)
      t
    (and (or (not (consp (car ops)))
             (not (equal (car (car ops)) :write))
             (not (equal (nth 1 (car ops)) ino))
             (<= (nfix f) (nfix (nth 2 (car ops)))))
         (fn-lgu-writes-at-or-above (cdr ops) ino f))))

(defun fn-lgu-safep (bs ks ino genesis max)
  (declare (xargs :guard t :verify-guards nil))
  (let ((c (fn-bs-durable-content bs ino)) (f (fn-lgk-frontier ks)))
    (and ino
         (<= f (len c))
         (equal (fn-lg-scan (fn-bs-take f c) genesis (fn-bs-unit bs) max)
                (cons (fn-lgk-committed ks) f))
         (fn-lgu-writes-at-or-above (fn-bs-pending bs) ino f)
         (true-listp (fn-lgk-committed ks))
         (<= (fn-lgk-acked ks) (len (fn-lgk-committed ks))))))

(local
 (defthm fn-lgu-assoc-put-assoc-same
   (implies ino (equal (assoc-equal ino (fn-bs-put-assoc ino v a)) (cons ino v)))))
(local
 (defthm fn-lgu-assoc-put-assoc-other
   (implies (and ino (not (equal k ino)))
            (equal (assoc-equal ino (fn-bs-put-assoc k v a)) (assoc-equal ino a)))))
(local
 (defthm fn-lgu-len-take (equal (len (fn-bs-take n x)) (nfix n))))
(local
 (defthm fn-lgu-take-of-append-short
   (implies (and (natp f) (<= f (len a)))
            (equal (fn-bs-take f (append a b)) (fn-bs-take f a)))))
(local
 (defthm fn-lgu-splice-keeps-the-prefix
   (implies (and (natp f) (<= f (nfix off)))
            (and (equal (fn-bs-take f (fn-bs-splice old off oct)) (fn-bs-take f old))
                 (<= f (len (fn-bs-splice old off oct)))))
   :hints (("Goal" :in-theory (e/d (fn-bs-splice) (fn-bs-take))))))
(local
 (defthm fn-lgu-apply-op-content
   (implies ino
            (equal (cdr (assoc-equal ino (car (fn-bs-apply-op inodes dirs op))))
                   (if (and (equal (car op) :write) (equal (nth 1 op) ino))
                       (fn-bs-splice (cdr (assoc-equal ino inodes)) (nth 2 op) (nth 3 op))
                     (cdr (assoc-equal ino inodes)))))
   :hints (("Goal" :cases ((equal (nth 1 op) ino))
            :in-theory (e/d (fn-bs-apply-op) (fn-bs-take fn-bs-splice fn-bs-put-assoc fn-bs-del-assoc))))))
(local
 (defthm fn-lgu-apply-ops-keeps-the-prefix
   (implies (and ino (natp f) (fn-lgu-writes-at-or-above ops ino f))
            (let ((c2 (cdr (assoc-equal ino (mv-nth 0 (fn-bs-apply-ops inodes dirs ops)))))
                  (c (cdr (assoc-equal ino inodes))))
              (and (equal (fn-bs-take f c2) (fn-bs-take f c))
                   (implies (<= f (len c)) (<= f (len c2))))))
   :hints (("Goal" :induct (fn-bs-apply-ops inodes dirs ops)
            :in-theory (e/d () (fn-bs-apply-op fn-bs-take fn-bs-splice fn-bs-put-assoc fn-bs-del-assoc))))))
(defthm fn-lgu-writes-at-or-above-of-append
  (equal (fn-lgu-writes-at-or-above (append a b) ino f)
         (and (fn-lgu-writes-at-or-above a ino f) (fn-lgu-writes-at-or-above b ino f))))
(local
 (defthm fn-lgu-max-at-or-above-linear
   (implies (and (natp o) (integerp y)) (<= o (nfix (max o y))))
   :rule-classes :linear))
(local
 (defthm fn-lgu-tear-write-at-or-above
   (implies (or (not (equal (nth 1 op) ino)) (<= (nfix f) (nfix (nth 2 op))))
            (fn-lgu-writes-at-or-above (fn-bs-tear-write op sels i unit) ino f))
   :hints (("Goal" :induct (fn-bs-tear-write op sels i unit)
            :expand ((fn-bs-tear-write op sels i unit))
            :do-not '(generalize fertilize)
            :in-theory (e/d (fn-lgu-max-at-or-above-linear)
                            (fn-bs-take fn-bs-zeros fn-bs-unit-count max nfix floor))))))
(defthm fn-lgu-crash-select-writes-at-or-above
  (implies (fn-lgu-writes-at-or-above ops ino f)
           (fn-lgu-writes-at-or-above (fn-bs-crash-select ops choices unit) ino f))
  :hints (("Goal" :induct (fn-bs-crash-select ops choices unit)
           :in-theory (disable fn-bs-tear-write))
          ("Subgoal *1/1" :use ((:instance fn-lgu-tear-write-at-or-above
                                           (op (car ops)) (sels (car choices)) (i 0))))))
(defthm fn-lgu-ops-for-ino-writes-at-or-above
  (implies (fn-lgu-writes-at-or-above ops ino f)
           (and (fn-lgu-writes-at-or-above (fn-bs-ops-for-ino ops j) ino f)
                (fn-lgu-writes-at-or-above (fn-bs-ops-not-for-ino ops j) ino f))))
(local
 (defthm fn-lgu-take-then-nthcdr-any
   (implies (and (natp n) (<= n (len x)))
            (equal (append (fn-bs-take n x) (nthcdr n x)) x))))
(defthm fn-lgu-crash-with-choices-keeps-the-prefix
  (implies (and ino (natp f) (fn-lgu-writes-at-or-above (fn-bs-pending s) ino f)
                (<= f (len (fn-bs-durable-content s ino))))
           (let ((c2 (fn-bs-durable-content (fn-bs-crash s choices) ino)))
             (and (equal (fn-bs-take f c2) (fn-bs-take f (fn-bs-durable-content s ino)))
                  (<= f (len c2)))))
  :hints (("Goal" :in-theory (e/d (fn-bs-crash fn-bs-durable-content)
                                  (fn-bs-take fn-bs-apply-ops fn-bs-crash-select
                                   fn-lgu-apply-ops-keeps-the-prefix))
           :use ((:instance fn-lgu-apply-ops-keeps-the-prefix
                            (inodes (fn-bs-inodes s)) (dirs (fn-bs-dirs s))
                            (ops (fn-bs-crash-select (fn-bs-pending s) choices (fn-bs-unit s))))))))
(defthm fn-lgu-crash-keeps-the-prefix
  (implies (and ino (natp f) (fn-lgu-writes-at-or-above (fn-bs-pending s) ino f)
                (<= f (len (fn-bs-durable-content s ino)))
                (fn-bs-crash-imagep s image))
           (let ((c2 (fn-bs-durable-content image ino)))
             (and (equal (fn-bs-take f c2) (fn-bs-take f (fn-bs-durable-content s ino)))
                  (<= f (len c2)))))
  :hints (("Goal" :in-theory (e/d (fn-bs-crash-imagep)
                                  (fn-bs-take fn-bs-crash fn-bs-durable-content)))))
(defthm fn-lgu-safe-image-scans-the-committed-records-first
  (implies (and (fn-lgu-safep bs ks ino genesis max) (fn-bs-crash-imagep bs image))
           (let* ((c (fn-bs-durable-content bs ino)) (c2 (fn-bs-durable-content image ino))
                  (f (fn-lgk-frontier ks)) (unit (fn-bs-unit bs)))
             (equal (car (fn-lg-scan c2 genesis unit max))
                    (append (fn-lgk-committed ks)
                            (car (fn-lg-scan (nthcdr f c2)
                                             (fn-lg-scan-last (fn-bs-take f c) genesis unit max)
                                             unit max))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgu-safep)
                           (fn-bs-take fn-lg-scan fn-lg-scan-last fn-bs-durable-content
                            fn-bs-crash-imagep fn-lgu-crash-keeps-the-prefix
                            fn-lgu-take-then-nthcdr-any fn-lg-scan-of-complete-append
                            fn-lgk-frontier fn-lgk-committed))
           :use ((:instance fn-lgu-crash-keeps-the-prefix (s bs) (f (fn-lgk-frontier ks)))
                 (:instance fn-lgu-take-then-nthcdr-any (n (fn-lgk-frontier ks))
                            (x (fn-bs-durable-content image ino)))
                 (:instance fn-lg-scan-of-complete-append
                            (d (fn-bs-take (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                            (x (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image ino)))
                            (prev genesis) (unit (fn-bs-unit bs)))))))
(defthm fn-lgu-safep-acked-within
  (implies (fn-lgu-safep bs ks ino genesis max)
           (and (<= (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
                (natp (fn-lgk-acked ks))))
  :rule-classes nil)
(local
 (defthm fn-lgu-take-of-append-within
   (implies (and (natp a) (<= a (len c)))
            (equal (take a (append c x)) (take a c)))))
(local
 (defthm fn-lgu-len-append
   (equal (len (append c x)) (+ (len c) (len x)))))
(defthm fn-lgu-safe-image-recovers-the-acknowledged-records
  (implies (and (fn-lgu-safep bs ks ino genesis max) (fn-bs-crash-imagep bs image))
           (let ((a (fn-lgk-acked ks))
                 (recovered (fn-lgk-committed
                             (fn-lgk-recover (fn-bs-durable-content image ino)
                                             genesis (fn-bs-unit bs) max next-txid))))
             (and (<= a (len recovered))
                  (equal (take a recovered) (take a (fn-lgk-committed ks))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgu-recovered-kernel-holds-the-scan)
                           (fn-lgu-safep fn-lg-scan fn-lg-scan-last fn-bs-take fn-lgk-recover
                            fn-bs-durable-content fn-bs-crash-imagep fn-lgk-committed fn-lgk-acked
                            fn-lgu-safe-image-scans-the-committed-records-first take))
           :use ((:instance fn-lgu-safe-image-scans-the-committed-records-first)
                 (:instance fn-lgu-safep-acked-within)))))
(defthm fn-lgu-related-state-is-safe
  (implies (fn-lgk-relp bs ks ino genesis max)
           (fn-lgu-safep bs ks ino genesis max))
  :hints (("Goal" :in-theory (e/d (fn-lgk-relp fn-lgk-content-okp)
                                  (fn-lg-scan fn-lg-scan-last fn-lg-log fn-bs-take fn-lg-zerosp
                                   fn-lg-recordsp fn-frame-digestp fn-bs-durable-content mod)))))
(defthm fn-lgu-safep-when-fields-agree
  (implies (and (fn-lgu-safep bs ks ino genesis max)
                (equal (fn-lgk-committed k2) (fn-lgk-committed ks))
                (equal (fn-lgk-frontier k2) (fn-lgk-frontier ks))
                (<= (fn-lgk-acked k2) (len (fn-lgk-committed ks))))
           (fn-lgu-safep bs k2 ino genesis max))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-lgu-safep)
                                  (fn-lg-scan fn-bs-take fn-bs-durable-content
                                   fn-lgk-committed fn-lgk-frontier fn-lgk-acked)))))
(local
 (defthm fn-lgu-write-parts
   (let ((s1 (mv-nth 1 (fn-bs-write bs ino off octets outcome))))
     (and (equal (fn-bs-durable-content s1 i) (fn-bs-durable-content bs i))
          (equal (fn-bs-unit s1) (fn-bs-unit bs))
          (implies (and (fn-lgu-writes-at-or-above (fn-bs-pending bs) ino f)
                        (<= (nfix f) (nfix off)))
                   (fn-lgu-writes-at-or-above (fn-bs-pending s1) ino f))))
   :hints (("Goal" :in-theory (e/d (fn-bs-write fn-bs-durable-content) (fn-bs-take))))))
(defthm fn-lgu-write-keeps-safe
  (implies (and (fn-lgu-safep bs ks ino genesis max)
                (<= (fn-lgk-frontier ks) (nfix off)))
           (fn-lgu-safep (mv-nth 1 (fn-bs-write bs ino off octets outcome)) ks ino genesis max))
  :hints (("Goal" :in-theory (e/d (fn-lgu-safep)
                                  (fn-bs-write fn-lg-scan fn-bs-take fn-lgk-frontier fn-lgk-committed
                                   fn-bs-durable-content fn-lgu-writes-at-or-above)))))
(defthm fn-lgu-fsync-keeps-safe
  (implies (fn-lgu-safep bs ks ino genesis max)
           (fn-lgu-safep (mv-nth 1 (fn-bs-fsync-file bs ino outcome)) ks ino genesis max))
  :hints (("Goal" :in-theory (e/d (fn-lgu-safep fn-bs-fsync-file fn-bs-fence-file fn-bs-durable-content)
                                  (fn-lg-scan fn-bs-take fn-lgk-frontier fn-lgk-committed
                                   fn-bs-apply-ops fn-bs-crash-select fn-bs-ops-for-ino
                                   fn-bs-ops-not-for-ino fn-lgu-apply-ops-keeps-the-prefix))
           :use ((:instance fn-lgu-apply-ops-keeps-the-prefix
                            (inodes (fn-bs-inodes bs)) (dirs (fn-bs-dirs bs)) (f (fn-lgk-frontier ks))
                            (ops (fn-bs-ops-for-ino (fn-bs-pending bs) ino)))
                 (:instance fn-lgu-apply-ops-keeps-the-prefix
                            (inodes (fn-bs-inodes bs)) (dirs (fn-bs-dirs bs)) (f (fn-lgk-frontier ks))
                            (ops (fn-bs-crash-select (fn-bs-ops-for-ino (fn-bs-pending bs) ino)
                                                     (cdr outcome) (fn-bs-unit bs))))))))
(defun fn-lgu-all-safep (pairs ino genesis max)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom pairs)
      t
    (and (consp (car pairs))
         (fn-lgu-safep (car (car pairs)) (cdr (car pairs)) ino genesis max)
         (fn-lgu-all-safep (cdr pairs) ino genesis max))))
(defthm fn-lgu-all-safep-of-append
  (equal (fn-lgu-all-safep (append a b) ino genesis max)
         (and (fn-lgu-all-safep a ino genesis max) (fn-lgu-all-safep b ino genesis max)))
  :hints (("Goal" :in-theory (disable fn-lgu-safep))))
(defthm fn-lgu-all-safep-member
  (implies (and (fn-lgu-all-safep pairs ino genesis max) (member-equal pair pairs))
           (fn-lgu-safep (car pair) (cdr pair) ino genesis max))
  :hints (("Goal" :in-theory (disable fn-lgu-safep))))

; -----------------------------------------------------------------------------
; 3. The host's run of the active segment, every cut of it.
;
; The operations, each one the host performs on the record log
; (host/native/io.lisp), in the kernel language of fn-lgk-host-step
; (books/store-log-kernel-concrete.lisp) where the operation is the
; kernel's alone, and with the byte effects of the programs where it
; writes:
;   (:prepare R) (:take R TXID COUNT OCTETS BMAX OMAX UNIT) (:consume-to T)
;   (:finish-one) (:fence-failed)
;       the kernel's alone (fnn-log-prepare, fnn-log-take, fnn-log-reserve,
;       fnn-log-finish under fnn-log-ack, and the fence-failed of every OS
;       error handler: fnn-log-commit-open-batch, fnn-log-sealed-effect,
;       fnn-log-sealed-abandon, fnn-log-sync-sealed-batch); no byte moves.
;   (:seal EXT-WRITE EXT-FENCE WRITE)
;       the batch's seal: the kernel takes the append against the sealed
;       extent (fnn-log-seal-capture -> fnn-log-append-capture,
;       fn-lgc-sealed-extent and fn-lgc-append; fnn-log-commit-open-batch
;       inline), then the extension when ACL2 decided one (fnn-log-ensure-
;       extent: fn-lg-extend-program's zeros at the old end, cut
;       log-extended, its barrier, cut log-extent-fenced), then the batch's
;       one positioned write at the frontier (fnn-log-append: fn-lg-append-
;       program's write, cut log-written).  An outcome other than :ok is
;       the environment's failure with the progress it made (fn-bs-write's
;       accepted octets, fn-bs-fsync-file's landed selection): the host's
;       handler fences the kernel (fn-lgk-fence-failed) and the batch job
;       stops (books/owner-queued-work.lisp: no phase after one that did not
;       return).  The kernel's capture precedes the extension on the seal
;       path and follows it inline; it changes no byte and the extension no
;       kernel field, so the cut states are the same stores, with COMMITTED
;       and ACKED the same in both kernels.
;   (:fence OUTCOME)
;       the barrier and the kernel's fence (fnn-log-fence, cut log-fenced):
;       fn-lgk-fence on :ok, fn-lgk-fence-failed otherwise.  The host
;       fences only the batch its seal put in flight: fnn-log-sync-sealed-
;       batch fences only while the sealed count is positive, which only
;       fnn-log-seal-capture sets after the kernel took the append, and
;       which fnn-log-sealed-abandon and the sync itself reset;
;       fnn-log-commit-open-batch fences only after its append returned.
;       So the kernel's phase is :appended at every host fence, and a fence
;       in another phase is no step of the host's (in particular none after
;       a failed barrier: fsyncgate, a later :ok fences nothing).
; Segment rotation (fnn-log-rotate, fn-lgs-rotate) is not an operation:
; the run is one segment's, from its open.  Every other operation is
; nothing.

;; THE TAKE'S VERDICT (lane m1-durable, repair M1-LOG-RECORD-FRAMING-WINDOW).
;; The log frames a record with the 32-octet chain before it, and the scan
;; opens a one-record entry with payload bound MAX (fn-lg-open-bound), so the
;; log holds a record only when 32 + its length is within MAX: fn-lg-recordp.
;; The profile's publication gate admits a record of MAX octets
;; (fn-store-publication-admissibility), so a record of MAX-31..MAX octets
;; would be appended, fenced and acknowledged, and the next open would stop
;; at its entry and zero it and every later record.  The host asks this
;; verdict for the record the log takes before it fences the store
;; (host/native/io.lisp fnn-log-publish, and the import's take in
;; fnn-log-write-history), and refuses by name: a known pre-publication
;; refusal.  The bound is the profile's own (D27), the log's format unchanged.
;;
;; THE LOG'S FRAME BOUND (lane m1-durable-2; the regression the verdict above
;; exposed in batch 6, dev 6107ceb56: native recovery's atomic hybrid article
;; and log_compaction's rotation took records of R-31..R octets that the
;; shipped profiles admit, and the verdict refused them).  The verdict is
;; right about the bound it is handed; the bound was wrong.  The log is
;; scanned and appended with MAX = R + 32 (fn-lgu-log-max of the profile's
;; record field R), so every record the store admits -- R octets or fewer --
;; is framed (fn-lgu-log-max-frames-every-record-within-r: R is at most the
;; poll reply's ceiling, u32 - 355, so R + 32 stays within the frame's u32),
;; and the verdict refuses exactly the records past R
;; (fn-lgu-log-max-refuses-past-r), which the publication gate never admits.
;; The host's log bound: host/native/io.lisp fnn-store-log-max and the
;; import's open (fnn-log-write-history); the read-only and developer scans
;; in host/store-open-host.lisp and host/store-write-host.lisp.  The entry
;; checks bound sizes from above only, so a segment written under the old
;; bound reads the same under the new one (not stated as a theorem here).
(defun fn-lgu-log-max (r)
  (declare (xargs :guard t))
  (+ (nfix r) *fn-frame-trailer-octets*))

(defun fn-lgu-take-verdict (record max)
  (declare (xargs :guard t))
  (if (fn-lg-recordp record max) :admissible :record-exceeds-log-frame))

(defthm fn-lgu-take-verdict-admits-exactly-log-records
  (and (member-equal (fn-lgu-take-verdict record max)
                     '(:admissible :record-exceeds-log-frame))
       (iff (equal (fn-lgu-take-verdict record max) :admissible)
            (fn-lg-recordp record max)))
  :rule-classes nil)

; KEYSTONE: every record within the profile's record field is framed by the
; log at its frame bound.
(defthm fn-lgu-log-max-frames-every-record-within-r
  (implies (and (fn-cbor-octet-listp record)
                (<= (len record) (fn-bs-profile-max-record-octets values)))
           (equal (fn-lgu-take-verdict record
                                       (fn-lgu-log-max (fn-bs-profile-max-record-octets values)))
                  :admissible))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-profile-valid-record-fits-a-poll-reply))
           :in-theory (e/d (fn-lgu-take-verdict fn-lg-recordp fn-lgu-log-max)
                           (fn-bs-profile-max-record-octets fn-cbor-octet-listp
                            fn-bs-publication-admissiblep)))))

; And refuses exactly past R.
(defthm fn-lgu-log-max-refuses-past-r
  (implies (< (nfix r) (len record))
           (equal (fn-lgu-take-verdict record (fn-lgu-log-max r))
                  :record-exceeds-log-frame))
  :hints (("Goal" :in-theory (enable fn-lgu-take-verdict fn-lg-recordp))))

(defun fn-lgu-kernel-op-p (op)
  (declare (xargs :guard t))
  (and (consp op)
       (member-equal (car op) '(:prepare :take :consume-to :finish-one :fence-failed))
       t))

; The extension, when the sealed extent NEXT is past the segment's EXTENT:
; (mv PAIRS BS OK), the cut states recorded with the host's kernel KS.
(defun fn-lgu-extend (bs ks ino extent next eo1 eo2)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal next extent)
      (mv nil bs t)
    (mv-let (r1 bs1) (fn-bs-write bs ino extent (fn-bs-zeros (- (nfix next) (nfix extent))) eo1)
      (declare (ignore r1))
      (if (not (equal eo1 :ok))
          (mv (list (cons bs1 ks)) bs1 nil)
        (mv-let (r2 bs2) (fn-bs-fsync-file bs1 ino eo2)
          (declare (ignore r2))
          (mv (list (cons bs1 ks) (cons bs2 ks)) bs2 (equal eo2 :ok)))))))

; One operation: (mv PAIRS BS1 KS1), PAIRS the cut states it passes, in
; order, each (STORE . KERNEL) with the host's kernel at that cut.
(defun fn-lgu-host-step (bs ks op ino max)
  (declare (xargs :guard t :verify-guards nil))
  (let ((unit (fn-bs-unit bs)))
    (cond
     ((fn-lgu-kernel-op-p op)
      (if (and (member-equal (car op) '(:prepare :take))
               (not (equal (fn-lgu-take-verdict (nth 1 op) max) :admissible)))
          (mv nil bs ks)
        (let ((ks1 (fn-lgk-host-step ks op)))
          (mv (list (cons bs ks1)) bs ks1))))
     ((and (consp op) (equal (car op) :seal))
      (let* ((extent (len (fn-bs-durable-content bs ino)))
             (next (fn-lgk-sealed-extent ks extent unit)))
        (if (not (fn-lg-append-admitsp ks unit next))
            (mv nil bs ks)
          (let ((ks1 (fn-lgk-append ks unit next)))
            (mv-let (xpairs bs2 xok)
              (fn-lgu-extend bs ks1 ino extent next (nth 1 op) (nth 2 op))
              (if (not xok)
                  (mv xpairs bs2 (fn-lgk-fence-failed ks1))
                (mv-let (r bs3)
                  (fn-bs-write bs2 ino (fn-lgk-frontier ks) (fn-lgk-append-octets ks unit)
                               (nth 3 op))
                  (declare (ignore r))
                  (mv (append xpairs (list (cons bs3 ks1)))
                      bs3
                      (if (equal (nth 3 op) :ok) ks1 (fn-lgk-fence-failed ks1))))))))))
     ((and (consp op) (equal (car op) :fence))
      (if (not (equal (fn-lgk-phase ks) :appended))
          (mv nil bs ks)
        (mv-let (r bs1) (fn-bs-fsync-file bs ino (nth 1 op))
          (declare (ignore r))
          (let ((ks1 (if (equal (nth 1 op) :ok) (fn-lgk-fence ks unit) (fn-lgk-fence-failed ks))))
            (mv (list (cons bs1 ks1)) bs1 ks1)))))
     (t (mv nil bs ks)))))

; Every cut state of a run of OPS from (BS . KS), the start included.
(defun fn-lgu-host-run (bs ks ops ino max)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom ops)
      (list (cons bs ks))
    (mv-let (pairs bs1 ks1) (fn-lgu-host-step bs ks (car ops) ino max)
      (cons (cons bs ks) (append pairs (fn-lgu-host-run bs1 ks1 (cdr ops) ino max))))))

(defun fn-lgu-invp (bs ks ino genesis max)
  (declare (xargs :guard t :verify-guards nil))
  (or (fn-lgk-relp bs ks ino genesis max)
      (and (equal (fn-lgk-phase ks) :fault)
           (fn-lgu-safep bs ks ino genesis max))))
(defthm fn-lgu-fence-failed-keeps-the-relation
  (implies (fn-lgk-relp bs ks ino genesis max)
           (fn-lgk-relp bs (fn-lgk-fence-failed ks) ino genesis max))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgk-fields-of-make fn-lgk-fence-failed)
                           (fn-lgk-make fn-lgk-relp fn-lgk-committed fn-lgk-last fn-lgk-frontier
                            fn-lgk-next-txid fn-lgk-batch fn-lgk-inflight fn-lgk-acked fn-lgk-phase))
           :use ((:instance fn-lgk-relp-forward)
                 (:instance fn-lgk-relp-when-fields-agree (k2 (fn-lgk-fence-failed ks)))))))
(defthm fn-lgu-consume-to-keeps-the-relation
  (implies (fn-lgk-relp bs ks ino genesis max)
           (fn-lgk-relp bs (fn-olr-consume-to ks txid) ino genesis max))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgk-fields-of-make fn-olr-consume-to)
                           (fn-lgk-make fn-lgk-relp fn-lgk-committed fn-lgk-last fn-lgk-frontier
                            fn-lgk-next-txid fn-lgk-batch fn-lgk-inflight fn-lgk-acked fn-lgk-phase))
           :use ((:instance fn-lgk-relp-forward)
                 (:instance fn-lgk-relp-when-fields-agree (k2 (fn-olr-consume-to ks txid)))))))
(local
 (defthm fn-lgu-kernel-op-keeps-the-relation
   (implies (and (fn-lgk-relp bs ks ino genesis max)
                 (fn-lgu-kernel-op-p op)
                 (implies (member-equal (car op) '(:prepare :take))
                          (fn-lg-recordp (nth 1 op) max)))
            (fn-lgk-relp bs (fn-lgk-host-step ks op) ino genesis max))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories '(fn-lgk-host-step fn-lgu-kernel-op-p member-equal)
                                       (theory 'minimal-theory))
            :use ((:instance fn-lgt-prepare-preserves-relation (record (nth 1 op)))
                  (:instance fn-olr-take-preserves-relation
                             (record (nth 1 op)) (txid (nth 2 op)) (count (nth 3 op))
                             (octets (nth 4 op)) (bmax (nth 5 op)) (omax (nth 6 op)) (unit (nth 7 op)))
                  (:instance fn-lgu-consume-to-keeps-the-relation (txid (nth 1 op)))
                  (:instance fn-lgk-finish-one-preserves-relation)
                  (:instance fn-lgu-fence-failed-keeps-the-relation))))))
(local
 (defthm fn-lgu-kernel-op-fields-under-fault
   (implies (and (equal (fn-lgk-phase ks) :fault)
                 (<= (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
                 (fn-lgu-kernel-op-p op))
            (let ((k2 (fn-lgk-host-step ks op)))
              (and (equal (fn-lgk-phase k2) :fault)
                   (equal (fn-lgk-committed k2) (fn-lgk-committed ks))
                   (equal (fn-lgk-frontier k2) (fn-lgk-frontier ks))
                   (<= (fn-lgk-acked k2) (len (fn-lgk-committed ks))))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lgk-host-step fn-lgu-kernel-op-p fn-lgt-prepare fn-lgk-prepare
                             fn-olr-take fn-olr-consume-to fn-lgk-finish-one fn-lgk-fence-failed
                             fn-lgk-fields-of-make)
                            (fn-lgk-make fn-lgk-committed fn-lgk-last fn-lgk-frontier
                             fn-lgk-next-txid fn-lgk-batch fn-lgk-inflight fn-lgk-acked fn-lgk-phase
                             fn-lgk-append fn-lgk-fence fn-lgs-rotate
                             fn-lgs-rotate-admitsp fn-lgk-sealed-extent fn-olr-entry-octets))))))
(local
 (defthm fn-lgu-kernel-op-keeps-the-fault
   (implies (and (equal (fn-lgk-phase ks) :fault)
                 (fn-lgu-safep bs ks ino genesis max)
                 (fn-lgu-kernel-op-p op))
            (and (equal (fn-lgk-phase (fn-lgk-host-step ks op)) :fault)
                 (fn-lgu-safep bs (fn-lgk-host-step ks op) ino genesis max)))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-lgu-safep fn-lgk-host-step fn-lgu-kernel-op-p
                                fn-lgk-phase fn-lgk-committed fn-lgk-frontier fn-lgk-acked)
            :use ((:instance fn-lgu-safep-acked-within)
                  (:instance fn-lgu-kernel-op-fields-under-fault)
                  (:instance fn-lgu-safep-when-fields-agree (k2 (fn-lgk-host-step ks op))))))))
(local
 (defthm fn-lgu-safep-frontier-within
   (implies (fn-lgu-safep bs ks ino genesis max)
            (<= (fn-lgk-frontier ks) (len (fn-bs-durable-content bs ino))))
   :rule-classes :linear))
(defthm fn-lgu-extend-keeps-safe
  (implies (and (fn-lgu-safep bs k ino genesis max)
                (equal extent (len (fn-bs-durable-content bs ino))))
           (mv-let (pairs bs2 ok) (fn-lgu-extend bs k ino extent next eo1 eo2)
             (declare (ignore ok))
             (and (fn-lgu-all-safep pairs ino genesis max)
                  (fn-lgu-safep bs2 k ino genesis max)
                  (equal (fn-bs-unit bs2) (fn-bs-unit bs)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lgu-safep fn-bs-write fn-bs-fsync-file fn-bs-zeros
                               fn-bs-durable-content fn-lgk-frontier))))
(local
 (defthm fn-lgu-zeros-true-listp (true-listp (fn-bs-zeros n))))
(local
 (defthm fn-lgu-take-of-zeros
   (implies (natp n)
            (equal (fn-bs-take n (fn-bs-zeros n)) (fn-bs-zeros n)))
   :hints (("Goal" :use ((:instance fn-lgc-take-all (a (fn-bs-zeros n)) (n n)))
            :in-theory (e/d (fn-lgc-take-all fn-lgc-zeros-len) (fn-bs-zeros fn-bs-take))))))
(local
 (defthm fn-lgu-nthcdr-past-a-true-list
   (implies (and (true-listp c) (natp k)) (equal (nthcdr (+ (len c) k) c) nil))))
(local
 (defthm fn-lgu-splice-at-the-end
   (implies (and (true-listp c) (true-listp z))
            (equal (fn-bs-splice c (len c) z) (append c z)))
   :hints (("Goal" :in-theory (enable fn-bs-splice)
            :use ((:instance fn-lgu-nthcdr-past-a-true-list (k (len z))))))))
(local
 (defthm fn-lgu-two-steps-are-the-extended-state
   (implies (and (null (fn-bs-pending bs)) (assoc-equal ino (fn-bs-inodes bs))
                 (true-listp (fn-bs-durable-content bs ino))
                 (equal extent (len (fn-bs-durable-content bs ino)))
                 (< extent (nfix next)))
            (equal (mv-nth 1 (fn-bs-fsync-file
                              (mv-nth 1 (fn-bs-write bs ino extent
                                                     (fn-bs-zeros (- (nfix next) (nfix extent))) :ok))
                              ino :ok))
                   (fn-lg-extended-state bs ino next)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bs-write fn-bs-fsync-file fn-bs-fence-file fn-bs-durable-content
                             fn-lg-extended-state fn-bs-apply-op fn-bs-splice)
                            (fn-bs-zeros))))))
(defthm fn-lgu-extend-keeps-the-relation
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (not (consp (fn-lgk-inflight ks)))
                (equal extent (len (fn-bs-durable-content bs ino)))
                (natp next) (equal (mod next (fn-bs-unit bs)) 0) (<= extent next))
           (mv-let (pairs bs2 ok) (fn-lgu-extend bs k ino extent next eo1 eo2)
             (declare (ignore pairs))
             (implies ok
                      (and (fn-lgk-relp bs2 ks ino genesis max)
                           (equal (len (fn-bs-durable-content bs2 ino)) next)))))
  :hints (("Goal" :do-not-induct t
           :cases ((equal next extent))
           :in-theory (disable fn-lgk-relp fn-bs-write fn-bs-fsync-file fn-bs-zeros
                               fn-bs-durable-content fn-lg-extended-state
                               fn-lg-extension-keeps-the-relation
                               fn-lgu-two-steps-are-the-extended-state mod floor)
           :use ((:instance fn-lgk-relp-at-rest)
                 (:instance fn-lgu-two-steps-are-the-extended-state)
                 (:instance fn-lg-extension-keeps-the-relation)))))
(local
 (defthm fn-lgu-sealed-extent-facts
   (implies (and (posp unit) (natp extent) (equal (mod extent unit) 0))
            (let ((next (fn-lgk-sealed-extent ks extent unit)))
              (and (natp next) (equal (mod next unit) 0) (<= extent next))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-lgc-sealed-extent fn-lgk-sealed-extent fn-lgc-fitsp mod
                                fn-lgc-sealed-extent-fits-the-batch fn-lgc-sealed-extent-of-abstraction)
            :use ((:instance fn-lgc-sealed-extent-fits-the-batch (c (fn-lgc-of ks)))
                  (:instance fn-lgc-sealed-extent-of-abstraction))))))
(local
 (defthm fn-lgu-fields-of-append
   (let ((k2 (fn-lgk-append ks unit extent)))
     (and (equal (fn-lgk-committed k2) (fn-lgk-committed ks))
          (equal (fn-lgk-frontier k2) (fn-lgk-frontier ks))
          (equal (fn-lgk-acked k2) (fn-lgk-acked ks))))
   :hints (("Goal" :in-theory (e/d (fn-lgk-append fn-lgk-fields-of-make)
                                   (fn-lgk-make fn-lgk-committed fn-lgk-frontier fn-lgk-acked
                                    fn-lgk-fitsp fn-lgk-inflight fn-lgk-phase fn-lgk-batch))))))
(local
 (defthm fn-lgu-fields-of-fence-failed
   (let ((k2 (fn-lgk-fence-failed ks)))
     (and (equal (fn-lgk-committed k2) (fn-lgk-committed ks))
          (equal (fn-lgk-frontier k2) (fn-lgk-frontier ks))
          (equal (fn-lgk-acked k2) (fn-lgk-acked ks))
          (equal (fn-lgk-phase k2) :fault)))
   :hints (("Goal" :in-theory (e/d (fn-lgk-fence-failed fn-lgk-fields-of-make)
                                   (fn-lgk-make fn-lgk-committed fn-lgk-frontier fn-lgk-acked
                                    fn-lgk-phase))))))
(local
 (defthm fn-lgu-safe-of-append-and-fence-failed
   (implies (fn-lgu-safep bs ks ino genesis max)
            (and (fn-lgu-safep bs (fn-lgk-append ks unit extent) ino genesis max)
                 (fn-lgu-safep bs (fn-lgk-fence-failed ks) ino genesis max)))
   :hints (("Goal" :in-theory (disable fn-lgu-safep fn-lgk-append fn-lgk-fence-failed)
            :use ((:instance fn-lgu-safep-acked-within)
                  (:instance fn-lgu-safep-when-fields-agree (k2 (fn-lgk-append ks unit extent)))
                  (:instance fn-lgu-safep-when-fields-agree (k2 (fn-lgk-fence-failed ks))))))))
(local
 (defthm fn-lgu-relp-content-shape
   (implies (fn-lgk-relp bs ks ino genesis max)
            (and (posp (fn-bs-unit bs))
                 (equal (mod (len (fn-bs-durable-content bs ino)) (fn-bs-unit bs)) 0)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-lgk-relp fn-lgk-content-okp)
                                   (fn-lg-scan fn-lg-scan-last fn-lg-log fn-bs-take fn-lg-zerosp
                                    fn-lg-recordsp fn-frame-digestp fn-bs-durable-content mod))))))
(local
 (defthm fn-lgu-seal-step-from-the-relation
   (implies (and (fn-lgk-relp bs ks ino genesis max)
                 (consp op) (equal (car op) :seal))
            (mv-let (pairs bs1 ks1) (fn-lgu-host-step bs ks op ino max)
              (and (fn-lgu-all-safep pairs ino genesis max)
                   (fn-lgu-invp bs1 ks1 ino genesis max)
                   (equal (fn-bs-unit bs1) (fn-bs-unit bs)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lgu-host-step fn-lgu-invp fn-lg-append-admitsp)
                            (fn-lgk-relp fn-lgu-safep fn-lgu-extend fn-bs-write fn-bs-fsync-file
                             fn-lgk-append fn-lgk-fence-failed fn-lgk-sealed-extent fn-lgk-append-octets
                             fn-lgk-fitsp fn-bs-durable-content fn-lgk-frontier fn-lgk-inflight
                             fn-lgk-phase mod
                             fn-lgk-append-preserves-relation fn-lgu-extend-keeps-the-relation
                             fn-lgu-extend-keeps-safe))
            :use ((:instance fn-lgu-relp-content-shape)
                  (:instance fn-lgu-related-state-is-safe)
                  (:instance fn-lgu-sealed-extent-facts
                             (unit (fn-bs-unit bs)) (extent (len (fn-bs-durable-content bs ino))))
                  (:instance fn-lgu-extend-keeps-safe
                             (k (fn-lgk-append ks (fn-bs-unit bs)
                                               (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                                     (fn-bs-unit bs))))
                             (extent (len (fn-bs-durable-content bs ino)))
                             (next (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                         (fn-bs-unit bs)))
                             (eo1 (nth 1 op)) (eo2 (nth 2 op)))
                  (:instance fn-lgu-extend-keeps-the-relation
                             (k (fn-lgk-append ks (fn-bs-unit bs)
                                               (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                                     (fn-bs-unit bs))))
                             (extent (len (fn-bs-durable-content bs ino)))
                             (next (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                         (fn-bs-unit bs)))
                             (eo1 (nth 1 op)) (eo2 (nth 2 op)))
                  (:instance fn-lgk-append-preserves-relation
                             (bs (mv-nth 1 (fn-lgu-extend bs
                                                          (fn-lgk-append ks (fn-bs-unit bs)
                                                                         (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                                                               (fn-bs-unit bs)))
                                                          ino (len (fn-bs-durable-content bs ino))
                                                          (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                                                (fn-bs-unit bs))
                                                          (nth 1 op) (nth 2 op)))))
                  (:instance fn-lgu-write-keeps-safe
                             (bs (mv-nth 1 (fn-lgu-extend bs
                                                          (fn-lgk-append ks (fn-bs-unit bs)
                                                                         (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                                                               (fn-bs-unit bs)))
                                                          ino (len (fn-bs-durable-content bs ino))
                                                          (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                                                (fn-bs-unit bs))
                                                          (nth 1 op) (nth 2 op))))
                             (ks (fn-lgk-append ks (fn-bs-unit bs)
                                                (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                                      (fn-bs-unit bs))))
                             (off (fn-lgk-frontier ks))
                             (octets (fn-lgk-append-octets ks (fn-bs-unit bs)))
                             (outcome (nth 3 op))))))))
(local
 (defthm fn-lgu-unit-of-fsync-any
   (equal (fn-bs-unit (mv-nth 1 (fn-bs-fsync-file s ino outcome))) (fn-bs-unit s))
   :hints (("Goal" :in-theory (enable fn-bs-fsync-file fn-bs-fence-file)))))
(local
 (defthm fn-lgu-fence-step-from-the-relation
   (implies (and (fn-lgk-relp bs ks ino genesis max)
                 (consp op) (equal (car op) :fence))
            (mv-let (pairs bs1 ks1) (fn-lgu-host-step bs ks op ino max)
              (and (fn-lgu-all-safep pairs ino genesis max)
                   (fn-lgu-invp bs1 ks1 ino genesis max)
                   (equal (fn-bs-unit bs1) (fn-bs-unit bs)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lgu-host-step fn-lgu-invp)
                            (fn-lgk-relp fn-lgu-safep fn-bs-fsync-file fn-lgk-fence
                             fn-lgk-fence-failed fn-lgk-phase))
            :use ((:instance fn-lgu-related-state-is-safe)
                  (:instance fn-lgk-fence-preserves-relation)
                  (:instance fn-lgu-related-state-is-safe
                             (bs (mv-nth 1 (fn-bs-fsync-file bs ino :ok)))
                             (ks (fn-lgk-fence ks (fn-bs-unit bs))))
                  (:instance fn-lgu-fsync-keeps-safe (outcome (nth 1 op))))))))
(local
 (defthm fn-lgu-step-from-the-fault
   (implies (and (equal (fn-lgk-phase ks) :fault)
                 (fn-lgu-safep bs ks ino genesis max))
            (mv-let (pairs bs1 ks1) (fn-lgu-host-step bs ks op ino max)
              (and (fn-lgu-all-safep pairs ino genesis max)
                   (fn-lgu-invp bs1 ks1 ino genesis max)
                   (equal (fn-bs-unit bs1) (fn-bs-unit bs)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lgu-host-step fn-lgu-invp fn-lg-append-admitsp)
                            (fn-lgk-relp fn-lgu-safep fn-lgk-host-step fn-lgu-kernel-op-p
                             fn-lgk-phase fn-lgk-inflight fn-lgk-fitsp fn-lgu-extend fn-bs-write
                             fn-bs-fsync-file fn-lgk-sealed-extent))
            :use ((:instance fn-lgu-kernel-op-keeps-the-fault))))))
(local
 (defthm fn-lgu-host-step-of-a-kernel-op
   (implies (and (fn-lgu-kernel-op-p op)
                 (implies (member-equal (car op) '(:prepare :take))
                          (equal (fn-lgu-take-verdict (nth 1 op) max) :admissible)))
            (equal (fn-lgu-host-step bs ks op ino max)
                   (list (list (cons bs (fn-lgk-host-step ks op))) bs (fn-lgk-host-step ks op))))
   :hints (("Goal" :in-theory (disable fn-lgk-host-step fn-lgu-take-verdict)))))
(local
 (defthm fn-lgu-host-step-of-a-refused-take
   (implies (and (fn-lgu-kernel-op-p op)
                 (member-equal (car op) '(:prepare :take))
                 (not (equal (fn-lgu-take-verdict (nth 1 op) max) :admissible)))
            (equal (fn-lgu-host-step bs ks op ino max) (list nil bs ks)))
   :hints (("Goal" :in-theory (disable fn-lgk-host-step fn-lgu-take-verdict)))))
(local
 (defthm fn-lgu-host-step-of-nothing
   (implies (and (not (fn-lgu-kernel-op-p op))
                 (not (and (consp op) (equal (car op) :seal)))
                 (not (and (consp op) (equal (car op) :fence))))
            (equal (fn-lgu-host-step bs ks op ino max) (list nil bs ks)))
   :hints (("Goal" :in-theory (disable fn-lgk-host-step)))))
(local
 (defthm fn-lgu-step-from-the-relation
   (implies (fn-lgk-relp bs ks ino genesis max)
            (mv-let (pairs bs1 ks1) (fn-lgu-host-step bs ks op ino max)
              (and (fn-lgu-all-safep pairs ino genesis max)
                   (fn-lgu-invp bs1 ks1 ino genesis max)
                   (equal (fn-bs-unit bs1) (fn-bs-unit bs)))))
   :hints (("Goal" :do-not-induct t
            :cases ((and (fn-lgu-kernel-op-p op)
                         (member-equal (car op) '(:prepare :take))
                         (not (equal (fn-lgu-take-verdict (nth 1 op) max) :admissible)))
                    (fn-lgu-kernel-op-p op)
                    (and (consp op) (equal (car op) :seal))
                    (and (consp op) (equal (car op) :fence)))
            :in-theory (e/d (fn-lgu-invp)
                            (fn-lgk-relp fn-lgu-safep fn-lgk-host-step fn-lgu-host-step
                             fn-lgu-kernel-op-p fn-lg-recordp fn-lgu-take-verdict
                             fn-lgu-host-step-of-a-kernel-op fn-lgu-host-step-of-a-refused-take
                             fn-lgu-seal-step-from-the-relation fn-lgu-fence-step-from-the-relation))
            :use ((:instance fn-lgu-take-verdict-admits-exactly-log-records (record (nth 1 op)))
                  (:instance fn-lgu-host-step-of-a-kernel-op)
                  (:instance fn-lgu-host-step-of-a-refused-take)
                  (:instance fn-lgu-seal-step-from-the-relation)
                  (:instance fn-lgu-fence-step-from-the-relation)
                  (:instance fn-lgu-kernel-op-keeps-the-relation)
                  (:instance fn-lgu-related-state-is-safe
                             (ks (fn-lgk-host-step ks op))))))))
(local
 (defthm fn-lgu-invp-is-safe
   (implies (fn-lgu-invp bs ks ino genesis max)
            (fn-lgu-safep bs ks ino genesis max))
   :hints (("Goal" :in-theory (disable fn-lgu-safep fn-lgk-relp)))))
(local
 (defthm fn-lgu-step-keeps-the-invariant
   (implies (fn-lgu-invp bs ks ino genesis max)
            (and (fn-lgu-all-safep (mv-nth 0 (fn-lgu-host-step bs ks op ino max)) ino genesis max)
                 (fn-lgu-invp (mv-nth 1 (fn-lgu-host-step bs ks op ino max))
                              (mv-nth 2 (fn-lgu-host-step bs ks op ino max)) ino genesis max)))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories '(fn-lgu-invp) (theory 'minimal-theory))
            :use ((:instance fn-lgu-step-from-the-relation)
                  (:instance fn-lgu-step-from-the-fault))))))
(defthm fn-lgu-host-run-is-safe
  (implies (fn-lgu-invp bs ks ino genesis max)
           (fn-lgu-all-safep (fn-lgu-host-run bs ks ops ino max) ino genesis max))
  :hints (("Goal" :induct (fn-lgu-host-run bs ks ops ino max)
           :in-theory (union-theories '(fn-lgu-host-run fn-lgu-all-safep fn-lgu-all-safep-of-append
                                        fn-lgu-invp-is-safe car-cons cdr-cons
                                        (:induction fn-lgu-host-run))
                                      (theory 'minimal-theory)))
          ("Subgoal *1/2" :use ((:instance fn-lgu-step-keeps-the-invariant (op (car ops)))))))

; -----------------------------------------------------------------------------
; 4. What the kernel acknowledged is recovered at every cut (a lemma: the
; host-entry KEYSTONE fn-lgu-acknowledge-acknowledges-only-recoverable-records,
; section 8, states it over the function the host calls).
;
; Subject: the log kernel's acknowledged count, the one fnn-log-ack
; advances (fn-lgc-finish-one, through fnn-log-finish) in the COMPLETE
; before the batch's replies leave (host/native/owner.lisp
; fnn-owner-commit-complete-locked: fnn-log-batch-finish, then each
; member's :rendered reply, as fn-ocs-member-releases names for
; fn-ocs-commit-step's :complete), and in a batch of one (fnn-finish).
; From a store related to the kernel (R: the open establishes it,
; fn-lgu-open-run-acknowledges-only-recoverable-records below), over any
; sequence of the host's operations (a take of a record the log cannot
; frame refused by its verdict, as the host refuses it), at every
; cut state of the run and for every admissible crash image of it, the
; kernel's first ACKED committed records are the first ACKED records the
; next open recovers.  The tear model is the platform's (fn-bs-crash-imagep);
; no trailer assumption.  Scope: one segment, no rotation.
(defthm fn-lgu-acknowledged-records-are-recovered-at-every-cut
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (member-equal pair (fn-lgu-host-run bs ks ops ino max))
                (fn-bs-crash-imagep (car pair) image))
           (let ((a (fn-lgk-acked (cdr pair)))
                 (recovered (fn-lgk-committed
                             (fn-lgk-recover (fn-bs-durable-content image ino)
                                             genesis (fn-bs-unit (car pair)) max next-txid))))
             (and (<= a (len recovered))
                  (equal (take a recovered) (take a (fn-lgk-committed (cdr pair)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-lgu-invp) (theory 'minimal-theory))
           :use ((:instance fn-lgu-host-run-is-safe)
                 (:instance fn-lgu-all-safep-member (pairs (fn-lgu-host-run bs ks ops ino max)))
                 (:instance fn-lgu-safe-image-recovers-the-acknowledged-records
                            (bs (car pair)) (ks (cdr pair)))))))

; -----------------------------------------------------------------------------
; 5. From the open: P-LOG-RECOVER's every cut, then the served run.
;
; The store the open reads (BS) is a crash image or a fresh segment:
; nothing pending (fn-bs-crash leaves no pending operation).  Its kernel is
; fn-lg-recovered-kernel (fnn-log-recover: fn-lgc-open of the segment's
; octets, fn-lgc-open-refines); every cut of the recovery program under any
; outcomes acknowledges only what the scan read (the recovered kernel's
; ACKED is its record count), and from the program's last state, related
; (fn-lg-recover-program-establishes-the-relation, its sole-pending-writer
; obligation discharged here for a store with nothing pending), the
; keystone covers every cut of the served run.

(defun fn-lgu-tail-steps-p (steps)
  (declare (xargs :guard t))
  (if (atom steps)
      t
    (and (or (equal (car steps) '(:write-at :segment :tail))
             (equal (car steps) '(:fence :segment :tail))
             (and (consp (car steps)) (equal (car (car steps)) :cut)))
         (fn-lgu-tail-steps-p (cdr steps)))))
(local
 (defthm fn-lgu-tail-step-is-safe
   (implies (and (fn-lgu-safep bs ks ino genesis max)
                 (or (equal step '(:write-at :segment :tail))
                     (equal step '(:fence :segment :tail))
                     (and (consp step) (equal (car step) :cut))))
            (and (fn-lgu-safep (mv-nth 1 (fn-lg-step bs ks step outcome ino)) ks ino genesis max)
                 (equal (mv-nth 2 (fn-lg-step bs ks step outcome ino)) ks)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lg-step)
                            (fn-lgu-safep fn-bs-write fn-bs-fsync-file fn-bs-zeros
                             fn-bs-durable-content fn-lgk-frontier fn-lgk-append fn-lgk-fence
                             fn-lgk-fence-failed fn-lg-append-admitsp fn-lgk-append-octets))
            :use ((:instance fn-lgu-write-keeps-safe
                             (off (fn-lgk-frontier ks))
                             (octets (fn-bs-zeros (- (len (fn-bs-durable-content bs ino))
                                                     (fn-lgk-frontier ks)))))
                  (:instance fn-lgu-fsync-keeps-safe))))))
(local
 (defthm fn-lgu-tail-run-is-safe
   (implies (and (fn-lgu-safep bs ks ino genesis max)
                 (fn-lgu-tail-steps-p steps))
            (fn-lgu-all-safep (fn-lg-run bs ks steps outcomes ino) ino genesis max))
   :hints (("Goal" :induct (fn-lg-run bs ks steps outcomes ino)
            :in-theory (union-theories '(fn-lg-run fn-lgu-all-safep fn-lgu-tail-steps-p
                                         car-cons cdr-cons (:induction fn-lg-run))
                                       (theory 'minimal-theory)))
           ("Subgoal *1/1" :use ((:instance fn-lgu-tail-step-is-safe
                                            (step (car steps))
                                            (outcome (if (consp outcomes) (car outcomes) :ok))))))))
(local
 (defthm fn-lgu-acked-of-recover
   (equal (fn-lgk-acked (fn-lgk-recover c genesis unit max next-txid))
          (len (car (fn-lg-scan c genesis unit max))))
   :hints (("Goal" :in-theory (disable fn-lg-scan fn-lg-scan-last)))))
(defthm fn-lgu-recovered-kernel-is-safe
  (implies (and (posp (fn-bs-unit bs)) ino
                (true-listp (fn-bs-durable-content bs ino))
                (equal (mod (len (fn-bs-durable-content bs ino)) (fn-bs-unit bs)) 0)
                (null (fn-bs-pending bs)))
           (fn-lgu-safep bs (fn-lg-recovered-kernel bs ino genesis max floor) ino genesis max))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgu-safep fn-lgu-recovered-kernel-is-the-recover-by-definition)
                           (fn-lg-scan fn-lg-scan-last fn-bs-take fn-lgk-recover fn-lgt-next-after
                            fn-lg-recovered-kernel fn-bs-durable-content mod))
           :use ((:instance fn-lg-recovered-frontier-is-the-last-complete-record
                            (c (fn-bs-durable-content bs ino)) (unit (fn-bs-unit bs)))
                 (:instance fn-lgc-scan-records-true-listp
                            (octets (fn-bs-durable-content bs ino)) (prev genesis)
                            (unit (fn-bs-unit bs)))))))
; The sole pending writer at the open, discharged at kernel level: a store
; with nothing pending (every crash image: fn-bs-crash leaves none) has no
; operation of another file pending.
(defun fn-lgu-sole-pending-writer (bs ino)
  (declare (xargs :guard t :verify-guards nil))
  (not (fn-bs-ops-not-for-ino (fn-bs-pending bs) ino)))
(defthm fn-lgu-recover-program-establishes-the-relation
  (let* ((ks (fn-lg-recovered-kernel bs ino genesis max floor))
         (run (fn-lg-run bs ks (fn-lg-recover-program) nil ino))
         (final (car (last run))))
    (implies (and (posp (fn-bs-unit bs)) ino (assoc-equal ino (fn-bs-inodes bs))
                  (true-listp (fn-bs-durable-content bs ino))
                  (equal (mod (len (fn-bs-durable-content bs ino)) (fn-bs-unit bs)) 0)
                  (fn-frame-digestp genesis)
                  (fn-lgu-sole-pending-writer bs ino)
                  (not (fn-bs-ops-for-ino (fn-bs-pending bs) ino)))
             (and (equal (len run) 4)
                  (fn-lgk-relp (car final) (cdr final) ino genesis max))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory) '(fn-lgu-sole-pending-writer))
           :use ((:functional-instance fn-lg-recover-program-establishes-the-relation
                                       (fn-assume-log-sole-pending-writer
                                        fn-lgu-sole-pending-writer))))))
(defthm fn-lgu-open-run-acknowledges-only-recoverable-records
  (let* ((ks0 (fn-lg-recovered-kernel bs ino genesis max floor))
         (opened (car (last (fn-lg-run bs ks0 (fn-lg-recover-program) nil ino)))))
    (implies (and (posp (fn-bs-unit bs)) ino (assoc-equal ino (fn-bs-inodes bs))
                  (true-listp (fn-bs-durable-content bs ino))
                  (equal (mod (len (fn-bs-durable-content bs ino)) (fn-bs-unit bs)) 0)
                  (fn-frame-digestp genesis)
                  (null (fn-bs-pending bs))
                  (or (member-equal pair (fn-lg-run bs ks0 (fn-lg-recover-program) routs ino))
                      (member-equal pair (fn-lgu-host-run (car opened) (cdr opened) ops ino max)))
                  (fn-bs-crash-imagep (car pair) image))
             (let ((a (fn-lgk-acked (cdr pair)))
                   (recovered (fn-lgk-committed
                               (fn-lgk-recover (fn-bs-durable-content image ino)
                                               genesis (fn-bs-unit (car pair)) max next-txid))))
               (and (<= a (len recovered))
                    (equal (take a recovered) (take a (fn-lgk-committed (cdr pair))))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-lgu-sole-pending-writer fn-bs-ops-not-for-ino
                                        fn-bs-ops-for-ino atom
                                        (:executable-counterpart fn-lg-recover-program)
                                        (:executable-counterpart fn-lgu-tail-steps-p))
                                      (theory 'minimal-theory))
           :use ((:instance fn-lgu-recovered-kernel-is-safe)
                 (:instance fn-lgu-tail-run-is-safe
                            (ks (fn-lg-recovered-kernel bs ino genesis max floor))
                            (steps (fn-lg-recover-program)) (outcomes routs))
                 (:instance fn-lgu-all-safep-member
                            (pairs (fn-lg-run bs (fn-lg-recovered-kernel bs ino genesis max floor)
                                              (fn-lg-recover-program) routs ino)))
                 (:instance fn-lgu-safe-image-recovers-the-acknowledged-records
                            (bs (car pair)) (ks (cdr pair)))
                 (:instance fn-lgu-recover-program-establishes-the-relation)
                 (:instance fn-lgu-acknowledged-records-are-recovered-at-every-cut
                            (bs (car (car (last (fn-lg-run bs (fn-lg-recovered-kernel bs ino genesis max floor)
                                                           (fn-lg-recover-program) nil ino)))))
                            (ks (cdr (car (last (fn-lg-run bs (fn-lg-recovered-kernel bs ino genesis max floor)
                                                           (fn-lg-recover-program) nil ino))))))))))

; -----------------------------------------------------------------------------
; 6. The count the host holds.  The host's kernel is the concrete one
; (books/store-log-kernel-concrete.lisp, PRF-282): from fn-lgc-open of the
; segment's octets S (the durable content, A-HOST's read of the regular
; file), after the kernel operations of the run (fn-lgu-host-kops, each a
; fn-lgc-host-step the host calls), its acknowledged count fn-lgc-acked is
; the logical kernel's (fn-lgc-run-refines-the-kernel), so the first that
; many committed records are the first the next open recovers from every
; crash image of the store the run leaves.

; The kernel operations, in fn-lgk-host-step's language, an operation
; applies: what the host's concrete kernel runs (fn-lgc-host-step).
(defun fn-lgu-step-kops (bs ks op ino max)
  (declare (xargs :guard t :verify-guards nil))
  (let ((unit (fn-bs-unit bs)))
    (cond
     ((fn-lgu-kernel-op-p op)
      (if (and (member-equal (car op) '(:prepare :take))
               (not (equal (fn-lgu-take-verdict (nth 1 op) max) :admissible)))
          nil
        (list op)))
     ((and (consp op) (equal (car op) :seal))
      (let ((extent (len (fn-bs-durable-content bs ino))))
        (if (not (fn-lg-append-admitsp ks unit (fn-lgk-sealed-extent ks extent unit)))
            nil
          (mv-let (pairs bs1 ks1) (fn-lgu-host-step bs ks op ino max)
            (declare (ignore pairs bs1))
            (if (equal (fn-lgk-phase ks1) :fault)
                (list (list :seal unit extent) (list :fence-failed))
              (list (list :seal unit extent)))))))
     ((and (consp op) (equal (car op) :fence))
      (if (not (equal (fn-lgk-phase ks) :appended))
          nil
        (list (if (equal (nth 1 op) :ok) (list :fence unit) (list :fence-failed)))))
     (t nil))))
(defun fn-lgu-host-kops (bs ks ops ino max)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom ops)
      nil
    (mv-let (pairs bs1 ks1) (fn-lgu-host-step bs ks (car ops) ino max)
      (declare (ignore pairs))
      (append (fn-lgu-step-kops bs ks (car ops) ino max)
              (fn-lgu-host-kops bs1 ks1 (cdr ops) ino max)))))
; The state a run leaves.
(defun fn-lgu-host-final (bs ks ops ino max)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom ops)
      (cons bs ks)
    (mv-let (pairs bs1 ks1) (fn-lgu-host-step bs ks (car ops) ino max)
      (declare (ignore pairs))
      (fn-lgu-host-final bs1 ks1 (cdr ops) ino max))))
(local
 (defthm fn-lgu-lgk-host-run-of-append
   (equal (fn-lgk-host-run ks (append a b))
          (fn-lgk-host-run (fn-lgk-host-run ks a) b))
   :hints (("Goal" :in-theory (disable fn-lgk-host-step)))))
(local
 (defthm fn-lgu-step-kops-are-the-step
   (equal (fn-lgk-host-run ks (fn-lgu-step-kops bs ks op ino max))
          (mv-nth 2 (fn-lgu-host-step bs ks op ino max)))
   :hints (("Goal" :do-not-induct t
            :expand ((:free (k o) (fn-lgk-host-run k (list o)))
                     (:free (k o1 o2) (fn-lgk-host-run k (list o1 o2))))
            :in-theory (e/d (fn-lgk-host-step fn-lgk-append)
                            (fn-lgu-extend fn-bs-write fn-bs-fsync-file fn-lgk-sealed-extent
                             fn-lgk-fence fn-lgk-fence-failed fn-lgk-fitsp fn-lgk-append-octets
                             fn-lgt-prepare fn-olr-take fn-olr-consume-to fn-lgk-finish-one
                             fn-lgs-rotate fn-lgs-rotate-admitsp fn-lgk-make
                             fn-lgk-phase fn-lgk-inflight fn-bs-durable-content))))))
(defthm fn-lgu-host-kops-run-to-the-final-kernel
  (equal (fn-lgk-host-run ks (fn-lgu-host-kops bs ks ops ino max))
         (cdr (fn-lgu-host-final bs ks ops ino max)))
  :hints (("Goal" :induct (fn-lgu-host-final bs ks ops ino max)
           :expand ((fn-lgk-host-run ks nil))
           :in-theory (disable fn-lgu-host-step fn-lgu-step-kops fn-lgk-host-run))))
(local
 (defthm fn-lgu-host-final-is-a-cut
   (member-equal (fn-lgu-host-final bs ks ops ino max) (fn-lgu-host-run bs ks ops ino max))
   :hints (("Goal" :induct (fn-lgu-host-final bs ks ops ino max)
            :in-theory (disable fn-lgu-host-step)))))
(local
 (defthm fn-lgu-tail-step-keeps-the-kernel
   (implies (or (equal step '(:write-at :segment :tail))
                (equal step '(:fence :segment :tail))
                (and (consp step) (equal (car step) :cut)))
            (equal (mv-nth 2 (fn-lg-step bs ks step outcome ino)) ks))
   :hints (("Goal" :in-theory (e/d (fn-lg-step)
                                   (fn-bs-write fn-bs-fsync-file fn-bs-zeros fn-bs-durable-content
                                    fn-lgk-append fn-lgk-fence fn-lgk-fence-failed
                                    fn-lg-append-admitsp fn-lgk-append-octets fn-lgk-frontier))))))
(local
 (defthm fn-lgu-tail-run-keeps-the-kernel
   (implies (and (fn-lgu-tail-steps-p steps) (consp (fn-lg-run bs ks steps outcomes ino)))
            (equal (cdr (car (last (fn-lg-run bs ks steps outcomes ino)))) ks))
   :hints (("Goal" :induct (fn-lg-run bs ks steps outcomes ino)
            :in-theory (union-theories '(fn-lg-run fn-lgu-tail-steps-p last car-cons cdr-cons
                                         (:induction fn-lg-run))
                                       (theory 'minimal-theory)))
           ("Subgoal *1/1" :use ((:instance fn-lgu-tail-step-keeps-the-kernel
                                            (step (car steps))
                                            (outcome (if (consp outcomes) (car outcomes) :ok))))))))
(defthm fn-lgu-host-kernel-acknowledges-only-recoverable-records
  (let* ((ks0 (fn-lg-recovered-kernel bs ino genesis max floor))
         (opened (car (last (fn-lg-run bs ks0 (fn-lg-recover-program) nil ino))))
         (final (fn-lgu-host-final (car opened) (cdr opened) ops ino max))
         (host (fn-lgc-host-run (mv-nth 1 (fn-lgc-open s genesis (fn-bs-unit bs) max floor))
                                (fn-lgu-host-kops (car opened) (cdr opened) ops ino max))))
    (implies (and (posp (fn-bs-unit bs)) ino (assoc-equal ino (fn-bs-inodes bs))
                  (true-listp (fn-bs-durable-content bs ino))
                  (equal (mod (len (fn-bs-durable-content bs ino)) (fn-bs-unit bs)) 0)
                  (fn-frame-digestp genesis)
                  (null (fn-bs-pending bs))
                  (equal (fn-lgd-octets s) (fn-bs-durable-content bs ino))
                  (fn-bs-crash-imagep (car final) image))
             (let ((a (fn-lgc-acked host))
                   (recovered (fn-lgk-committed
                               (fn-lgk-recover (fn-bs-durable-content image ino)
                                               genesis (fn-bs-unit (car final)) max next-txid))))
               (and (equal a (fn-lgk-acked (cdr final)))
                    (<= a (len recovered))
                    (equal (take a recovered) (take a (fn-lgk-committed (cdr final))))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-lg-recovered-kernel fn-lgc-observers-of-abstraction
                                        fn-lgu-sole-pending-writer fn-bs-ops-not-for-ino
                                        fn-bs-ops-for-ino atom len
                                        (:executable-counterpart fn-lg-recover-program)
                                        (:executable-counterpart fn-lgu-tail-steps-p)
                                        fn-lgu-host-kops-run-to-the-final-kernel)
                                      (theory 'minimal-theory))
           :use ((:instance fn-lgc-run-refines-the-kernel
                            (unit (fn-bs-unit bs))
                            (ops (fn-lgu-host-kops
                                  (car (car (last (fn-lg-run bs (fn-lg-recovered-kernel bs ino genesis max floor)
                                                             (fn-lg-recover-program) nil ino))))
                                  (cdr (car (last (fn-lg-run bs (fn-lg-recovered-kernel bs ino genesis max floor)
                                                             (fn-lg-recover-program) nil ino))))
                                  ops ino max)))
                 (:instance fn-lgu-recover-program-establishes-the-relation)
                 (:instance fn-lgu-tail-run-keeps-the-kernel
                            (ks (fn-lg-recovered-kernel bs ino genesis max floor))
                            (steps (fn-lg-recover-program)) (outcomes nil))
                 (:instance fn-lgu-host-final-is-a-cut
                            (bs (car (car (last (fn-lg-run bs (fn-lg-recovered-kernel bs ino genesis max floor)
                                                           (fn-lg-recover-program) nil ino)))))
                            (ks (cdr (car (last (fn-lg-run bs (fn-lg-recovered-kernel bs ino genesis max floor)
                                                           (fn-lg-recover-program) nil ino))))))
                 (:instance fn-lgu-open-run-acknowledges-only-recoverable-records
                            (routs nil)
                            (pair (fn-lgu-host-final
                                   (car (car (last (fn-lg-run bs (fn-lg-recovered-kernel bs ino genesis max floor)
                                                              (fn-lg-recover-program) nil ino))))
                                   (cdr (car (last (fn-lg-run bs (fn-lg-recovered-kernel bs ino genesis max floor)
                                                              (fn-lg-recover-program) nil ino))))
                                   ops ino max)))))))


; -----------------------------------------------------------------------------
; 7. The COMPLETE acknowledges exactly the fenced batch.  From a kernel
; whose committed records are all acknowledged, the barrier's fence and one
; fn-lgk-finish-one per member of the batch in flight (fnn-log-batch-
; finish's fnn-log-ack, before the members' replies) leave the acknowledged
; records the committed ones followed by the batch, in order.

(defun fn-lgu-finishes (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons (list :finish-one) (fn-lgu-finishes (1- n)))))
(local
 (defun fn-lgu-finishes-ind (n ks)
   (declare (xargs :guard t :verify-guards nil))
   (if (zp n) ks (fn-lgu-finishes-ind (1- n) (fn-lgk-finish-one ks)))))
(local
 (defthm fn-lgu-finish-one-fields
   (implies (< (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
            (and (equal (fn-lgk-committed (fn-lgk-finish-one ks)) (fn-lgk-committed ks))
                 (equal (fn-lgk-acked (fn-lgk-finish-one ks)) (+ 1 (fn-lgk-acked ks)))))
   :hints (("Goal" :in-theory (e/d (fn-lgk-finish-one fn-lgk-fields-of-make)
                                   (fn-lgk-make fn-lgk-committed fn-lgk-acked fn-lgk-last
                                    fn-lgk-frontier fn-lgk-next-txid fn-lgk-batch
                                    fn-lgk-inflight fn-lgk-phase))))))
(local
 (defthm fn-lgu-finishes-acknowledge-n
   (implies (and (natp n) (<= (+ (fn-lgk-acked ks) n) (len (fn-lgk-committed ks))))
            (let ((k2 (fn-lgk-host-run ks (fn-lgu-finishes n))))
              (and (equal (fn-lgk-committed k2) (fn-lgk-committed ks))
                   (equal (fn-lgk-acked k2) (+ (fn-lgk-acked ks) n)))))
   :hints (("Goal" :induct (fn-lgu-finishes-ind n ks)
            :expand ((fn-lgu-finishes n) (fn-lgk-host-run ks nil)
                     (:free (op rest) (fn-lgk-host-run ks (cons op rest))))
            :in-theory (e/d (fn-lgk-host-step)
                            (fn-lgk-finish-one fn-lgk-committed fn-lgk-acked fn-lgk-host-run
                             fn-lgu-finishes))))))
(local
 (defthm fn-lgu-take-of-a-whole-list
   (implies (true-listp x) (equal (take (len x) x) x))))
(local
 (defthm fn-lgu-take-of-a-whole-append
   (implies (and (true-listp a) (true-listp b))
            (equal (take (+ (len a) (len b)) (append a b)) (append a b)))
   :hints (("Goal" :use ((:instance fn-lgu-take-of-a-whole-list (x (append a b))))
            :in-theory (disable fn-lgu-take-of-a-whole-list)))))
(defthm fn-lgu-complete-acknowledges-the-fenced-batch
  (implies (and (equal (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
                (true-listp (fn-lgk-committed ks))
                (true-listp (fn-lgk-inflight ks)))
           (let ((k2 (fn-lgk-host-run (fn-lgk-fence ks unit)
                                      (fn-lgu-finishes (len (fn-lgk-inflight ks))))))
             (equal (take (fn-lgk-acked k2) (fn-lgk-committed k2))
                    (append (fn-lgk-committed ks) (fn-lgk-inflight ks)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgk-fence fn-lgk-fields-of-make)
                           (fn-lgk-make fn-lgk-committed fn-lgk-acked fn-lgk-last fn-lgk-frontier
                            fn-lgk-next-txid fn-lgk-batch fn-lgk-inflight fn-lgk-phase fn-lg-log
                            fn-lg-last-trailer fn-lgk-host-run fn-lgu-finishes
                            fn-lgu-finishes-acknowledge-n))
           :use ((:instance fn-lgu-finishes-acknowledge-n
                            (ks (fn-lgk-fence ks unit)) (n (len (fn-lgk-inflight ks))))))))

; -----------------------------------------------------------------------------
; 8. The host's acknowledgement is one ACL2 call (lane m1-durable-2;
; DI-OWED-STEP-OF-LGC-FINISH).  host/native/io.lisp fnn-log-finish used to
; call fn-lgc-finish-one COUNT times in a Lisp loop, and no theorem equated
; that loop to the fold the keystones are about (:step-of fn-lgc-host-run).
; Now the host calls fn-lgu-acknowledge once: the fold of COUNT
; :finish-one operations by definition (its :exec is the loop,
; fn-lgu-acknowledge-loop-is-the-run), and the KEYSTONE
; fn-lgu-acknowledge-acknowledges-only-recoverable-records is
; fn-lgu-host-kernel-acknowledges-only-recoverable-records over the run
; that ends with the COMPLETE's COUNT acknowledgements, stated over the
; function the host calls.

(defun fn-lgu-acknowledge-loop (c n)
  (declare (xargs :guard (and (true-listp c) (natp n))))
  (if (zp n) c (fn-lgu-acknowledge-loop (fn-lgc-finish-one c) (1- n))))

(defthm fn-lgu-acknowledge-loop-is-the-run
  (equal (fn-lgu-acknowledge-loop c n) (fn-lgc-host-run c (fn-lgu-finishes n)))
  :hints (("Goal" :induct (fn-lgu-acknowledge-loop c n)
           :in-theory (e/d (fn-lgc-host-step) (fn-lgc-finish-one)))))

(defun fn-lgu-acknowledge (c n)
  (declare (xargs :guard (and (true-listp c) (natp n))
                  :guard-hints (("Goal" :in-theory (disable fn-lgu-acknowledge-loop)))))
  (mbe :logic (fn-lgc-host-run c (fn-lgu-finishes n))
       :exec (fn-lgu-acknowledge-loop c n)))

(local
 (defthm fn-lgu-lgc-host-run-of-append
   (equal (fn-lgc-host-run c (append x y)) (fn-lgc-host-run (fn-lgc-host-run c x) y))
   :hints (("Goal" :induct (fn-lgc-host-run c x) :in-theory (disable fn-lgc-host-step)))))

(local
 (defthm fn-lgu-host-final-of-append
   (equal (fn-lgu-host-final bs ks (append x y) ino max)
          (let ((f (fn-lgu-host-final bs ks x ino max)))
            (fn-lgu-host-final (car f) (cdr f) y ino max)))
   :hints (("Goal" :induct (fn-lgu-host-final bs ks x ino max)
            :in-theory (disable fn-lgu-host-step)))))

(local
 (defthm fn-lgu-host-kops-of-append
   (equal (fn-lgu-host-kops bs ks (append x y) ino max)
          (let ((f (fn-lgu-host-final bs ks x ino max)))
            (append (fn-lgu-host-kops bs ks x ino max)
                    (fn-lgu-host-kops (car f) (cdr f) y ino max))))
   :hints (("Goal" :induct (fn-lgu-host-final bs ks x ino max)
            :in-theory (disable fn-lgu-host-step fn-lgu-step-kops)))))

(local
 (defthm fn-lgu-step-kops-of-finish-one
   (equal (fn-lgu-step-kops bs ks '(:finish-one) ino max) '((:finish-one)))
   :hints (("Goal" :in-theory (enable fn-lgu-step-kops fn-lgu-kernel-op-p)))))
(local
 (defthm fn-lgu-host-step-of-finish-one-bs
   (equal (mv-nth 1 (fn-lgu-host-step bs ks '(:finish-one) ino max)) bs)
   :hints (("Goal" :in-theory (e/d (fn-lgu-host-step fn-lgu-kernel-op-p) (fn-lgk-host-step))))))
(local
 (defun fn-lgu-kops-fin-ind (n bs ks ino max)
   (declare (xargs :guard t :verify-guards nil))
   (if (zp n) (list bs ks)
     (mv-let (pairs bs1 ks1) (fn-lgu-host-step bs ks '(:finish-one) ino max)
       (declare (ignore pairs bs1))
       (fn-lgu-kops-fin-ind (1- n) bs ks1 ino max)))))
(local
 (defthm fn-lgu-host-kops-of-finishes
   (equal (fn-lgu-host-kops bs ks (fn-lgu-finishes n) ino max)
          (fn-lgu-finishes n))
   :hints (("Goal" :induct (fn-lgu-kops-fin-ind n bs ks ino max)
            :expand ((fn-lgu-finishes n)
                     (:free (op rest) (fn-lgu-host-kops bs ks (cons op rest) ino max)))
            :in-theory (union-theories '(fn-lgu-kops-fin-ind fn-lgu-step-kops-of-finish-one
                                         fn-lgu-host-step-of-finish-one-bs zp
                                         car-cons cdr-cons (:executable-counterpart fn-lgu-finishes)
                                         append-to-nil binary-append (:induction fn-lgu-kops-fin-ind)
                                         fn-lgu-host-kops)
                                       (theory 'minimal-theory))))))

; KEYSTONE (M1 at the host's entry).  From an open of a store with nothing
; pending (every crash image), the count the host holds after fnn-log-finish
; (fn-lgu-acknowledge, the one ACL2 call) is the run's acknowledged count;
; every crash image of the store it leaves recovers that many records first;
; and at EVERY cut of the run -- each operation's intermediate states
; included -- the acknowledged records are recovered from every crash image
; of the cut.  Scope: one segment, no rotation; the open is P-LOG-RECOVER
; (RL-01's A2 replaces it, books/store-log-recover-copy.lisp).
(defthm fn-lgu-acknowledge-acknowledges-only-recoverable-records
  (let* ((ks0 (fn-lg-recovered-kernel bs ino genesis max floor))
         (opened (car (last (fn-lg-run bs ks0 (fn-lg-recover-program) nil ino))))
         (run (fn-lgu-host-run (car opened) (cdr opened)
                               (append ops (fn-lgu-finishes n)) ino max))
         (final (fn-lgu-host-final (car opened) (cdr opened)
                                   (append ops (fn-lgu-finishes n)) ino max))
         (host (fn-lgu-acknowledge
                (fn-lgc-host-run (mv-nth 1 (fn-lgc-open s genesis (fn-bs-unit bs) max floor))
                                 (fn-lgu-host-kops (car opened) (cdr opened) ops ino max))
                n)))
    (implies (and (posp (fn-bs-unit bs)) ino (assoc-equal ino (fn-bs-inodes bs))
                  (true-listp (fn-bs-durable-content bs ino))
                  (equal (mod (len (fn-bs-durable-content bs ino)) (fn-bs-unit bs)) 0)
                  (fn-frame-digestp genesis)
                  (null (fn-bs-pending bs))
                  (equal (fn-lgd-octets s) (fn-bs-durable-content bs ino)))
             (and
              ;; the count the host holds after acknowledging is the run's
              (equal (fn-lgc-acked host) (fn-lgk-acked (cdr final)))
              ;; ... and every crash image of the store it leaves recovers it
              (implies (fn-bs-crash-imagep (car final) image)
                       (let ((a (fn-lgc-acked host))
                             (recovered (fn-lgk-committed
                                         (fn-lgk-recover (fn-bs-durable-content image ino)
                                                         genesis (fn-bs-unit (car final)) max next-txid))))
                         (and (<= a (len recovered))
                              (equal (take a recovered) (take a (fn-lgk-committed (cdr final)))))))
              ;; at EVERY cut of the run, its acknowledged records are recovered
              ;; from every crash image of the cut
              (implies (and (member-equal pair run)
                            (fn-bs-crash-imagep (car pair) image))
                       (let ((a (fn-lgk-acked (cdr pair)))
                             (recovered (fn-lgk-committed
                                         (fn-lgk-recover (fn-bs-durable-content image ino)
                                                         genesis (fn-bs-unit (car pair)) max next-txid))))
                         (and (<= a (len recovered))
                              (equal (take a recovered) (take a (fn-lgk-committed (cdr pair))))))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-lgu-acknowledge fn-lgu-host-kops-of-append
                                        fn-lgu-host-kops-of-finishes fn-lgu-lgc-host-run-of-append)
                                      (theory 'minimal-theory))
           :use ((:instance fn-lgu-host-kernel-acknowledges-only-recoverable-records
                            (ops (append ops (fn-lgu-finishes n))))
                 (:instance fn-lgu-host-kernel-acknowledges-only-recoverable-records
                            (ops (append ops (fn-lgu-finishes n)))
                            (image (fn-bs-crash
                                    (car (fn-lgu-host-final
                                          (car (car (last (fn-lg-run bs (fn-lg-recovered-kernel bs ino genesis max floor)
                                                                     (fn-lg-recover-program) nil ino))))
                                          (cdr (car (last (fn-lg-run bs (fn-lg-recovered-kernel bs ino genesis max floor)
                                                                     (fn-lg-recover-program) nil ino))))
                                          (append ops (fn-lgu-finishes n)) ino max))
                                    nil)))
                 (:instance fn-bs-lose-everything-is-an-admissible-image
                            (s (car (fn-lgu-host-final
                                     (car (car (last (fn-lg-run bs (fn-lg-recovered-kernel bs ino genesis max floor)
                                                                (fn-lg-recover-program) nil ino))))
                                     (cdr (car (last (fn-lg-run bs (fn-lg-recovered-kernel bs ino genesis max floor)
                                                                (fn-lg-recover-program) nil ino))))
                                     (append ops (fn-lgu-finishes n)) ino max))))
                 (:instance fn-lgu-open-run-acknowledges-only-recoverable-records
                            (ops (append ops (fn-lgu-finishes n))) (routs nil))))))
