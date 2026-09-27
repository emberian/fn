; fn: the record log's byte programs and their runner (design
; planning/design-2026-09-27-storage-log.md section 4: P-BATCH and
; P-LOG-RECOVER), log-local.
;
; books/byte-store-programs.lisp's step language writes whole files
; (:write-all); the log writes at an offset of one preallocated segment.  A
; new step there would recertify every program book above it, so the log
; has its own two-step language over the same byte model (fn-bs-write,
; fn-bs-fsync-file) and the kernel (books/store-log-kernel.lisp):
;
;   (:write-at :segment :batch)  the kernel's append decides (fn-lgk-append:
;                                refused when a batch is in flight, the
;                                kernel is faulted, or the batch does not fit
;                                the extent) and the one write of
;                                fn-lgk-append-octets at the frontier
;                                (host: fnn-log-pwrite in fnn-log-append);
;   (:fence :segment :batch)     the barrier (fn-bs-fsync-file; host:
;                                fnn-log-fdatasync in fnn-log-fence, fdatasync
;                                on Linux: the preallocated segment's append
;                                changes no size or allocation), then the
;                                kernel's fence, or fence-failed on an error;
;   (:write-at :segment :tail)   recovery's zeroing of [F, end) (one write);
;   (:fence :segment :tail)      its barrier;
;   (:cut name)                  a campaign fault point; no effect.
;
; The programs, each hosted by one function of host/native/io.lisp, with the
; cuts tests/campaign/native_cuts.py LOG_CUTS names:
;
;   fn-lg-append-program    fnn-log-append    log-written
;   fn-lg-fence-program     fnn-log-fence     log-fenced
;   fn-lg-recover-program   fnn-log-recover   log-truncated, log-recovered
;
; Theorems (the subject is the runner the programs name; the host performs
; the same steps in the same order, checked by native_cuts.verify_log_cut_map):
;
;   fn-lg-append-program-keeps-the-relation   from R, every state of the
;       append program's run (outcomes :ok) is R-related to its kernel (a
;       refused append leaves the related state); fn-lg-append-program-
;       appends: when the kernel admits the batch the run reaches
;       log-written with the kernel's append;
;   fn-lg-fence-program-keeps-the-relation    from R, every state of the
;       fence program's run is R-related (the batch committed);
;   fn-lg-recover-program-establishes-the-relation   the recovered kernel
;       (fn-lgt-recover of the durable content) and the store at
;       log-recovered are R-related, under R's establishment hypotheses.
;
; At log-written a crash is T2 lifted (fn-lgk-crash-of-related-state-is-a-
; prefix, PRF-244/245); at log-fenced and log-recovered nothing is pending.
(in-package "ACL2")

(include-book "store-log-txid")

; -----------------------------------------------------------------------------
; The steps and the runner.

(defun fn-lg-step (bs ks step outcome ino)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((unit (fn-bs-unit bs))
         (c (fn-bs-durable-content bs ino))
         (f (fn-lgk-frontier ks)))
    (cond ((equal step '(:write-at :segment :batch))
           (if (or (consp (fn-lgk-inflight ks)) (equal (fn-lgk-phase ks) :fault)
                   (not (fn-lgk-fitsp ks unit (len c))))
               (mv :refused bs ks)
             (mv-let (r bs1) (fn-bs-write bs ino f (fn-lgk-append-octets ks unit) outcome)
               (mv r bs1 (if (equal r :ok) (fn-lgk-append ks unit (len c)) ks)))))
          ((equal step '(:fence :segment :batch))
           (mv-let (r bs1) (fn-bs-fsync-file bs ino outcome)
             (mv r bs1 (if (equal r :ok) (fn-lgk-fence ks unit) (fn-lgk-fence-failed ks)))))
          ((equal step '(:write-at :segment :tail))
           (mv-let (r bs1) (fn-bs-write bs ino f (fn-bs-zeros (- (len c) f)) outcome)
             (mv r bs1 ks)))
          ((equal step '(:fence :segment :tail))
           (mv-let (r bs1) (fn-bs-fsync-file bs ino outcome)
             (mv r bs1 ks)))
          (t (mv :ok bs ks)))))

; Run to the first error, as the host does: the (bs . ks) pair after each
; step, most recent last.  A missing outcome is :ok.
(defun fn-lg-run (bs ks steps outcomes ino)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp steps)
      (mv-let (r bs1 ks1)
        (fn-lg-step bs ks (car steps) (if (consp outcomes) (car outcomes) :ok) ino)
        (cons (cons bs1 ks1)
              (if (equal r :ok) (fn-lg-run bs1 ks1 (cdr steps) (cdr outcomes) ino) nil)))
    nil))

; -----------------------------------------------------------------------------
; The programs.

(defun fn-lg-append-program ()
  (declare (xargs :guard t))
  (list (list :write-at :segment :batch)
        (list :cut "log-written")))

(defun fn-lg-fence-program ()
  (declare (xargs :guard t))
  (list (list :fence :segment :batch)
        (list :cut "log-fenced")))

(defun fn-lg-recover-program ()
  (declare (xargs :guard t))
  (list (list :write-at :segment :tail)
        (list :cut "log-truncated")
        (list :fence :segment :tail)
        (list :cut "log-recovered")))

; -----------------------------------------------------------------------------
; Every state of a run is related.

(defun fn-lg-all-relp (pairs ino genesis max)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pairs)
      (and (consp (car pairs))
           (fn-lgk-relp (car (car pairs)) (cdr (car pairs)) ino genesis max)
           (fn-lg-all-relp (cdr pairs) ino genesis max))
    t))

; No other hypothesis: the runner refuses an append the kernel refuses (a
; batch in flight, a faulted kernel, a batch past the extent), and the
; refused state is the related one.
(defthm fn-lg-append-program-keeps-the-relation
  (implies (fn-lgk-relp bs ks ino genesis max)
           (fn-lg-all-relp (fn-lg-run bs ks (fn-lg-append-program) nil ino)
                           ino genesis max))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-write)
                           (fn-lgk-relp fn-lgk-append fn-lgk-append-octets fn-lgk-fitsp
                            fn-bs-durable-content fn-lgk-frontier fn-lgk-inflight fn-lgk-phase
                            fn-lgk-append-preserves-relation))
           :use ((:instance fn-lgk-append-preserves-relation)))))

(defthm fn-lg-relp-names-an-inode
  (implies (fn-lgk-relp bs ks ino genesis max)
           (assoc-equal ino (fn-bs-inodes bs)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-lgk-relp) (fn-lgk-content-okp)))))

; When the kernel admits the batch, the run reaches log-written with the
; batch in flight (the relation above is not the refusal's alone).
(defthm fn-lg-append-program-appends
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (not (consp (fn-lgk-inflight ks)))
                (not (equal (fn-lgk-phase ks) :fault))
                (fn-lgk-fitsp ks (fn-bs-unit bs) (len (fn-bs-durable-content bs ino))))
           (let ((run (fn-lg-run bs ks (fn-lg-append-program) nil ino)))
             (and (equal (len run) 2)
                  (equal (cdr (car (last run)))
                         (fn-lgk-append ks (fn-bs-unit bs)
                                        (len (fn-bs-durable-content bs ino)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-write)
                           (fn-lgk-relp fn-lgk-append fn-lgk-append-octets fn-lgk-fitsp
                            fn-bs-durable-content fn-lgk-frontier fn-lgk-inflight fn-lgk-phase)))))

(defthm fn-lg-fence-program-keeps-the-relation
  (implies (fn-lgk-relp bs ks ino genesis max)
           (fn-lg-all-relp (fn-lg-run bs ks (fn-lg-fence-program) nil ino)
                           ino genesis max))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-fsync-file)
                           (fn-lgk-relp fn-lgk-fence fn-bs-fence-file fn-bs-durable-content
                            fn-lgk-fence-preserves-relation))
           :use ((:instance fn-lgk-fence-preserves-relation)))))

; The recovered kernel: fn-lgt-recover of the durable content, then the
; program.  Its last state (log-recovered) is related.
(defun fn-lg-recovered-kernel (bs ino genesis max floor)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgt-recover (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max floor))

(defthm fn-lg-recover-program-establishes-the-relation
  (let* ((ks (fn-lg-recovered-kernel bs ino genesis max floor))
         (run (fn-lg-run bs ks (fn-lg-recover-program) nil ino))
         (final (car (last run))))
    (implies (and (posp (fn-bs-unit bs)) ino (assoc-equal ino (fn-bs-inodes bs))
                  (true-listp (fn-bs-durable-content bs ino))
                  (equal (mod (len (fn-bs-durable-content bs ino)) (fn-bs-unit bs)) 0)
                  (fn-frame-digestp genesis)
                  (fn-assume-log-sole-pending-writer bs ino)
                  (not (fn-bs-ops-for-ino (fn-bs-pending bs) ino)))
             (and (equal (len run) 4)
                  (fn-lgk-relp (car final) (cdr final) ino genesis max))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-write fn-bs-fsync-file fn-lgt-recover)
                           (fn-lgk-relp fn-lgk-recover fn-bs-fence-file fn-bs-durable-content
                            fn-lgk-frontier fn-bs-zeros fn-lg-scan
                            fn-lgk-recover-establishes-relation fn-lgt-next-after))
           :use ((:instance fn-lgk-recover-establishes-relation
                            (next-txid (fn-lgt-next-after
                                        (car (fn-lg-scan (fn-bs-durable-content bs ino)
                                                         genesis (fn-bs-unit bs) max))
                                        floor)))))))
