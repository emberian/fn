; The record log's durable acceptance at every crash point (lane byte-model,
; row Q3b of COMPLETE-BEFORE-6.6.0; the resource contract's D4).
;
; The sentence: an article the node acknowledged as accepted is recoverable
; from the bytes on disk at every crash point.  "Acknowledged" is the owner
; batch layer's word (books/owner-batch.lisp: a member of fn-owb-acked, whose
; record the aligned layer places in the kernel's committed records);
; "recoverable from the bytes" is the record log's open: the kernel
; fn-lgk-recover reads from the durable content of the segment
; (fn-lg-scan), and the recovered kernel's committed records hold the
; article's record; "every crash point" is every cut state of the byte
; programs the host runs (books/store-log-programs.lisp fn-lg-run over
; fn-lg-append-program, fn-lg-fence-program and fn-lg-recover-program;
; books/store-log-extend.lisp fn-lg-extend-run over fn-lg-extend-program),
; which tools/native_program_check.py ties to host/native/io.lisp
; fnn-log-append, fnn-log-fence, fnn-log-recover and fnn-log-ensure-extent
; (tests/campaign/native_cuts.py LOG_PROGRAM_HOSTS), and every admissible
; crash image (fn-bs-crash-imagep) of each: the pending writes land as any
; per-unit tear, or not at all; the barrier's failure (the fsyncgate
; outcome) lands the environment's selection and discards the rest.
;
; No trailer assumption.  A record the kernel holds committed lies below
; the frontier, and every pending write of the segment starts at or above
; it: the crash keeps the prefix (fn-bs-crash-of-aligned-append, the shift
; lemma), and the scan reads the prefix's complete chained entries before it
; looks at whatever the tear left (fn-lg-scan-of-complete-append).  The
; trailer assumption A-CRYPTO-TRAILER decides what the scan reads AFTER the
; committed records (T2: a prefix of the batch in flight, or a forgery);
; this book needs only that the committed records are read, so it does not
; use it.  Contrast fn-owb-committed-record-survives-crash, which was
; proved through T2's verdict and carries the platform-tear hypothesis.
;
; The theorems, and what each composes:
;   fn-lgu-committed-record-is-read-from-every-crash-image: at one related
;     state (R, books/store-log-kernel.lisp fn-lgk-relp), with or without a
;     batch in flight, every crash image's scan reads every committed record.
;   fn-lgu-recovered-kernel-holds-the-scan: fn-lgk-recover's committed
;     records are the scan's (so "read by the scan" is "held by the open").
;   ...-survives-every-cut-of-the-append / -the-fence / -a-failed-fence /
;     -the-extension: the cut states of the served programs, from a related
;     state.  The append and the fence keep R at every cut
;     (fn-lg-append-program-keeps-the-relation, fn-lg-fence-program-keeps-
;     the-relation); the failed fence leaves the crash image itself, with
;     nothing pending; the extension's written state is the shift lemma's
;     shape and its fenced state is related (fn-lg-extension-keeps-the-
;     relation).
;   fn-lgu-record-read-at-open-survives-every-cut-of-recovery: the cut
;     states of P-LOG-RECOVER from the kernel the scan gives: the zeroing
;     write lies at the frontier (T3, fn-lg-recovered-frontier-is-the-last-
;     complete-record) and its fence establishes R (fn-lgk-recover-
;     establishes-relation).
;   KEYSTONE fn-lgu-acknowledged-article-is-recoverable-at-every-crash-point:
;     the composition in the owner layer's vocabulary over the served
;     programs' cut states (fn-lgu-crash-point-p), and its recovery half
;     fn-lgu-acknowledged-article-is-recoverable-at-every-cut-of-recovery
;     over the recovered layer (fn-owb-recover).
;
; Teeth: tests/acl2/store-log-durable-tests.lisp (a ground two-record log,
; acknowledged, then each program's cuts under explicit crash choices, and
; one witness per removed hypothesis).

(in-package "ACL2")
(include-book "owner-batch")
(include-book "store-log-programs")
(include-book "store-log-extend")
(include-book "byte-store-invariants")

; -----------------------------------------------------------------------------
; Local arithmetic and list facts.

(local
 (encapsulate ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (defthm fn-lgu-mod-zero-is-times
     (implies (and (natp f) (posp unit) (equal (mod f unit) 0))
              (equal (* (floor f unit) unit) f)))
   (defthm fn-lgu-floor-natp
     (implies (and (natp f) (posp unit))
              (natp (floor f unit)))
     :rule-classes :type-prescription)))

(local
 (defthm fn-lgu-member-of-append-left
   (implies (member-equal x a) (member-equal x (append a b)))))

(local
 (defthm fn-lgu-member-of-true-list-fix
   (implies (member-equal x a) (member-equal x (true-list-fix a)))))

(local
 (defthm fn-lgu-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

; -----------------------------------------------------------------------------
; 1. The scan reads a complete prefix's records whatever follows it.

(defthm fn-lgu-scan-of-a-complete-prefix-reads-its-records
  (implies (and (true-listp d)
                (equal (cdr (fn-lg-scan d prev unit max)) (len d))
                (member-equal r (car (fn-lg-scan d prev unit max))))
           (member-equal r (car (fn-lg-scan (append d x) prev unit max))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lg-scan-of-complete-append))
           :in-theory (disable fn-lg-scan fn-lg-scan-last fn-lg-scan-of-complete-append))))

; -----------------------------------------------------------------------------
; 2. A committed record is read by the scan of every crash image of a
;    related state.

; A batch in flight: the image's content is the prefix below the frontier
; followed by the tear of the batch's write over the zeros (the shift lemma).
(local
 (defthm fn-lgu-image-of-a-batch-in-flight-keeps-the-prefix
   (implies (and (fn-lgk-relp bs ks ino genesis max)
                 (consp (fn-lgk-inflight ks))
                 (fn-bs-crash-imagep bs image))
            (equal (fn-bs-durable-content image ino)
                   (append (fn-bs-take (fn-lgk-frontier ks) (fn-bs-durable-content bs ino))
                           (fn-lg-apply-to
                            (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content bs ino))
                            (fn-lg-pieces ino 0
                                          (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks)
                                                     (fn-bs-unit bs))
                                          (fn-lg-crash-sels bs image) (fn-bs-unit bs))))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories (theory 'minimal-theory) '(car-cons cdr-cons))
            :use ((:instance fn-lgk-relp-gives-the-tear-hypotheses)
                  (:instance fn-lg-log-true-listp
                             (records (fn-lgk-inflight ks)) (prev (fn-lgk-last ks))
                             (unit (fn-bs-unit bs)))
                  (:instance fn-bs-crash-of-aligned-append
                             (s bs) (k (floor (fn-lgk-frontier ks) (fn-bs-unit bs)))
                             (d (fn-bs-take (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                             (z (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                             (w (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks)
                                           (fn-bs-unit bs)))))))))

(local
 (defthm fn-lgu-read-when-a-batch-is-in-flight
   (implies (and (fn-lgk-relp bs ks ino genesis max)
                 (consp (fn-lgk-inflight ks))
                 (member-equal r (fn-lgk-committed ks))
                 (fn-bs-crash-imagep bs image))
            (member-equal r (car (fn-lg-scan (fn-bs-durable-content image ino)
                                             genesis (fn-bs-unit bs) max))))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories (theory 'minimal-theory) '(car-cons cdr-cons))
            :use ((:instance fn-lgk-relp-gives-the-tear-hypotheses)
                  (:instance fn-lgu-image-of-a-batch-in-flight-keeps-the-prefix)
                  (:instance fn-lgu-scan-of-a-complete-prefix-reads-its-records
                             (d (fn-bs-take (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                             (x (fn-lg-apply-to
                                 (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content bs ino))
                                 (fn-lg-pieces ino 0
                                               (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks)
                                                          (fn-bs-unit bs))
                                               (fn-lg-crash-sels bs image) (fn-bs-unit bs))))
                             (prev genesis) (unit (fn-bs-unit bs))))))))

; At rest: nothing is pending, the image's content is the store's.
(local
 (defthm fn-lgu-read-when-at-rest
   (implies (and (fn-lgk-relp bs ks ino genesis max)
                 (not (consp (fn-lgk-inflight ks)))
                 (member-equal r (fn-lgk-committed ks))
                 (fn-bs-crash-imagep bs image))
            (member-equal r (car (fn-lg-scan (fn-bs-durable-content image ino)
                                             genesis (fn-bs-unit bs) max))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lgk-relp fn-lgk-content-okp fn-bs-fencedp fn-bs-ops-for-ino)
                            (fn-lg-scan fn-lg-scan-last fn-lg-log fn-bs-take fn-lg-zerosp
                             fn-lg-recordsp fn-frame-digestp fn-bs-durable-content
                             fn-bs-crash-imagep fn-bs-crash-keeps-fenced-content
                             fn-lgc-take-then-nthcdr fn-lgu-scan-of-a-complete-prefix-reads-its-records
                             mod))
            :use ((:instance fn-bs-crash-keeps-fenced-content (s bs))
                  (:instance fn-lgc-take-then-nthcdr
                             (n (fn-lgk-frontier ks)) (x (fn-bs-durable-content bs ino)))
                  (:instance fn-lgu-scan-of-a-complete-prefix-reads-its-records
                             (d (fn-bs-take (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                             (x (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                             (prev genesis) (unit (fn-bs-unit bs))))))))

(defthm fn-lgu-committed-record-is-read-from-every-crash-image
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (member-equal r (fn-lgk-committed ks))
                (fn-bs-crash-imagep bs image))
           (member-equal r (car (fn-lg-scan (fn-bs-durable-content image ino)
                                            genesis (fn-bs-unit bs) max))))
  :hints (("Goal" :do-not-induct t
           :cases ((consp (fn-lgk-inflight ks)))
           :in-theory (disable fn-lg-scan fn-lgk-relp fn-bs-crash-imagep fn-bs-durable-content
                               fn-lgk-committed fn-lgk-inflight))))

; -----------------------------------------------------------------------------
; 3. The open holds what the scan reads.

(defthm fn-lgu-recovered-kernel-holds-the-scan
  (equal (fn-lgk-committed (fn-lgk-recover c genesis unit max next-txid))
         (car (fn-lg-scan c genesis unit max)))
  :hints (("Goal" :in-theory (e/d (fn-lgk-recover)
                                  (fn-lg-scan fn-lg-scan-last fn-lgk-make fn-lgk-committed)))))

; -----------------------------------------------------------------------------
; 4. The served programs' cut states.

(local
 (defthm fn-lgu-all-relp-member
   (implies (and (fn-lg-all-relp pairs ino genesis max) (member-equal pair pairs))
            (fn-lgk-relp (car pair) (cdr pair) ino genesis max))
   :hints (("Goal" :in-theory (disable fn-lgk-relp)))))

(local
 (defthm fn-lgu-committed-of-append
   (equal (fn-lgk-committed (fn-lgk-append ks unit extent)) (fn-lgk-committed ks))
   :hints (("Goal" :in-theory (e/d (fn-lgk-append) (fn-lgk-make fn-lgk-committed fn-lgk-fitsp))))))

(local
 (defthm fn-lgu-committed-of-fence
   (implies (true-listp (fn-lgk-committed ks))
            (equal (fn-lgk-committed (fn-lgk-fence ks unit))
                   (append (fn-lgk-committed ks) (true-list-fix (fn-lgk-inflight ks)))))
   :hints (("Goal" :in-theory (e/d (fn-lgk-fence) (fn-lgk-make fn-lgk-committed fn-lg-log))))))

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

(local
 (defthm fn-lgu-relp-committed-true-listp
   (implies (fn-lgk-relp bs ks ino genesis max)
            (true-listp (fn-lgk-committed ks)))
   :hints (("Goal" :in-theory (e/d (fn-lgk-relp fn-lgk-content-okp)
                                   (fn-lg-scan fn-lg-scan-last fn-lg-log fn-bs-take
                                    fn-lg-zerosp fn-lg-recordsp fn-frame-digestp))))))

; The append's cut states: related, the committed records the same, the
; unit the store's.
(local
 (defthm fn-lgu-append-run-pairs
   (implies (and (fn-lgk-relp bs ks ino genesis max)
                 (member-equal pair (fn-lg-run bs ks (fn-lg-append-program) nil ino)))
            (and (fn-lgk-relp (car pair) (cdr pair) ino genesis max)
                 (equal (fn-lgk-committed (cdr pair)) (fn-lgk-committed ks))
                 (equal (fn-bs-unit (car pair)) (fn-bs-unit bs))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-lg-append-program-keeps-the-relation))
            :in-theory (e/d (fn-lg-run fn-lg-step fn-lg-append-program)
                            (fn-lgk-relp fn-lgk-append fn-lgk-append-octets fn-lgk-fitsp
                             fn-bs-durable-content fn-lgk-frontier fn-lgk-inflight fn-lgk-phase
                             fn-lg-append-admitsp fn-bs-write fn-lgk-committed
                             fn-lg-append-program-keeps-the-relation))))))

(defthm fn-lgu-committed-record-survives-every-cut-of-the-append
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (member-equal r (fn-lgk-committed ks))
                (member-equal pair (fn-lg-run bs ks (fn-lg-append-program) nil ino))
                (fn-bs-crash-imagep (car pair) image))
           (member-equal r (car (fn-lg-scan (fn-bs-durable-content image ino)
                                            genesis (fn-bs-unit bs) max))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgu-append-run-pairs)
                 (:instance fn-lgu-committed-record-is-read-from-every-crash-image
                            (bs (car pair)) (ks (cdr pair))))
           :in-theory (disable fn-lg-scan fn-lgk-relp fn-bs-crash-imagep fn-bs-durable-content
                               fn-lgk-committed fn-lg-run fn-lg-append-program
                               fn-lgu-committed-record-is-read-from-every-crash-image))))

; The fence's cut states when the barrier returns :ok.
(local
 (defthm fn-lgu-fsync-ok-result
   (and (equal (mv-nth 0 (fn-bs-fsync-file s ino :ok)) :ok)
        (equal (car (fn-bs-fsync-file s ino :ok)) :ok))
   :hints (("Goal" :in-theory (enable fn-bs-fsync-file)))))

; The fence's run, computed: the fenced store and the fenced kernel, twice
; (the barrier, then the cut).
(local
 (defthm fn-lgu-fence-run-computed
   (equal (fn-lg-run bs ks (fn-lg-fence-program) nil ino)
          (let ((pair (cons (mv-nth 1 (fn-bs-fsync-file bs ino :ok))
                            (fn-lgk-fence ks (fn-bs-unit bs)))))
            (list pair pair)))
   :hints (("Goal" :in-theory (e/d (fn-lg-run fn-lg-step fn-lg-fence-program)
                                   (fn-lgk-fence fn-lgk-fence-failed fn-bs-fsync-file
                                    fn-bs-durable-content fn-lgk-frontier fn-bs-fence-file
                                    fn-lgk-make))))))

(local
 (defthm fn-lgu-fence-run-pairs
   (implies (and (fn-lgk-relp bs ks ino genesis max)
                 (member-equal pair (fn-lg-run bs ks (fn-lg-fence-program) nil ino)))
            (and (fn-lgk-relp (car pair) (cdr pair) ino genesis max)
                 (equal (fn-lgk-committed (cdr pair))
                        (append (fn-lgk-committed ks) (true-list-fix (fn-lgk-inflight ks))))
                 (equal (fn-bs-unit (car pair)) (fn-bs-unit bs))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-lg-fence-program-keeps-the-relation)
                  (:instance fn-lgu-relp-committed-true-listp))
            :in-theory (e/d (fn-lg-all-relp)
                            (fn-lgk-relp fn-lgk-fence fn-lgk-fence-failed fn-bs-durable-content
                             fn-lgk-frontier fn-lgk-inflight fn-lgk-phase fn-bs-fsync-file
                             fn-lgk-committed fn-lgk-make fn-lg-run fn-lg-fence-program
                             (:executable-counterpart fn-lg-fence-program)
                             fn-lg-fence-program-keeps-the-relation
                             fn-lgu-relp-committed-true-listp))))))

(defthm fn-lgu-committed-record-survives-every-cut-of-the-fence
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (member-equal r (fn-lgk-committed ks))
                (member-equal pair (fn-lg-run bs ks (fn-lg-fence-program) nil ino))
                (fn-bs-crash-imagep (car pair) image))
           (member-equal r (car (fn-lg-scan (fn-bs-durable-content image ino)
                                            genesis (fn-bs-unit bs) max))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgu-fence-run-pairs)
                 (:instance fn-lgu-committed-record-is-read-from-every-crash-image
                            (bs (car pair)) (ks (cdr pair))))
           :in-theory (disable fn-lg-scan fn-lgk-relp fn-bs-crash-imagep fn-bs-durable-content
                               fn-lgk-committed fn-lgk-inflight fn-lg-run fn-lg-fence-program
                               fn-lgu-committed-record-is-read-from-every-crash-image))))

; The failed barrier: the environment's selection of the batch's write
; lands and the rest is discarded (fn-bs-fsync-file's error arm); the store
; the failure leaves is the crash image of that selection, with nothing of
; the segment pending, so its own crash images keep its content.
(local
 (defthm fn-lgu-crash-select-of-ops-for-ino
   (implies (not (fn-bs-ops-not-for-ino ops ino))
            (equal (fn-bs-crash-select (fn-bs-ops-for-ino ops ino) choices unit)
                   (fn-bs-crash-select ops choices unit)))
   :hints (("Goal" :in-theory (enable fn-bs-crash-select fn-bs-ops-for-ino fn-bs-ops-not-for-ino)))))

(local
 (defthm fn-lgu-failed-fence-is-the-crash-image
   (implies (and (not (fn-bs-ops-not-for-ino (fn-bs-pending bs) ino))
                 (consp outcome) (not (equal (car outcome) :ok)))
            (equal (mv-nth 1 (fn-bs-fsync-file bs ino outcome))
                   (fn-bs-crash bs (cdr outcome))))
   :hints (("Goal" :in-theory (e/d (fn-bs-fsync-file fn-bs-crash)
                                   (fn-bs-apply-ops fn-bs-crash-select fn-bs-make
                                    fn-bs-ops-for-ino fn-bs-ops-not-for-ino))))))

(local
 (defthm fn-lgu-ops-for-ino-of-not-for-ino
   (equal (fn-bs-ops-for-ino (fn-bs-ops-not-for-ino ops ino) ino) nil)))

(local
 (defthm fn-lgu-ops-for-ino-of-nil
   (equal (fn-bs-ops-for-ino nil ino) nil)))

(local
 (defthm fn-lgu-relp-pending-names-only-the-segment
   (implies (fn-lgk-relp bs ks ino genesis max)
            (not (fn-bs-ops-not-for-ino (fn-bs-pending bs) ino)))
   :hints (("Goal" :in-theory (e/d (fn-lgk-relp fn-bs-ops-not-for-ino)
                                   (fn-lgk-content-okp fn-lg-log fn-bs-durable-content))))))

(local
 (defthm fn-lgu-failed-fence-run
   (implies (and (consp outcome) (not (equal (car outcome) :ok)))
            (equal (fn-lg-run bs ks (fn-lg-fence-program) (list outcome) ino)
                   (list (cons (mv-nth 1 (fn-bs-fsync-file bs ino outcome))
                               (fn-lgk-fence-failed ks)))))
   :hints (("Goal" :in-theory (e/d (fn-lg-run fn-lg-step fn-lg-fence-program fn-bs-fsync-file)
                                   (fn-lgk-fence fn-lgk-fence-failed fn-bs-fence-file
                                    fn-bs-apply-ops fn-bs-crash-select fn-bs-make
                                    fn-bs-ops-for-ino fn-bs-ops-not-for-ino))))))

(local
 (defthm fn-lgu-pending-of-failed-fence
   (implies (and (consp outcome) (not (equal (car outcome) :ok)))
            (equal (fn-bs-pending (mv-nth 1 (fn-bs-fsync-file bs ino outcome)))
                   (fn-bs-ops-not-for-ino (fn-bs-pending bs) ino)))
   :hints (("Goal" :in-theory (e/d (fn-bs-fsync-file)
                                   (fn-bs-apply-ops fn-bs-crash-select fn-bs-ops-not-for-ino))))))

(defthm fn-lgu-committed-record-survives-every-cut-of-a-failed-fence
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (member-equal r (fn-lgk-committed ks))
                (consp outcome) (not (equal (car outcome) :ok))
                (fn-bs-crash-choicesp (cdr outcome) (fn-bs-pending bs) (fn-bs-unit bs))
                (member-equal pair (fn-lg-run bs ks (fn-lg-fence-program) (list outcome) ino))
                (fn-bs-crash-imagep (car pair) image))
           (member-equal r (car (fn-lg-scan (fn-bs-durable-content image ino)
                                            genesis (fn-bs-unit bs) max))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgu-relp-pending-names-only-the-segment)
                 (:instance fn-lgu-failed-fence-run)
                 (:instance fn-lgu-failed-fence-is-the-crash-image)
                 (:instance fn-bs-crash-imagep-suff
                            (s bs) (choices (cdr outcome)) (image (fn-bs-crash bs (cdr outcome))))
                 (:instance fn-lgu-committed-record-is-read-from-every-crash-image
                            (image (fn-bs-crash bs (cdr outcome))))
                 (:instance fn-bs-crash-keeps-fenced-content
                            (s (fn-bs-crash bs (cdr outcome))))
                 (:instance fn-lgu-pending-of-failed-fence))
           :in-theory (e/d (fn-bs-fencedp)
                           (fn-lg-scan fn-lgk-relp fn-bs-crash-imagep fn-bs-durable-content
                            fn-lgk-committed fn-lgk-inflight fn-lg-run fn-lg-fence-program
                            (:executable-counterpart fn-lg-fence-program)
                            fn-bs-fsync-file fn-bs-crash fn-bs-crash-choicesp
                            fn-bs-ops-for-ino fn-bs-ops-not-for-ino fn-bs-crash-imagep-suff
                            fn-lgu-committed-record-is-read-from-every-crash-image
                            fn-bs-crash-keeps-fenced-content
                            fn-lgu-failed-fence-is-the-crash-image fn-lgu-pending-of-failed-fence)))))

; The extension's cut states: the written state (its zeros pending at the
; segment's end, the shift lemma's shape with the whole content as the
; prefix) and the fenced state (related, fn-lg-extension-keeps-the-relation).
(local
 (defthm fn-lgu-relp-at-rest-pending
   (implies (and (fn-lgk-relp bs ks ino genesis max) (not (consp (fn-lgk-inflight ks))))
            (equal (fn-bs-pending bs) nil))
   :hints (("Goal" :in-theory (e/d (fn-lgk-relp) (fn-lgk-content-okp fn-lg-log fn-bs-durable-content))))))

(local
 (defthm fn-lgu-relp-content-facts
   (implies (fn-lgk-relp bs ks ino genesis max)
            (let ((c (fn-bs-durable-content bs ino)) (f (fn-lgk-frontier ks))
                  (unit (fn-bs-unit bs)))
              (and (posp unit) ino (assoc-equal ino (fn-bs-inodes bs))
                   (true-listp c) (equal (mod (len c) unit) 0)
                   (natp f) (<= f (len c))
                   (equal (fn-lg-scan (fn-bs-take f c) genesis unit max)
                          (cons (fn-lgk-committed ks) f)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-lgk-relp fn-lgk-content-okp)
                                   (fn-lg-scan fn-lg-scan-last fn-lg-log fn-bs-take fn-lg-zerosp
                                    fn-lg-recordsp fn-frame-digestp fn-bs-durable-content mod))))))

(local
 (defthm fn-lgu-zeros-true-listp (true-listp (fn-bs-zeros n))))

(local
 (defthm fn-lgu-take-of-zeros
   (implies (natp n)
            (equal (fn-bs-take n (fn-bs-zeros n)) (fn-bs-zeros n)))
   :hints (("Goal" :use ((:instance fn-lgc-take-all (a (fn-bs-zeros n)) (n n)))
            :in-theory (e/d (fn-lgc-take-all fn-lgc-zeros-len) (fn-bs-zeros fn-bs-take))))))

; The shift lemma with its alignment stated as the kernel states it (a
; zero remainder), proved where nothing normalizes the arithmetic.
(local
 (defthm fn-lgu-crash-of-aligned-append-by-mod
   (implies (and (posp (fn-bs-unit s)) ino (true-listp d) (true-listp w)
                 (equal (mod (len d) (fn-bs-unit s)) 0)
                 (equal (fn-bs-durable-content s ino) (append d z))
                 (equal (fn-bs-pending s) (list (list :write ino (len d) w)))
                 (fn-bs-crash-imagep s image))
            (equal (fn-bs-durable-content image ino)
                   (append d (fn-lg-apply-to z (fn-lg-pieces ino 0 w (fn-lg-crash-sels s image)
                                                            (fn-bs-unit s))))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bs-crash-of-aligned-append (k (floor (len d) (fn-bs-unit s))))
                  (:instance fn-lgu-mod-zero-is-times (f (len d)) (unit (fn-bs-unit s)))
                  (:instance fn-lgu-floor-natp (f (len d)) (unit (fn-bs-unit s))))
            :in-theory (union-theories '(car-cons cdr-cons natp posp (:type-prescription len))
                                       (theory 'minimal-theory))))))

; A crash image of the written state keeps the old content: the zeros are
; written at its end.
(local
 (defthm fn-lgu-extension-image-keeps-the-content
   (implies (and (fn-lgk-relp bs ks ino genesis max)
                 (not (consp (fn-lgk-inflight ks)))
                 (< (len (fn-bs-durable-content bs ino)) (nfix next))
                 (fn-bs-crash-imagep (fn-lg-extension-written-state bs ino next) image))
            (equal (fn-bs-durable-content image ino)
                   (append (fn-bs-durable-content bs ino)
                           (fn-lg-apply-to nil
                                           (fn-lg-pieces ino 0
                                                         (fn-bs-zeros (- (nfix next)
                                                                         (len (fn-bs-durable-content bs ino))))
                                                         (fn-lg-crash-sels
                                                          (fn-lg-extension-written-state bs ino next) image)
                                                         (fn-bs-unit bs))))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-lgu-relp-content-facts)
                  (:instance fn-lgu-relp-at-rest-pending)
                  (:instance fn-lgu-crash-of-aligned-append-by-mod
                             (s (fn-lg-extension-written-state bs ino next))
                             (d (fn-bs-durable-content bs ino))
                             (z nil)
                             (w (fn-bs-zeros (- (nfix next) (len (fn-bs-durable-content bs ino)))))))
            :in-theory (e/d (fn-lg-extension-written-state fn-bs-write fn-bs-durable-content)
                            (fn-lgk-relp fn-bs-zeros fn-lg-apply-to fn-lg-pieces fn-bs-crash-imagep
                             fn-lg-crash-sels fn-bs-crash-of-aligned-append fn-bs-take
                             fn-lgk-frontier fn-lgk-inflight fn-lgk-committed mod floor
                             fn-lgu-mod-zero-is-times fn-lgu-relp-at-rest-pending))))))

; A content split at an offset within it, in the direction the used
; instances need (the prefix's records, then the rest and the tear).
(local
 (defthm fn-lgu-split-append
   (implies (and (true-listp c) (natp f) (<= f (len c)))
            (equal (append (fn-bs-take f c) (append (nthcdr f c) x))
                   (append c x)))
   :hints (("Goal" :induct (nthcdr f c)
            :in-theory (e/d (fn-bs-take) (fn-lgu-append-assoc))))))

(local
 (defthm fn-lgu-read-from-an-image-of-the-written-state
   (implies (and (fn-lgk-relp bs ks ino genesis max)
                 (not (consp (fn-lgk-inflight ks)))
                 (member-equal r (fn-lgk-committed ks))
                 (< (len (fn-bs-durable-content bs ino)) (nfix next))
                 (fn-bs-crash-imagep (fn-lg-extension-written-state bs ino next) image))
            (member-equal r (car (fn-lg-scan (fn-bs-durable-content image ino)
                                             genesis (fn-bs-unit bs) max))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-lgu-relp-content-facts)
                  (:instance fn-lgu-extension-image-keeps-the-content)
                  (:instance fn-lgu-scan-of-a-complete-prefix-reads-its-records
                             (d (fn-bs-take (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                             (x (append (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content bs ino))
                                        (fn-lg-apply-to nil
                                                        (fn-lg-pieces ino 0
                                                                      (fn-bs-zeros (- (nfix next)
                                                                                      (len (fn-bs-durable-content bs ino))))
                                                                      (fn-lg-crash-sels
                                                                       (fn-lg-extension-written-state bs ino next) image)
                                                                      (fn-bs-unit bs)))))
                             (prev genesis) (unit (fn-bs-unit bs))))
            :in-theory (e/d (fn-lgu-split-append)
                            (fn-lg-scan fn-lgk-relp fn-bs-crash-imagep fn-bs-durable-content
                             fn-lgk-committed fn-lgk-inflight fn-lgk-frontier fn-bs-take
                             fn-lg-apply-to fn-lg-pieces fn-bs-zeros fn-lg-crash-sels
                             fn-lg-extension-written-state fn-lgc-take-then-nthcdr
                             fn-lgu-append-assoc
                             fn-lgu-scan-of-a-complete-prefix-reads-its-records mod floor))))))

; The extension run's four states are the written state (twice) and the
; extended state (twice): a crash image of a cut state is one of theirs.
(local
 (defthm fn-lgu-extend-run-pairs
   (implies (and (null (fn-bs-pending bs)) (assoc-equal ino (fn-bs-inodes bs))
                 (true-listp (fn-bs-durable-content bs ino))
                 (< (len (fn-bs-durable-content bs ino)) (nfix next))
                 (member-equal pair (fn-lg-extend-run bs ks (fn-lg-extend-program next) nil ino))
                 (fn-bs-crash-imagep (car pair) image))
            (or (fn-bs-crash-imagep (fn-lg-extension-written-state bs ino next) image)
                (fn-bs-crash-imagep (fn-lg-extended-state bs ino next) image)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-lg-extend-run-is-the-extended-state)
                  (:instance fn-lg-extend-run-writes-first))
            :in-theory (e/d (fn-lg-extend-run fn-lg-extend-step fn-lg-extend-program)
                            (fn-lg-extension-written-state fn-lg-extended-state fn-bs-write
                             fn-bs-fsync-file fn-bs-durable-content fn-bs-zeros fn-bs-crash-imagep
                             fn-lg-extend-run-is-the-extended-state fn-lg-extend-run-writes-first))))))

(local
 (defthm fn-lgu-unit-of-extended-state
   (equal (fn-bs-unit (fn-lg-extended-state bs ino next)) (fn-bs-unit bs))
   :hints (("Goal" :in-theory (enable fn-lg-extended-state)))))

(defthm fn-lgu-committed-record-survives-every-cut-of-the-extension
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (not (consp (fn-lgk-inflight ks)))
                (member-equal r (fn-lgk-committed ks))
                (natp next)
                (equal (mod next (fn-bs-unit bs)) 0)
                (< (len (fn-bs-durable-content bs ino)) next)
                (member-equal pair (fn-lg-extend-run bs ks (fn-lg-extend-program next) nil ino))
                (fn-bs-crash-imagep (car pair) image))
           (member-equal r (car (fn-lg-scan (fn-bs-durable-content image ino)
                                            genesis (fn-bs-unit bs) max))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgu-relp-content-facts)
                 (:instance fn-lgu-relp-at-rest-pending)
                 (:instance fn-lgu-extend-run-pairs)
                 (:instance fn-lgu-read-from-an-image-of-the-written-state)
                 (:instance fn-lg-extension-keeps-the-relation)
                 (:instance fn-lgu-committed-record-is-read-from-every-crash-image
                            (bs (fn-lg-extended-state bs ino next))))
           :in-theory (union-theories '(car-cons cdr-cons natp nfix fn-lgu-unit-of-extended-state)
                                      (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; 5. P-LOG-RECOVER's cut states, from the kernel the scan gives.

(local
 (defthm fn-lgu-no-ops-either-way-is-atom
   (implies (and (not (fn-bs-ops-for-ino ops ino)) (not (fn-bs-ops-not-for-ino ops ino)))
            (atom ops))
   :rule-classes nil))

; The zeroing write's pending list, and the state it leaves.
(local
 (defthm fn-lgu-recovery-write-pending
   (implies (and (atom (fn-bs-pending bs)) (assoc-equal ino (fn-bs-inodes bs)))
            (let ((bs1 (mv-nth 1 (fn-bs-write bs ino f octets :ok))))
              (and (equal (fn-bs-durable-content bs1 ino) (fn-bs-durable-content bs ino))
                   (equal (fn-bs-unit bs1) (fn-bs-unit bs))
                   (equal (fn-bs-pending bs1)
                          (if (zp (len octets)) (fn-bs-pending bs)
                            (list (list :write ino f (fn-bs-take (len octets) octets))))))))
   :hints (("Goal" :in-theory (e/d (fn-bs-write fn-bs-durable-content) (fn-bs-take))))))

; The scan's frontier: aligned, within, the scan of the prefix the scan
; (T3), restated with the natural number the kernel carries.
(local
 (defthm fn-lgu-frontier-facts
   (implies (and (posp unit) (true-listp c) (equal (mod (len c) unit) 0))
            (let ((f (cdr (fn-lg-scan c genesis unit max))))
              (and (natp f) (<= f (len c)) (equal (mod f unit) 0)
                   (equal (fn-lg-scan (fn-bs-take f c) genesis unit max)
                          (fn-lg-scan c genesis unit max)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-lg-recovered-frontier-is-the-last-complete-record)
                         (:instance fn-lg-scan-consumed-aligned (x c) (prev genesis)))
            :in-theory (disable fn-lg-scan fn-lg-scan-last mod)))))

; The zeroing write pending (something to zero): the shift lemma over the
; scanned prefix.
(local
 (defthm fn-lgu-truncating-image-with-zeros-pending
   (let* ((c (fn-bs-durable-content bs ino)) (unit (fn-bs-unit bs))
          (f (cdr (fn-lg-scan c genesis unit max)))
          (bs1 (mv-nth 1 (fn-bs-write bs ino f (fn-bs-zeros (- (len c) f)) :ok))))
     (implies (and (posp unit) ino (assoc-equal ino (fn-bs-inodes bs))
                   (true-listp c) (equal (mod (len c) unit) 0)
                   (atom (fn-bs-pending bs))
                   (< f (len c))
                   (member-equal r (car (fn-lg-scan c genesis unit max)))
                   (fn-bs-crash-imagep bs1 image))
              (member-equal r (car (fn-lg-scan (fn-bs-durable-content image ino)
                                               genesis unit max)))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-lgu-frontier-facts (c (fn-bs-durable-content bs ino)) (unit (fn-bs-unit bs)))
                  (:instance fn-lgu-recovery-write-pending
                             (f (cdr (fn-lg-scan (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max)))
                             (octets (fn-bs-zeros (- (len (fn-bs-durable-content bs ino))
                                                     (cdr (fn-lg-scan (fn-bs-durable-content bs ino)
                                                                      genesis (fn-bs-unit bs) max))))))
                  (:instance fn-lgu-crash-of-aligned-append-by-mod
                             (s (mv-nth 1 (fn-bs-write bs ino
                                                       (cdr (fn-lg-scan (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max))
                                                       (fn-bs-zeros (- (len (fn-bs-durable-content bs ino))
                                                                       (cdr (fn-lg-scan (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max))))
                                                       :ok)))
                             (d (fn-bs-take (cdr (fn-lg-scan (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max))
                                            (fn-bs-durable-content bs ino)))
                             (z (nthcdr (cdr (fn-lg-scan (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max))
                                        (fn-bs-durable-content bs ino)))
                             (w (fn-bs-zeros (- (len (fn-bs-durable-content bs ino))
                                                (cdr (fn-lg-scan (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max))))))
                  (:instance fn-lgc-take-then-nthcdr
                             (n (cdr (fn-lg-scan (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max)))
                             (x (fn-bs-durable-content bs ino)))
                  (:instance fn-lgu-scan-of-a-complete-prefix-reads-its-records
                             (d (fn-bs-take (cdr (fn-lg-scan (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max))
                                            (fn-bs-durable-content bs ino)))
                             (x (fn-lg-apply-to
                                 (nthcdr (cdr (fn-lg-scan (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max))
                                         (fn-bs-durable-content bs ino))
                                 (fn-lg-pieces ino 0
                                               (fn-bs-zeros (- (len (fn-bs-durable-content bs ino))
                                                               (cdr (fn-lg-scan (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max))))
                                               (fn-lg-crash-sels
                                                (mv-nth 1 (fn-bs-write bs ino
                                                                       (cdr (fn-lg-scan (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max))
                                                                       (fn-bs-zeros (- (len (fn-bs-durable-content bs ino))
                                                                                       (cdr (fn-lg-scan (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max))))
                                                                       :ok))
                                                image)
                                               (fn-bs-unit bs))))
                             (prev genesis) (unit (fn-bs-unit bs))))
            :in-theory (e/d () (fn-lg-scan fn-lg-scan-last fn-bs-take fn-bs-zeros fn-bs-write
                                fn-bs-durable-content fn-bs-crash-imagep fn-lg-apply-to fn-lg-pieces
                                fn-lg-crash-sels mod floor fn-lgc-take-then-nthcdr
                                fn-lgu-scan-of-a-complete-prefix-reads-its-records
                                fn-lgu-recovery-write-pending fn-lgu-mod-zero-is-times))))))

; Nothing to zero (the scan consumed the whole content): the write adds no
; pending operation and the image keeps the content.
(local
 (defthm fn-lgu-truncating-image-with-nothing-pending
   (let* ((c (fn-bs-durable-content bs ino)) (unit (fn-bs-unit bs))
          (f (cdr (fn-lg-scan c genesis unit max)))
          (bs1 (mv-nth 1 (fn-bs-write bs ino f (fn-bs-zeros (- (len c) f)) :ok))))
     (implies (and (posp unit) ino (assoc-equal ino (fn-bs-inodes bs))
                   (true-listp c) (equal (mod (len c) unit) 0)
                   (atom (fn-bs-pending bs))
                   (equal f (len c))
                   (member-equal r (car (fn-lg-scan c genesis unit max)))
                   (fn-bs-crash-imagep bs1 image))
              (member-equal r (car (fn-lg-scan (fn-bs-durable-content image ino)
                                               genesis unit max)))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-lgu-recovery-write-pending
                             (f (cdr (fn-lg-scan (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max)))
                             (octets (fn-bs-zeros (- (len (fn-bs-durable-content bs ino))
                                                     (cdr (fn-lg-scan (fn-bs-durable-content bs ino)
                                                                      genesis (fn-bs-unit bs) max))))))
                  (:instance fn-bs-crash-keeps-fenced-content
                             (s (mv-nth 1 (fn-bs-write bs ino
                                                       (cdr (fn-lg-scan (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max))
                                                       (fn-bs-zeros (- (len (fn-bs-durable-content bs ino))
                                                                       (cdr (fn-lg-scan (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max))))
                                                       :ok)))))
            :in-theory (e/d (fn-bs-fencedp fn-bs-ops-for-ino)
                            (fn-lg-scan fn-lg-scan-last fn-bs-take fn-bs-zeros fn-bs-write
                             fn-bs-durable-content fn-bs-crash-imagep mod
                             fn-bs-crash-keeps-fenced-content fn-lgu-recovery-write-pending))))))

(local
 (defthm fn-lgu-read-from-an-image-of-the-truncating-state
   (let* ((c (fn-bs-durable-content bs ino)) (unit (fn-bs-unit bs))
          (f (cdr (fn-lg-scan c genesis unit max)))
          (bs1 (mv-nth 1 (fn-bs-write bs ino f (fn-bs-zeros (- (len c) f)) :ok))))
     (implies (and (posp unit) ino (assoc-equal ino (fn-bs-inodes bs))
                   (true-listp c) (equal (mod (len c) unit) 0)
                   (atom (fn-bs-pending bs))
                   (member-equal r (car (fn-lg-scan c genesis unit max)))
                   (fn-bs-crash-imagep bs1 image))
              (member-equal r (car (fn-lg-scan (fn-bs-durable-content image ino)
                                               genesis unit max)))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-lgu-frontier-facts (c (fn-bs-durable-content bs ino)) (unit (fn-bs-unit bs)))
                  (:instance fn-lgu-truncating-image-with-zeros-pending)
                  (:instance fn-lgu-truncating-image-with-nothing-pending))
            :in-theory (disable fn-lg-scan fn-lg-scan-last fn-bs-take fn-bs-zeros fn-bs-write
                                fn-bs-durable-content fn-bs-crash-imagep mod
                                fn-lgu-truncating-image-with-zeros-pending
                                fn-lgu-truncating-image-with-nothing-pending)))))

; The recovery run's states: the truncating state (twice) and the fenced
; state (twice), the kernel throughout: a crash image of a cut state is one
; of theirs.
(local
 (defthm fn-lgu-recover-run-pairs
   (let* ((c (fn-bs-durable-content bs ino)) (f (fn-lgk-frontier ks))
          (bs1 (mv-nth 1 (fn-bs-write bs ino f (fn-bs-zeros (- (len c) f)) :ok)))
          (bs2 (mv-nth 1 (fn-bs-fsync-file bs1 ino :ok))))
     (implies (and (assoc-equal ino (fn-bs-inodes bs))
                   (member-equal pair (fn-lg-run bs ks (fn-lg-recover-program) nil ino))
                   (fn-bs-crash-imagep (car pair) image))
              (or (fn-bs-crash-imagep bs1 image) (fn-bs-crash-imagep bs2 image))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lg-run fn-lg-step fn-lg-recover-program)
                            (fn-bs-write fn-bs-fsync-file fn-bs-durable-content fn-bs-zeros
                             fn-lgk-frontier fn-bs-crash-imagep))))))

; The recovered kernel's frontier is the scan's.
(local
 (defthm fn-lgu-frontier-of-recover
   (implies (natp (cdr (fn-lg-scan c genesis unit max)))
            (equal (fn-lgk-frontier (fn-lgk-recover c genesis unit max next-txid))
                   (cdr (fn-lg-scan c genesis unit max))))
   :hints (("Goal" :in-theory (e/d (fn-lgk-recover) (fn-lg-scan fn-lg-scan-last fn-lgk-make
                                                      fn-lgk-frontier))))))

(defthm fn-lgu-record-read-at-open-survives-every-cut-of-recovery
  (let* ((c (fn-bs-durable-content bs ino)) (unit (fn-bs-unit bs))
         (ks (fn-lgk-recover c genesis unit max next-txid)))
    (implies (and (posp unit) ino (assoc-equal ino (fn-bs-inodes bs))
                  (true-listp c) (equal (mod (len c) unit) 0)
                  (fn-frame-digestp genesis)
                  (fn-assume-log-sole-pending-writer bs ino)
                  (not (fn-bs-ops-for-ino (fn-bs-pending bs) ino))
                  (member-equal r (fn-lgk-committed ks))
                  (member-equal pair (fn-lg-run bs ks (fn-lg-recover-program) nil ino))
                  (fn-bs-crash-imagep (car pair) image))
             (member-equal r (car (fn-lg-scan (fn-bs-durable-content image ino)
                                              genesis unit max)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-assume-log-sole-pending-writer-names-only-the-log)
                 (:instance fn-lgu-no-ops-either-way-is-atom (ops (fn-bs-pending bs)))
                 (:instance fn-lgu-frontier-facts (c (fn-bs-durable-content bs ino)) (unit (fn-bs-unit bs)))
                 (:instance fn-lgu-recover-run-pairs
                            (ks (fn-lgk-recover (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max next-txid)))
                 (:instance fn-lgu-read-from-an-image-of-the-truncating-state)
                 (:instance fn-lgk-recover-establishes-relation)
                 (:instance fn-lgu-committed-record-is-read-from-every-crash-image
                            (bs (mv-nth 1 (fn-bs-fsync-file
                                           (mv-nth 1 (fn-bs-write bs ino
                                                                  (cdr (fn-lg-scan (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max))
                                                                  (fn-bs-zeros (- (len (fn-bs-durable-content bs ino))
                                                                                  (cdr (fn-lg-scan (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max))))
                                                                  :ok))
                                           ino :ok)))
                            (ks (fn-lgk-recover (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max next-txid))))
           :in-theory (union-theories '(car-cons cdr-cons natp nfix atom not
                                        fn-lgu-frontier-of-recover fn-lgu-recovered-kernel-holds-the-scan
                                        fn-lgu-unit-of-write fn-lgu-unit-of-fsync-file)
                                      (theory 'minimal-theory)))))

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
; 6. The keystone, in the owner layer's vocabulary.

; An acknowledged member's record is one of the kernel's committed records
; (the aligned layer places acked ++ waiting's records there).
(local
 (defthm fn-lgu-member-record-in-records
   (implies (member-equal m ms)
            (member-equal (fn-owb-member-record m) (fn-owb-records ms)))))

(defthm fn-lgu-acknowledged-record-is-committed
  (implies (and (fn-owb-alignedp st) (member-equal m (fn-owb-acked st)))
           (member-equal (fn-owb-member-record m) (fn-lgk-committed (fn-owb-ks st))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgu-member-record-in-records (ms (fn-owb-acked st)))
                 (:instance fn-lgu-member-of-append-left
                            (x (fn-owb-member-record m))
                            (a (fn-owb-records (fn-owb-acked st)))
                            (b (fn-owb-records (fn-owb-waiting st)))))
           :in-theory (e/d (fn-owb-alignedp)
                           (fn-owb-records fn-owb-member-record fn-lgk-committed fn-owb-ks
                            fn-owb-acked fn-owb-waiting fn-lgu-member-record-in-records
                            fn-lgu-member-of-append-left)))))

; A crash point of the served programs: a cut state of P-BATCH's append,
; of its fence (the barrier :ok, or failed after landing the admissible
; selection OUTCOME names), or of the segment's extension to NEXT, run from
; the related state (BS, KS).  The cut states are every state of the runs
; (fn-lg-run and fn-lg-extend-run record the pair after every step, the
; :cut steps included).
(defun fn-lgu-crash-point-p (pair bs ks outcome next ino genesis max)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-lgk-relp bs ks ino genesis max)
       (or (member-equal pair (fn-lg-run bs ks (fn-lg-append-program) nil ino))
           (member-equal pair (fn-lg-run bs ks (fn-lg-fence-program) nil ino))
           (and (consp outcome) (not (equal (car outcome) :ok))
                (fn-bs-crash-choicesp (cdr outcome) (fn-bs-pending bs) (fn-bs-unit bs))
                (member-equal pair (fn-lg-run bs ks (fn-lg-fence-program) (list outcome) ino)))
           (and (not (consp (fn-lgk-inflight ks)))
                (natp next)
                (equal (mod next (fn-bs-unit bs)) 0)
                (< (len (fn-bs-durable-content bs ino)) next)
                (member-equal pair (fn-lg-extend-run bs ks (fn-lg-extend-program next) nil ino))))))

; KEYSTONE.  An article the node acknowledged as accepted (a member of the
; aligned layer's acked list) is held by the kernel recovered from the
; durable content of every admissible crash image of every crash point of
; the served programs.  No trailer assumption; the platform's tear model
; only (fn-bs-crash-imagep).
(defthm fn-lgu-acknowledged-article-is-recoverable-at-every-crash-point
  (implies (and (fn-owb-alignedp st)
                (member-equal m (fn-owb-acked st))
                (fn-lgu-crash-point-p pair bs (fn-owb-ks st) outcome next ino genesis max)
                (fn-bs-crash-imagep (car pair) image))
           (member-equal (fn-owb-member-record m)
                         (fn-lgk-committed
                          (fn-lgk-recover (fn-bs-durable-content image ino)
                                          genesis (fn-bs-unit bs) max next-txid))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgu-acknowledged-record-is-committed)
                 (:instance fn-lgu-committed-record-survives-every-cut-of-the-append
                            (ks (fn-owb-ks st)) (r (fn-owb-member-record m)))
                 (:instance fn-lgu-committed-record-survives-every-cut-of-the-fence
                            (ks (fn-owb-ks st)) (r (fn-owb-member-record m)))
                 (:instance fn-lgu-committed-record-survives-every-cut-of-a-failed-fence
                            (ks (fn-owb-ks st)) (r (fn-owb-member-record m)))
                 (:instance fn-lgu-committed-record-survives-every-cut-of-the-extension
                            (ks (fn-owb-ks st)) (r (fn-owb-member-record m))))
           :in-theory (union-theories '(fn-lgu-crash-point-p car-cons cdr-cons
                                        fn-lgu-recovered-kernel-holds-the-scan)
                                      (theory 'minimal-theory)))))

; The open's half: the recovered layer (fn-owb-recover, every record of the
; scan an anonymous acknowledged-as-stored member) at every cut of
; P-LOG-RECOVER.  The layer's kernel is the scan's kernel.
(defthm fn-lgu-acknowledged-article-is-recoverable-at-every-cut-of-recovery
  (let* ((c (fn-bs-durable-content bs ino)) (unit (fn-bs-unit bs))
         (st (fn-owb-recover c genesis unit max next-txid)))
    (implies (and (posp unit) ino (assoc-equal ino (fn-bs-inodes bs))
                  (true-listp c) (equal (mod (len c) unit) 0)
                  (fn-frame-digestp genesis)
                  (fn-assume-log-sole-pending-writer bs ino)
                  (not (fn-bs-ops-for-ino (fn-bs-pending bs) ino))
                  (member-equal r (fn-lgk-committed (fn-owb-ks st)))
                  (member-equal pair (fn-lg-run bs (fn-owb-ks st) (fn-lg-recover-program) nil ino))
                  (fn-bs-crash-imagep (car pair) image))
             (member-equal r (fn-lgk-committed
                              (fn-lgk-recover (fn-bs-durable-content image ino)
                                              genesis unit max next-txid2)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgu-record-read-at-open-survives-every-cut-of-recovery))
           :in-theory (union-theories '(fn-owb-recover fn-owb-fields-of-make car-cons cdr-cons
                                        fn-lgu-recovered-kernel-holds-the-scan)
                                      (theory 'minimal-theory)))))
