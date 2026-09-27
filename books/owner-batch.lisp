; owner-batch.lisp -- the owner's batch over the record log.
;
; Design planning/design-2026-09-27-storage-log.md section 3.3 (the commit,
; the batch, the frontier) and 5.1 (T1, T4, T7); D33 (the catalog's
; PreparedCommit token), D34 (fresh deploys at fn-store-9).  The batch layer
; sits over two kernels it does not change: the log kernel fn-lgk-*
; (books/store-log-kernel.lisp; the octets, offsets and phases of the
; segment) and the catalog's token protocol fn-cat-prepare / fn-cat-complete
; (books/catalog-commit.lisp).  Each transition here is the function the
; host's owner calls once the store node's article commit moves from the
; file kernel (books/store-files.lisp, one staged record) onto these two
; kernels; that move is the decision packet in
; planning/evidence/w6-log-owner-2026-09-27.md section 2, and until it lands
; no host line calls this book (as store-log-kernel's PRF-244/245 today).
;
; The batch layer's state: (:owb ks members inflight waiting acked).
;   ks       the log kernel state (fn-lgk-make ...)
;   members  the OPEN batch, in prepare order: (id token record) per member,
;            aligned with (fn-lgk-batch ks)
;   inflight the batch in flight (appended, not fenced), aligned with
;            (fn-lgk-inflight ks)
;   waiting  committed (fenced) members not yet acknowledged, in order
;   acked    acknowledged members, in order
; with (append (records acked) (records waiting)) = (fn-lgk-committed ks) and
; (len acked) = (fn-lgk-acked ks): fn-owb-alignedp.  A member's record is
; the encoded store event the log entry carries (T6: the entry's payload
; after its chain is the record's bytes; the host supplies it from
; fn-owner-pending-octets and computes nothing else).
;
; The transitions: fn-owb-take (the close rule's gate: below bmax members
; and omax octets, the kernel not faulted; then fn-lgk-prepare),
; fn-owb-append (fn-lgk-append: the open batch becomes the batch in flight),
; fn-owb-fence (:ok: every member in flight is committed and waits for its
; acknowledgement), fn-owb-fence-failed (fsyncgate: the kernel faults; every
; member in flight or waiting is answered :uncertain, fn-owb-fault-words),
; fn-owb-finish-member (in order: the head of WAITING is acknowledged
; :durable; only when the kernel is not faulted).  A refusal (duplicate,
; conflict, policy) never enters the batch; a known abort is
; fn-lgk-known-abort.
;
; THE CLOSE RULE (design 3.3, 8): barrier-paced, no timer.  bmax and omax
; are the operator's LIVE configuration through the existing delta kind
; :set-limit (books/config.lisp, code 8) with the slots "log-batch-records"
; and "log-batch-octets"; an unset slot (fn-cfg-limit answers 0) means the
; default: 64 records, the batch buffer's size.  Neither is a profile field
; or a constant of the kernel: a work bound per scheduling step (D27).
;
; KEYSTONES
;   fn-owb-batch-within-bounds (invariant): no open batch exceeds bmax
;     members or omax octets; fn-owb-take preserves it, the other
;     transitions empty or keep the open batch.
;   T1 fn-owb-acknowledged-record-survives-crash: an acknowledged member's
;     record is read by the scan of every admissible crash image (R at the
;     cut; A-CRASH-IMAGE as fn-bs-crash-imagep; the tear of a pending write
;     is the platform's, fn-lg-platform-tears-p, as store-log-crash's
;     corollary states it).
;   T4 fn-owb-batch-complete-is-the-sequential-complete: completing a batch
;     of tokens in order equals preparing and completing each member alone
;     after its predecessors: the same rows, the same deltas, the same
;     catalog and arena.  The content: fn-cat-intern reads no catalog state,
;     and a member's EXPECTED is the count its predecessors leave.
;   T7 fn-owb-uncertain-batch-recovers-to-a-prefix: after a failed barrier
;     the kernel is :fault, every member in flight is :uncertain, and the
;     kernel recovered from the store the failed fsync left holds the
;     committed records followed by a prefix of the batch.
;   fn-owb-recover-establishes-relation: store-log-recover's obligation
;     fn-assume-log-sole-pending-writer discharged by functional instantiation
;     with fn-owb-sole-pending-writer, which every R-related store satisfies
;     (fn-owb-related-state-is-the-sole-pending-writer).

(in-package "ACL2")
(include-book "store-log-recover")
(include-book "catalog-commit")
(include-book "config")

; -----------------------------------------------------------------------------
; The close rule's bounds.

(defconst *fn-owb-default-batch-records* 64)

(defun fn-owb-bmax (v)
  (declare (xargs :guard t))
  (let ((n (fn-cfg-limit v "log-batch-records")))
    (if (posp n) n *fn-owb-default-batch-records*)))

(defun fn-owb-omax (v size)
  (declare (xargs :guard (natp size)))
  (let ((n (fn-cfg-limit v "log-batch-octets")))
    (if (and (posp n) (< n size)) n size)))

(defthm fn-owb-bmax-posp
  (posp (fn-owb-bmax v))
  :rule-classes :type-prescription)

(defthm fn-owb-omax-within-the-buffer
  (implies (natp size) (<= (fn-owb-omax v size) size)))

; -----------------------------------------------------------------------------
; Members and the state.

(defun fn-owb-member (id token record)
  (declare (xargs :guard t))
  (list id token record))
(defun fn-owb-member-id (m) (declare (xargs :guard t)) (if (consp m) (car m) nil))
(defun fn-owb-member-token (m)
  (declare (xargs :guard t))
  (if (and (consp m) (consp (cdr m))) (cadr m) nil))
(defun fn-owb-member-record (m)
  (declare (xargs :guard t))
  (if (and (consp m) (consp (cdr m)) (consp (cddr m))) (caddr m) nil))

(defun fn-owb-records (ms)
  (declare (xargs :guard t))
  (if (atom ms) nil (cons (fn-owb-member-record (car ms)) (fn-owb-records (cdr ms)))))

(defun fn-owb-make (ks members inflight waiting acked)
  (declare (xargs :guard t))
  (list :owb ks members inflight waiting acked))
(defun fn-owb-ks (st) (declare (xargs :guard (true-listp st))) (nth 1 st))
(defun fn-owb-members (st) (declare (xargs :guard (true-listp st))) (nth 2 st))
(defun fn-owb-inflight (st) (declare (xargs :guard (true-listp st))) (nth 3 st))
(defun fn-owb-waiting (st) (declare (xargs :guard (true-listp st))) (nth 4 st))
(defun fn-owb-acked (st) (declare (xargs :guard (true-listp st))) (nth 5 st))

(defthm fn-owb-fields-of-make
  (and (equal (fn-owb-ks (fn-owb-make ks m i w a)) ks)
       (equal (fn-owb-members (fn-owb-make ks m i w a)) m)
       (equal (fn-owb-inflight (fn-owb-make ks m i w a)) i)
       (equal (fn-owb-waiting (fn-owb-make ks m i w a)) w)
       (equal (fn-owb-acked (fn-owb-make ks m i w a)) a)))

(defthm fn-owb-records-of-append
  (equal (fn-owb-records (append a b))
         (append (fn-owb-records a) (fn-owb-records b))))

(defthm fn-owb-len-of-records
  (equal (len (fn-owb-records ms)) (len ms)))

; The alignment of the layer with the kernel.
(defun fn-owb-alignedp (st)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp st)
       (let ((ks (fn-owb-ks st)))
         (and (true-listp ks)
              (true-listp (fn-lgk-batch ks)) (true-listp (fn-lgk-inflight ks))
              (true-listp (fn-lgk-committed ks))
              (true-listp (fn-owb-members st)) (true-listp (fn-owb-inflight st))
              (true-listp (fn-owb-waiting st)) (true-listp (fn-owb-acked st))
              (equal (fn-owb-records (fn-owb-members st)) (fn-lgk-batch ks))
              (equal (fn-owb-records (fn-owb-inflight st)) (fn-lgk-inflight ks))
              (equal (append (fn-owb-records (fn-owb-acked st))
                             (fn-owb-records (fn-owb-waiting st)))
                     (fn-lgk-committed ks))
              (equal (len (fn-owb-acked st)) (fn-lgk-acked ks))))))

; The recovered layer: nothing open, in flight or waiting; every committed
; record of the scan is a durable, unacknowledged history the owner answers
; as stored (STO-005); ACKED is empty and the kernel's acked is the count of
; committed (fn-lgk-recover), so the layer carries the committed records as
; anonymous members with no connection to answer.
(defun fn-owb-anonymous (records)
  (declare (xargs :guard t))
  (if (atom records) nil
    (cons (fn-owb-member nil nil (car records)) (fn-owb-anonymous (cdr records)))))

(defthm fn-owb-records-of-anonymous
  (implies (true-listp records)
           (equal (fn-owb-records (fn-owb-anonymous records)) records)))

(defthm fn-owb-len-of-anonymous
  (equal (len (fn-owb-anonymous records)) (len records)))

(defun fn-owb-recover (c genesis unit max next-txid)
  (declare (xargs :guard t :verify-guards nil))
  (let ((ks (fn-lgk-recover c genesis unit max next-txid)))
    (fn-owb-make ks nil nil nil (fn-owb-anonymous (fn-lgk-committed ks)))))

; -----------------------------------------------------------------------------
; The open batch's octets, and the transitions.

; The entry's length does not read the chain digest's value (a digest is 32
; octets), so the bound is over a fixed digest and does not move with the
; chain head.
(defun fn-owb-batch-octets (records unit)
  (declare (xargs :guard t :verify-guards nil))
  (len (fn-lg-log records *fn-lg-genesis* unit)))

(defun fn-owb-take-enabledp (st record unit bmax omax)
  (declare (xargs :guard t :verify-guards nil))
  (let ((ks (fn-owb-ks st)))
    (and (true-listp st)
         (not (equal (fn-lgk-phase ks) :fault))
         (< (len (fn-owb-members st)) (nfix bmax))
         (<= (fn-owb-batch-octets (append (fn-lgk-batch ks) (list record)) unit)
             (nfix omax)))))

(defun fn-owb-take (st id token record unit bmax omax)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-owb-take-enabledp st record unit bmax omax)
      (fn-owb-make (fn-lgk-prepare (fn-owb-ks st) record)
                   (append (fn-owb-members st) (list (fn-owb-member id token record)))
                   (fn-owb-inflight st) (fn-owb-waiting st) (fn-owb-acked st))
    st))

(defun fn-owb-known-abort (st)
  (declare (xargs :guard t :verify-guards nil))
  (fn-owb-make (fn-lgk-known-abort (fn-owb-ks st)) (fn-owb-members st)
               (fn-owb-inflight st) (fn-owb-waiting st) (fn-owb-acked st)))

(defun fn-owb-append-enabledp (st unit extent)
  (declare (xargs :guard t :verify-guards nil))
  (let ((ks (fn-owb-ks st)))
    (and (true-listp st)
         (not (consp (fn-lgk-inflight ks)))
         (not (equal (fn-lgk-phase ks) :fault))
         (fn-lgk-fitsp ks unit extent))))

(defun fn-owb-append (st unit extent)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-owb-append-enabledp st unit extent)
      (fn-owb-make (fn-lgk-append (fn-owb-ks st) unit extent) nil (fn-owb-members st)
                   (fn-owb-waiting st) (fn-owb-acked st))
    st))

(defun fn-owb-fence (st unit)
  (declare (xargs :guard t :verify-guards nil))
  (fn-owb-make (fn-lgk-fence (fn-owb-ks st) unit) (fn-owb-members st) nil
               (append (fn-owb-waiting st) (fn-owb-inflight st)) (fn-owb-acked st)))

(defun fn-owb-fence-failed (st)
  (declare (xargs :guard t :verify-guards nil))
  (fn-owb-make (fn-lgk-fence-failed (fn-owb-ks st)) (fn-owb-members st)
               (fn-owb-inflight st) (fn-owb-waiting st) (fn-owb-acked st)))

; The words a faulted kernel answers: every member in flight or waiting is
; :uncertain (the store is fenced; recovery decides).
(defun fn-owb-uncertain-words (ms)
  (declare (xargs :guard t))
  (if (atom ms) nil
    (cons (cons (fn-owb-member-id (car ms)) :uncertain)
          (fn-owb-uncertain-words (cdr ms)))))

(defun fn-owb-fault-words (st)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (true-listp st) (equal (fn-lgk-phase (fn-owb-ks st)) :fault))
      (fn-owb-uncertain-words (append (fn-owb-waiting st) (fn-owb-inflight st)))
    nil))

; => (mv word-or-nil st'): the head of WAITING acknowledged :durable, in
; order; nothing when nothing waits or the kernel is faulted.
(defun fn-owb-finish-member (st)
  (declare (xargs :guard t :verify-guards nil))
  (let ((ks (fn-owb-ks st)) (w (fn-owb-waiting st)))
    (if (and (true-listp st) (consp w) (not (equal (fn-lgk-phase ks) :fault)))
        (mv (cons (fn-owb-member-id (car w)) :durable)
            (fn-owb-make (fn-lgk-finish-one ks) (fn-owb-members st) (fn-owb-inflight st)
                         (cdr w) (append (fn-owb-acked st) (list (car w)))))
      (mv nil st))))

; -----------------------------------------------------------------------------
; Alignment is carried by every transition.

(defthm fn-owb-take-preserves-alignment
  (implies (fn-owb-alignedp st)
           (fn-owb-alignedp (fn-owb-take st id token record unit bmax omax)))
  :hints (("Goal" :in-theory (disable fn-lg-log fn-owb-batch-octets fn-lgk-fitsp))))

(defthm fn-owb-known-abort-preserves-alignment
  (implies (fn-owb-alignedp st) (fn-owb-alignedp (fn-owb-known-abort st))))

(defthm fn-owb-append-preserves-alignment
  (implies (fn-owb-alignedp st) (fn-owb-alignedp (fn-owb-append st unit extent)))
  :hints (("Goal" :in-theory (disable fn-lgk-fitsp fn-lg-log))))

(defthm fn-owb-fence-preserves-alignment
  (implies (fn-owb-alignedp st) (fn-owb-alignedp (fn-owb-fence st unit)))
  :hints (("Goal" :in-theory (disable fn-lg-log fn-lg-last-trailer))))

(defthm fn-owb-fence-failed-preserves-alignment
  (implies (fn-owb-alignedp st) (fn-owb-alignedp (fn-owb-fence-failed st))))

(defthm fn-owb-finish-member-preserves-alignment
  (implies (fn-owb-alignedp st) (fn-owb-alignedp (mv-nth 1 (fn-owb-finish-member st)))))

(defthm fn-owb-recover-is-aligned
  (fn-owb-alignedp (fn-owb-recover c genesis unit max next-txid))
  :hints (("Goal" :in-theory (disable fn-lg-scan fn-lg-scan-last))))

; -----------------------------------------------------------------------------
; The bounds (design 3.3: a work bound per scheduling step, D27).

(defun fn-owb-boundedp (st unit bmax omax)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp st)
       (<= (len (fn-owb-members st)) (nfix bmax))
       (<= (fn-owb-batch-octets (fn-lgk-batch (fn-owb-ks st)) unit) (nfix omax))))

(defthm fn-owb-take-preserves-bounds
  (implies (fn-owb-boundedp st unit bmax omax)
           (fn-owb-boundedp (fn-owb-take st id token record unit bmax omax) unit bmax omax))
  :hints (("Goal" :in-theory (disable fn-owb-batch-octets fn-lg-log))))

(defthm fn-owb-batch-octets-of-nil
  (equal (fn-owb-batch-octets nil unit) 0))

(defthm fn-owb-append-preserves-bounds
  (implies (fn-owb-boundedp st unit bmax omax)
           (fn-owb-boundedp (fn-owb-append st unit extent) unit bmax omax))
  :hints (("Goal" :in-theory (disable fn-owb-batch-octets fn-lg-log fn-lgk-fitsp))))

(defthm fn-owb-fence-preserves-bounds
  (implies (fn-owb-boundedp st unit bmax omax)
           (fn-owb-boundedp (fn-owb-fence st unit) unit bmax omax))
  :hints (("Goal" :in-theory (disable fn-owb-batch-octets fn-lg-log fn-lg-last-trailer))))

(defthm fn-owb-fence-failed-preserves-bounds
  (implies (fn-owb-boundedp st unit bmax omax)
           (fn-owb-boundedp (fn-owb-fence-failed st) unit bmax omax))
  :hints (("Goal" :in-theory (disable fn-owb-batch-octets fn-lg-log))))

(defthm fn-owb-known-abort-preserves-bounds
  (implies (fn-owb-boundedp st unit bmax omax)
           (fn-owb-boundedp (fn-owb-known-abort st) unit bmax omax))
  :hints (("Goal" :in-theory (disable fn-owb-batch-octets fn-lg-log))))

(defthm fn-owb-finish-member-preserves-bounds
  (implies (fn-owb-boundedp st unit bmax omax)
           (fn-owb-boundedp (mv-nth 1 (fn-owb-finish-member st)) unit bmax omax))
  :hints (("Goal" :in-theory (disable fn-owb-batch-octets fn-lg-log))))

(defthm fn-owb-recover-is-bounded
  (fn-owb-boundedp (fn-owb-recover c genesis unit max next-txid) unit bmax omax)
  :hints (("Goal" :in-theory (disable fn-lg-scan fn-lg-scan-last))))

; The keystone form: the open batch of a bounded layer never exceeds either
; bound, and a take beyond either is refused with the layer unchanged.
(defthm fn-owb-batch-within-bounds
  (implies (fn-owb-boundedp st unit bmax omax)
           (and (<= (len (fn-owb-members st)) (nfix bmax))
                (<= (fn-owb-batch-octets (fn-lgk-batch (fn-owb-ks st)) unit) (nfix omax))
                (implies (or (not (< (len (fn-owb-members st)) (nfix bmax)))
                             (not (<= (fn-owb-batch-octets
                                       (append (fn-lgk-batch (fn-owb-ks st)) (list record)) unit)
                                      (nfix omax))))
                         (equal (fn-owb-take st id token record unit bmax omax) st))))
  :hints (("Goal" :in-theory (disable fn-owb-batch-octets fn-lg-log))))

; -----------------------------------------------------------------------------
; The sole pending writer: store-log-recover's obligation, discharged.

(defun fn-owb-sole-pending-writer (bs ino)
  (declare (xargs :guard t :verify-guards nil))
  (not (fn-bs-ops-not-for-ino (fn-bs-pending bs) ino)))

(defthm fn-owb-related-state-is-the-sole-pending-writer
  (implies (fn-lgk-relp bs ks ino genesis max)
           (fn-owb-sole-pending-writer bs ino))
  :hints (("Goal" :in-theory (e/d (fn-lgk-relp) (fn-lgk-content-okp fn-lg-log)))))

(defthm fn-owb-recover-establishes-relation
  (let* ((unit (fn-bs-unit bs)) (c (fn-bs-durable-content bs ino))
         (ks (fn-lgk-recover c genesis unit max next-txid))
         (f (fn-lgk-frontier ks))
         (bs1 (mv-nth 1 (fn-bs-write bs ino f (fn-bs-zeros (- (len c) f)) :ok)))
         (bs2 (mv-nth 1 (fn-bs-fsync-file bs1 ino :ok))))
    (implies (and (posp unit) ino (assoc-equal ino (fn-bs-inodes bs))
                  (true-listp c) (equal (mod (len c) unit) 0)
                  (fn-frame-digestp genesis)
                  (fn-owb-sole-pending-writer bs ino)
                  (not (fn-bs-ops-for-ino (fn-bs-pending bs) ino)))
             (fn-lgk-relp bs2 ks ino genesis max)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-owb-sole-pending-writer))
           :use ((:functional-instance fn-lgk-recover-establishes-relation
                                       (fn-assume-log-sole-pending-writer
                                        fn-owb-sole-pending-writer))))))
