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

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

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
; The kernel's transitions, field by field (D26: the preservation lemmas
; below rewrite through these instead of opening the kernel's constructor).

(defthm fn-owb-lgk-make-true-listp
  (true-listp (fn-lgk-make committed last frontier next-txid batch inflight acked phase)))

(defthm fn-owb-make-true-listp
  (true-listp (fn-owb-make ks m i w a)))

(local
 (defthm fn-owb-true-list-fix-of-true-listp
   (implies (true-listp x) (equal (true-list-fix x) x))))

(defthm fn-owb-member-record-of-member
  (equal (fn-owb-member-record (fn-owb-member id token record)) record))

(defthm fn-owb-fields-of-lgk-prepare
  (implies (not (equal (fn-lgk-phase ks) :fault))
           (let ((k2 (fn-lgk-prepare ks record)))
             (and (true-listp k2)
                  (equal (fn-lgk-committed k2) (fn-lgk-committed ks))
                  (equal (fn-lgk-last k2) (fn-lgk-last ks))
                  (equal (fn-lgk-frontier k2) (fn-lgk-frontier ks))
                  (equal (fn-lgk-batch k2) (append (true-list-fix (fn-lgk-batch ks)) (list record)))
                  (equal (fn-lgk-inflight k2) (fn-lgk-inflight ks))
                  (equal (fn-lgk-acked k2) (fn-lgk-acked ks))
                  (equal (fn-lgk-phase k2) (fn-lgk-phase ks)))))
  :hints (("Goal" :in-theory (e/d (fn-lgk-prepare) (fn-lgk-make fn-lgk-committed fn-lgk-last
                                                     fn-lgk-frontier fn-lgk-next-txid fn-lgk-batch
                                                     fn-lgk-inflight fn-lgk-acked fn-lgk-phase)))))

(defthm fn-owb-lgk-prepare-when-faulted
  (implies (equal (fn-lgk-phase ks) :fault)
           (equal (fn-lgk-prepare ks record) ks))
  :hints (("Goal" :in-theory (e/d (fn-lgk-prepare) (fn-lgk-make fn-lgk-phase)))))

(defthm fn-owb-fields-of-lgk-known-abort
  (let ((k2 (fn-lgk-known-abort ks)))
    (and (true-listp k2)
         (equal (fn-lgk-committed k2) (fn-lgk-committed ks))
         (equal (fn-lgk-last k2) (fn-lgk-last ks))
         (equal (fn-lgk-frontier k2) (fn-lgk-frontier ks))
         (equal (fn-lgk-batch k2) (fn-lgk-batch ks))
         (equal (fn-lgk-inflight k2) (fn-lgk-inflight ks))
         (equal (fn-lgk-acked k2) (fn-lgk-acked ks))
         (equal (fn-lgk-phase k2) (fn-lgk-phase ks))))
  :hints (("Goal" :in-theory (e/d (fn-lgk-known-abort) (fn-lgk-make fn-lgk-committed fn-lgk-last
                                                         fn-lgk-frontier fn-lgk-next-txid fn-lgk-batch
                                                         fn-lgk-inflight fn-lgk-acked fn-lgk-phase)))))

(defthm fn-owb-fields-of-lgk-append
  (implies (and (not (consp (fn-lgk-inflight ks))) (not (equal (fn-lgk-phase ks) :fault))
                (fn-lgk-fitsp ks unit extent))
           (let ((k2 (fn-lgk-append ks unit extent)))
             (and (true-listp k2)
                  (equal (fn-lgk-committed k2) (fn-lgk-committed ks))
                  (equal (fn-lgk-last k2) (fn-lgk-last ks))
                  (equal (fn-lgk-frontier k2) (fn-lgk-frontier ks))
                  (equal (fn-lgk-batch k2) nil)
                  (equal (fn-lgk-inflight k2) (true-list-fix (fn-lgk-batch ks)))
                  (equal (fn-lgk-acked k2) (fn-lgk-acked ks))
                  (equal (fn-lgk-phase k2) :appended))))
  :hints (("Goal" :in-theory (e/d (fn-lgk-append) (fn-lgk-make fn-lgk-committed fn-lgk-last
                                                    fn-lgk-frontier fn-lgk-next-txid fn-lgk-batch
                                                    fn-lgk-inflight fn-lgk-acked fn-lgk-phase
                                                    fn-lgk-fitsp)))))

(defthm fn-owb-lgk-append-when-refused
  (implies (or (consp (fn-lgk-inflight ks)) (equal (fn-lgk-phase ks) :fault)
               (not (fn-lgk-fitsp ks unit extent)))
           (equal (fn-lgk-append ks unit extent) ks))
  :hints (("Goal" :in-theory (e/d (fn-lgk-append) (fn-lgk-make fn-lgk-phase fn-lgk-inflight fn-lgk-fitsp)))))

(defthm fn-owb-fields-of-lgk-fence
  (let ((k2 (fn-lgk-fence ks unit)))
    (and (true-listp k2)
         (equal (fn-lgk-committed k2) (append (true-list-fix (fn-lgk-committed ks))
                                              (true-list-fix (fn-lgk-inflight ks))))
         (equal (fn-lgk-batch k2) (fn-lgk-batch ks))
         (equal (fn-lgk-inflight k2) nil)
         (equal (fn-lgk-acked k2) (fn-lgk-acked ks))
         (equal (fn-lgk-phase k2) :fenced)))
  :hints (("Goal" :in-theory (e/d (fn-lgk-fence) (fn-lgk-make fn-lgk-committed fn-lgk-last
                                                   fn-lgk-frontier fn-lgk-next-txid fn-lgk-batch
                                                   fn-lgk-inflight fn-lgk-acked fn-lgk-phase
                                                   fn-lg-log fn-lg-last-trailer)))))

(defthm fn-owb-fields-of-lgk-fence-failed
  (let ((k2 (fn-lgk-fence-failed ks)))
    (and (true-listp k2)
         (equal (fn-lgk-committed k2) (fn-lgk-committed ks))
         (equal (fn-lgk-last k2) (fn-lgk-last ks))
         (equal (fn-lgk-frontier k2) (fn-lgk-frontier ks))
         (equal (fn-lgk-batch k2) (fn-lgk-batch ks))
         (equal (fn-lgk-inflight k2) (fn-lgk-inflight ks))
         (equal (fn-lgk-acked k2) (fn-lgk-acked ks))
         (equal (fn-lgk-phase k2) :fault)))
  :hints (("Goal" :in-theory (e/d (fn-lgk-fence-failed) (fn-lgk-make fn-lgk-committed fn-lgk-last
                                                          fn-lgk-frontier fn-lgk-next-txid fn-lgk-batch
                                                          fn-lgk-inflight fn-lgk-acked fn-lgk-phase)))))

(defthm fn-owb-fields-of-lgk-finish-one
  (implies (< (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
           (let ((k2 (fn-lgk-finish-one ks)))
             (and (true-listp k2)
                  (equal (fn-lgk-committed k2) (fn-lgk-committed ks))
                  (equal (fn-lgk-last k2) (fn-lgk-last ks))
                  (equal (fn-lgk-frontier k2) (fn-lgk-frontier ks))
                  (equal (fn-lgk-batch k2) (fn-lgk-batch ks))
                  (equal (fn-lgk-inflight k2) (fn-lgk-inflight ks))
                  (equal (fn-lgk-acked k2) (1+ (fn-lgk-acked ks)))
                  (equal (fn-lgk-phase k2) (fn-lgk-phase ks)))))
  :hints (("Goal" :in-theory (e/d (fn-lgk-finish-one) (fn-lgk-make fn-lgk-committed fn-lgk-last
                                                        fn-lgk-frontier fn-lgk-next-txid fn-lgk-batch
                                                        fn-lgk-inflight fn-lgk-acked fn-lgk-phase)))))

(defthm fn-owb-lgk-finish-one-when-nothing-waits
  (implies (not (< (fn-lgk-acked ks) (len (fn-lgk-committed ks))))
           (equal (fn-lgk-finish-one ks) ks))
  :hints (("Goal" :in-theory (e/d (fn-lgk-finish-one) (fn-lgk-make fn-lgk-acked fn-lgk-committed)))))

(deftheory fn-owb-kernel-closed
  '(fn-lgk-make fn-lgk-committed fn-lgk-last fn-lgk-frontier fn-lgk-next-txid
    fn-lgk-batch fn-lgk-inflight fn-lgk-acked fn-lgk-phase
    fn-lgk-prepare fn-lgk-known-abort fn-lgk-append fn-lgk-fence fn-lgk-fence-failed
    fn-lgk-finish-one fn-lgk-fitsp fn-lg-log fn-lg-last-trailer fn-owb-batch-octets
    fn-owb-make fn-owb-ks fn-owb-members fn-owb-inflight fn-owb-waiting fn-owb-acked))

; -----------------------------------------------------------------------------
; Alignment is carried by every transition.

(defthm fn-owb-take-preserves-alignment
  (implies (fn-owb-alignedp st)
           (fn-owb-alignedp (fn-owb-take st id token record unit bmax omax)))
  :hints (("Goal" :in-theory (e/d (fn-owb-alignedp fn-owb-take fn-owb-take-enabledp) (fn-owb-kernel-closed)))))

(defthm fn-owb-known-abort-preserves-alignment
  (implies (fn-owb-alignedp st) (fn-owb-alignedp (fn-owb-known-abort st)))
  :hints (("Goal" :in-theory (e/d (fn-owb-alignedp fn-owb-known-abort) (fn-owb-kernel-closed)))))

(defthm fn-owb-append-preserves-alignment
  (implies (fn-owb-alignedp st) (fn-owb-alignedp (fn-owb-append st unit extent)))
  :hints (("Goal" :in-theory (e/d (fn-owb-alignedp fn-owb-append fn-owb-append-enabledp) (fn-owb-kernel-closed)))))

(defthm fn-owb-fence-preserves-alignment
  (implies (fn-owb-alignedp st) (fn-owb-alignedp (fn-owb-fence st unit)))
  :hints (("Goal" :in-theory (e/d (fn-owb-alignedp fn-owb-fence) (fn-owb-kernel-closed)))))

(defthm fn-owb-fence-failed-preserves-alignment
  (implies (fn-owb-alignedp st) (fn-owb-alignedp (fn-owb-fence-failed st)))
  :hints (("Goal" :in-theory (e/d (fn-owb-alignedp fn-owb-fence-failed) (fn-owb-kernel-closed)))))

(local
 (defthm fn-owb-len-of-equal-append-with-a-consp-tail
   (implies (and (equal (append a b) c) (consp b)) (< (len a) (len c)))
   :rule-classes nil))

(defthm fn-owb-finish-member-preserves-alignment
  (implies (fn-owb-alignedp st) (fn-owb-alignedp (mv-nth 1 (fn-owb-finish-member st))))
  :hints (("Goal" :in-theory (e/d (fn-owb-alignedp fn-owb-finish-member)
                                  (fn-owb-kernel-closed fn-owb-member-record fn-owb-member-id
                                   fn-owb-member-token))
           :use ((:instance fn-owb-len-of-equal-append-with-a-consp-tail
                            (a (fn-owb-records (fn-owb-acked st)))
                            (b (fn-owb-records (fn-owb-waiting st)))
                            (c (fn-lgk-committed (fn-owb-ks st))))))))

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
  :hints (("Goal" :in-theory (e/d (fn-owb-boundedp fn-owb-take fn-owb-take-enabledp) (fn-owb-kernel-closed)))))

(defthm fn-owb-batch-octets-of-nil
  (equal (fn-owb-batch-octets nil unit) 0))

(defthm fn-owb-append-preserves-bounds
  (implies (fn-owb-boundedp st unit bmax omax)
           (fn-owb-boundedp (fn-owb-append st unit extent) unit bmax omax))
  :hints (("Goal" :in-theory (e/d (fn-owb-boundedp fn-owb-append fn-owb-append-enabledp fn-owb-batch-octets-of-nil) (fn-owb-kernel-closed)))))

(defthm fn-owb-fence-preserves-bounds
  (implies (fn-owb-boundedp st unit bmax omax)
           (fn-owb-boundedp (fn-owb-fence st unit) unit bmax omax))
  :hints (("Goal" :in-theory (e/d (fn-owb-boundedp fn-owb-fence) (fn-owb-kernel-closed)))))

(defthm fn-owb-fence-failed-preserves-bounds
  (implies (fn-owb-boundedp st unit bmax omax)
           (fn-owb-boundedp (fn-owb-fence-failed st) unit bmax omax))
  :hints (("Goal" :in-theory (e/d (fn-owb-boundedp fn-owb-fence-failed) (fn-owb-kernel-closed)))))

(defthm fn-owb-known-abort-preserves-bounds
  (implies (fn-owb-boundedp st unit bmax omax)
           (fn-owb-boundedp (fn-owb-known-abort st) unit bmax omax))
  :hints (("Goal" :in-theory (e/d (fn-owb-boundedp fn-owb-known-abort) (fn-owb-kernel-closed)))))

; In both branches of the finish the open batch is untouched.
(defthm fn-owb-lgk-finish-one-keeps-the-batch
  (equal (fn-lgk-batch (fn-lgk-finish-one ks)) (fn-lgk-batch ks))
  :hints (("Goal" :in-theory (e/d (fn-lgk-finish-one) (fn-lgk-make fn-lgk-committed fn-lgk-last
                                                        fn-lgk-frontier fn-lgk-next-txid fn-lgk-batch
                                                        fn-lgk-inflight fn-lgk-acked fn-lgk-phase)))))

(defthm fn-owb-finish-member-preserves-bounds
  (implies (fn-owb-boundedp st unit bmax omax)
           (fn-owb-boundedp (mv-nth 1 (fn-owb-finish-member st)) unit bmax omax))
  :hints (("Goal" :in-theory (e/d (fn-owb-boundedp fn-owb-finish-member) (fn-owb-kernel-closed)))))

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

; -----------------------------------------------------------------------------
; The crash images of a related state: the committed records are read by
; every admissible image's scan.

(defthm fn-owb-prefixp-of-append
  (fn-lg-prefixp a (append a b)))

(defthm fn-owb-prefixp-reflexive
  (fn-lg-prefixp a a))

(local
 (defthm fn-owb-take-then-nthcdr
   (implies (and (true-listp c) (natp n) (<= n (len c)))
            (equal (append (fn-bs-take n c) (nthcdr n c)) c))))

(local
 (defthm fn-owb-len-of-take
   (implies (and (true-listp c) (natp n) (<= n (len c)))
            (equal (len (fn-bs-take n c)) n))))

; A content whose prefix scans completely and whose tail is zeros scans to
; that prefix's records: the zeros end the scan (fn-lg-scan-of-zeros).
(defthm fn-owb-scan-of-whole-content
  (implies (and (true-listp c) (natp f) (<= f (len c))
                (equal (fn-lg-scan (fn-bs-take f c) genesis unit max) (cons committed f))
                (fn-lg-zerosp (nthcdr f c)))
           (equal (fn-lg-scan c genesis unit max) (cons committed f)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-owb-take-then-nthcdr (n f))
                 (:instance fn-lg-scan-of-complete-append
                            (d (fn-bs-take f c)) (x (nthcdr f c)) (prev genesis)))
           :in-theory (disable fn-lg-scan fn-lg-scan-last fn-bs-take fn-lg-zerosp
                               fn-lg-scan-of-complete-append fn-owb-take-then-nthcdr))))

(defthm fn-owb-scan-of-related-content
  (implies (and (fn-lgk-relp bs ks ino genesis max) (not (consp (fn-lgk-inflight ks))))
           (equal (fn-lg-scan (fn-bs-durable-content bs ino) genesis (fn-bs-unit bs) max)
                  (cons (fn-lgk-committed ks) (fn-lgk-frontier ks))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgk-relp fn-lgk-content-okp)
                           (fn-lg-scan fn-lg-scan-last fn-lg-log fn-lg-recordsp fn-lg-zerosp
                            fn-bs-take fn-frame-digestp mod fn-bs-durable-content
                            fn-owb-scan-of-whole-content))
           :use ((:instance fn-owb-scan-of-whole-content
                            (c (fn-bs-durable-content bs ino)) (f (fn-lgk-frontier ks))
                            (unit (fn-bs-unit bs)) (committed (fn-lgk-committed ks)))))))

(defthm fn-owb-related-state-with-nothing-in-flight-is-fenced
  (implies (and (fn-lgk-relp bs ks ino genesis max) (not (consp (fn-lgk-inflight ks))))
           (fn-bs-fencedp bs ino))
  :hints (("Goal" :in-theory (e/d (fn-lgk-relp fn-bs-fencedp) (fn-lgk-content-okp fn-lg-log)))))

; A batch in flight: the image's scan is the committed records then a prefix
; of the batch (store-log-crash's corollary under A-CRYPTO-TRAILER; the
; tear of the pending write is the platform's, fn-lg-platform-tears-p).
(defthm fn-owb-image-scan-of-related-state
  (implies (and (fn-lgk-relp bs ks ino genesis max) (consp (fn-lgk-inflight ks))
                (fn-bs-crash-imagep bs image)
                (fn-lg-platform-tears-p (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image ino))
                                        (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs)))
           (fn-lg-crash-verdictp (fn-lg-scan (fn-bs-durable-content image ino) genesis (fn-bs-unit bs) max)
                                 (fn-lgk-committed ks) (fn-lgk-frontier ks) (fn-lgk-inflight ks)
                                 (fn-lgk-last ks) (fn-bs-unit bs)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance fn-lgk-relp-gives-the-tear-hypotheses)
                 (:instance fn-lg-batch-crash-is-a-prefix-under-a-crypto-trailer
                            (s bs) (k (floor (fn-lgk-frontier ks) (fn-bs-unit bs)))
                            (d (fn-bs-take (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                            (z (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                            (committed (fn-lgk-committed ks)) (last (fn-lgk-last ks))
                            (batch (fn-lgk-inflight ks)))))))

(local
 (defthm fn-owb-member-of-append-left
   (implies (member-equal x a) (member-equal x (append a b)))))

(defthm fn-owb-committed-record-survives-crash
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (member-equal r (fn-lgk-committed ks))
                (fn-bs-crash-imagep bs image)
                (implies (consp (fn-lgk-inflight ks))
                         (fn-lg-platform-tears-p
                          (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image ino))
                          (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))))
           (member-equal r (car (fn-lg-scan (fn-bs-durable-content image ino)
                                            genesis (fn-bs-unit bs) max))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-owb-image-scan-of-related-state)
                 (:instance fn-bs-crash-keeps-fenced-content (s bs)))
           :in-theory (e/d (fn-lg-crash-verdictp)
                           (fn-lg-scan fn-lgk-relp fn-bs-crash-imagep fn-bs-durable-content
                            fn-lg-platform-tears-p fn-lg-prefixp fn-lg-log
                            fn-bs-crash-keeps-fenced-content)))))

(local
 (defthm fn-owb-member-record-in-records
   (implies (member-equal m ms)
            (member-equal (fn-owb-member-record m) (fn-owb-records ms)))))

; T1.  An acknowledged member's record is in every admissible crash image.
; Hypotheses: the layer aligned with the kernel, R at the cut (fn-lgk-relp),
; A-CRASH-IMAGE (fn-bs-crash-imagep), and when a batch is in flight the tear
; of its pending write is the platform's (fn-lg-platform-tears-p).  The ack
; discipline is the layer's: fn-owb-finish-member acknowledges only a member
; of WAITING, which fn-owb-fence filled from the fenced batch, so ACKED's
; records are a prefix of the kernel's committed records.
(defthm fn-owb-acknowledged-record-survives-crash
  (implies (and (fn-owb-alignedp st)
                (fn-lgk-relp bs (fn-owb-ks st) ino genesis max)
                (member-equal m (fn-owb-acked st))
                (fn-bs-crash-imagep bs image)
                (implies (consp (fn-lgk-inflight (fn-owb-ks st)))
                         (fn-lg-platform-tears-p
                          (nthcdr (fn-lgk-frontier (fn-owb-ks st)) (fn-bs-durable-content image ino))
                          (fn-lgk-inflight (fn-owb-ks st)) (fn-lgk-last (fn-owb-ks st))
                          (fn-bs-unit bs))))
           (member-equal (fn-owb-member-record m)
                         (car (fn-lg-scan (fn-bs-durable-content image ino)
                                          genesis (fn-bs-unit bs) max))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-owb-committed-record-survives-crash
                            (ks (fn-owb-ks st)) (r (fn-owb-member-record m)))
                 (:instance fn-owb-member-record-in-records (ms (fn-owb-acked st)))
                 (:instance fn-owb-member-of-append-left
                            (x (fn-owb-member-record m))
                            (a (fn-owb-records (fn-owb-acked st)))
                            (b (fn-owb-records (fn-owb-waiting st)))))
           :in-theory (e/d (fn-owb-alignedp)
                           (fn-lg-scan fn-lgk-relp fn-bs-crash-imagep fn-bs-durable-content
                            fn-lg-platform-tears-p fn-owb-committed-record-survives-crash
                            fn-owb-member-record-in-records fn-owb-member-of-append-left
                            fn-owb-records-of-append)))))

; -----------------------------------------------------------------------------
; T7.  The failed barrier (fsyncgate).

; The store a failed fsync of the segment leaves is the crash image of the
; environment's selection: the pending write is the segment's alone.
(defthm fn-owb-failed-fence-is-the-crash-image
  (implies (and ino (equal (fn-bs-pending bs) (list (list :write ino f w))))
           (equal (mv-nth 1 (fn-bs-fsync-file bs ino (cons :eio choices)))
                  (fn-bs-crash bs choices)))
  :hints (("Goal" :in-theory (e/d (fn-bs-fsync-file fn-bs-crash)
                                  (fn-bs-apply-ops fn-bs-crash-select)))))

(defthm fn-owb-failed-fence-image-is-admissible
  (implies (and ino (equal (fn-bs-pending bs) (list (list :write ino f w)))
                (fn-bs-crash-choicesp choices (fn-bs-pending bs) (fn-bs-unit bs)))
           (fn-bs-crash-imagep bs (mv-nth 1 (fn-bs-fsync-file bs ino (cons :eio choices)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-crash-imagep-suff (s bs) (image (fn-bs-crash bs choices))))
           :in-theory (disable fn-bs-crash fn-bs-crash-imagep fn-bs-fsync-file
                               fn-bs-crash-choicesp))))

;; The pending write of a related state with a batch in flight (R's conjunct 3).
(defthm fn-owb-related-pending-in-flight
  (implies (and (fn-lgk-relp bs ks ino genesis max) (consp (fn-lgk-inflight ks)))
           (and ino
                (equal (fn-bs-pending bs)
                       (list (list :write ino (fn-lgk-frontier ks)
                                   (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-lgk-relp) (fn-lgk-content-okp fn-lg-log)))))

; The layer's half: the kernel faulted, every member in flight or waiting
; :uncertain, no acknowledgement.
(defthm fn-owb-fence-failed-answers-uncertain
  (implies (true-listp st)
           (let ((st1 (fn-owb-fence-failed st)))
             (and (equal (fn-lgk-phase (fn-owb-ks st1)) :fault)
                  (equal (fn-owb-fault-words st1)
                         (fn-owb-uncertain-words (append (fn-owb-waiting st) (fn-owb-inflight st))))
                  (equal (mv-nth 0 (fn-owb-finish-member st1)) nil))))
  :hints (("Goal" :in-theory (e/d (fn-lgk-fence-failed) (fn-lgk-committed fn-lgk-last fn-lgk-frontier
                                                          fn-lgk-next-txid fn-lgk-batch fn-lgk-inflight
                                                          fn-lgk-acked)))))

; The kernel's half: recovered from the store the failed fsync left, the
; committed records then a prefix of the batch in flight.
(defthm fn-owb-recovered-kernel-after-a-failed-fence
  (let* ((bs1 (mv-nth 1 (fn-bs-fsync-file bs ino (cons :eio choices))))
         (ks2 (fn-lgk-recover (fn-bs-durable-content bs1 ino) genesis (fn-bs-unit bs) max next-txid)))
    (implies (and (fn-lgk-relp bs ks ino genesis max)
                  (consp (fn-lgk-inflight ks))
                  (fn-bs-crash-choicesp choices (fn-bs-pending bs) (fn-bs-unit bs))
                  (fn-lg-platform-tears-p (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content bs1 ino))
                                          (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs)))
             (and (equal (fn-lgk-committed ks2)
                         (append (fn-lgk-committed ks)
                                 (nthcdr (len (fn-lgk-committed ks)) (fn-lgk-committed ks2))))
                  (fn-lg-prefixp (nthcdr (len (fn-lgk-committed ks)) (fn-lgk-committed ks2))
                                 (fn-lgk-inflight ks)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-owb-related-pending-in-flight)
                 (:instance fn-owb-failed-fence-image-is-admissible
                            (f (fn-lgk-frontier ks))
                            (w (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))))
                 (:instance fn-owb-image-scan-of-related-state
                            (image (mv-nth 1 (fn-bs-fsync-file bs ino (cons :eio choices))))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-lg-crash-verdictp fn-lgk-recover fn-lgk-fields-of-make)))))

; T7.  After a failed barrier the kernel is faulted, every member in flight
; or waiting is answered :uncertain, no member is acknowledged, and the
; kernel recovered from the store the failure left holds the committed
; records followed by a prefix of the batch in flight.
(defthm fn-owb-uncertain-batch-recovers-to-a-prefix
  (let* ((ks (fn-owb-ks st))
         (st1 (fn-owb-fence-failed st))
         (bs1 (mv-nth 1 (fn-bs-fsync-file bs ino (cons :eio choices))))
         (ks2 (fn-lgk-recover (fn-bs-durable-content bs1 ino) genesis (fn-bs-unit bs) max next-txid)))
    (implies (and (fn-owb-alignedp st)
                  (fn-lgk-relp bs ks ino genesis max)
                  (consp (fn-lgk-inflight ks))
                  (fn-bs-crash-choicesp choices (fn-bs-pending bs) (fn-bs-unit bs))
                  (fn-lg-platform-tears-p (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content bs1 ino))
                                          (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs)))
             (and (equal (fn-lgk-phase (fn-owb-ks st1)) :fault)
                  (equal (fn-owb-fault-words st1)
                         (fn-owb-uncertain-words (append (fn-owb-waiting st) (fn-owb-inflight st))))
                  (equal (mv-nth 0 (fn-owb-finish-member st1)) nil)
                  (equal (fn-lgk-committed ks2)
                         (append (fn-lgk-committed ks)
                                 (nthcdr (len (fn-lgk-committed ks)) (fn-lgk-committed ks2))))
                  (fn-lg-prefixp (nthcdr (len (fn-lgk-committed ks)) (fn-lgk-committed ks2))
                                 (fn-lgk-inflight ks)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-owb-fence-failed-answers-uncertain)
                 (:instance fn-owb-recovered-kernel-after-a-failed-fence (ks (fn-owb-ks st))))
           :in-theory (union-theories (theory 'minimal-theory) '(fn-owb-alignedp)))))

; -----------------------------------------------------------------------------
; T4.  The batch of tokens is the sequential token protocol.

; A prepare AHEAD of n members already in the batch: fn-cat-prepare's intern
; (the bytes are the buffer's, the catalog is not read) with EXPECTED the
; count the n predecessors' completes will leave.
(defun fn-owb-cat-prepare (w plan reservation fn-octets keyring generation ahead
                             fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (fn-prin-keyringp keyring) (natp generation) (natp ahead))))
  (mv-let (held fn-arena)
    (fn-cat-intern w fn-octets keyring generation fn-arena)
    (let ((expected (+ (fn-cat-count fn-cat) ahead)))
      (mv (fn-pc-make (cons (nfix (fn-record-txid w)) expected) expected held plan reservation)
          fn-arena))))

(defthm fn-owb-cat-prepare-with-nothing-ahead-is-cat-prepare-by-definition
  (equal (fn-owb-cat-prepare w plan reservation fn-octets keyring generation 0 fn-arena fn-cat)
         (fn-cat-prepare w plan reservation fn-octets keyring generation nil fn-arena fn-cat))
  :hints (("Goal" :in-theory (e/d (fn-cat-prepare fn-owb-cat-prepare)
                                  (fn-cat-intern fn-pc-make fn-record-txid fn-cat-count)))))

; T4's content, one step: the token minted AHEAD of n pending completes is
; the token the sequential protocol mints after them.
(defthm fn-owb-prepare-ahead-is-the-sequential-prepare
  (implies (and (natp ahead)
                (equal (fn-cat-count fn-cat2) (+ ahead (fn-cat-count fn-cat))))
           (equal (fn-owb-cat-prepare w plan reservation fn-octets keyring generation ahead
                                      fn-arena fn-cat)
                  (fn-cat-prepare w plan reservation fn-octets keyring generation nil
                                  fn-arena fn-cat2)))
  :hints (("Goal" :in-theory (e/d (fn-cat-prepare fn-owb-cat-prepare)
                                  (fn-cat-intern fn-pc-make fn-record-txid fn-cat-count)))))

; The batch's finishes, in order by token.
(defun fn-owb-complete-two (pc1 pc2 fn-cat)
  (declare (xargs :stobjs fn-cat :guard (and (fn-pc-p pc1) (fn-pc-p pc2))))
  (mv-let (r1 p1 fn-cat)
    (fn-cat-complete (fn-pc-token pc1) pc1 fn-cat)
    (declare (ignore p1))
    (mv-let (r2 p2 fn-cat)
      (fn-cat-complete (fn-pc-token pc2) pc2 fn-cat)
      (declare (ignore p2))
      (mv r1 r2 fn-cat))))

; T4.  Two members prepared as a batch against the catalog (the second AHEAD
; of the first) and completed in order equal the sequential protocol
; (prepare, complete, prepare, complete): the same deltas, the same catalog,
; the same arena, the count advanced by two.  The fold over a longer batch
; is this step repeated (fn-owb-prepare-ahead-is-the-sequential-prepare with
; fn-cat-commit-count).
(defthm fn-owb-batch-complete-is-the-sequential-complete
  (mv-let (pc1 arena1)
    (fn-owb-cat-prepare w1 plan1 res1 fn-octets keyring gen 0 fn-arena fn-cat)
    (declare (ignorable arena1))
    (mv-let (pc2 arena2)
      (fn-owb-cat-prepare w2 plan2 res2 fn-octets keyring gen 1 arena1 fn-cat)
      (mv-let (b1 b2 cat-b)
        (fn-owb-complete-two pc1 pc2 fn-cat)
        (mv-let (q1 arena-s1)
          (fn-cat-prepare w1 plan1 res1 fn-octets keyring gen nil fn-arena fn-cat)
          (mv-let (s1 p1 cat-s1)
            (fn-cat-complete (fn-pc-token q1) q1 fn-cat)
            (declare (ignorable p1))
            (mv-let (q2 arena-s2)
              (fn-cat-prepare w2 plan2 res2 fn-octets keyring gen nil arena-s1 cat-s1)
              (mv-let (s2 p2 cat-s2)
                (fn-cat-complete (fn-pc-token q2) q2 cat-s1)
                (declare (ignorable p2))
                (and (equal b1 s1) (equal b2 s2)
                     (equal cat-b cat-s2) (equal arena2 arena-s2)
                     (equal (fn-cat-count cat-b) (+ 2 (fn-cat-count fn-cat)))))))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-owb-cat-prepare fn-cat-prepare fn-owb-complete-two fn-cat-complete)
                           (fn-cat-commit fn-cat-intern fn-cat-at fn-delta-of-row
                            fn-cat-count-is-len fn-cat-at-is-nth fn-cat-commit-is-append)))))
