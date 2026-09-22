; Executable kernel for the immutable-file storage experiment.
;
; This book models allocator replacement, one-file transaction publication,
; crash choices, the completion gate, and recovery barriers.  It does not model
; POSIX calls or prove that a platform implements these events.  Candidate
; records are checked by the existing record predicate and replay engine; no
; second acceptance implementation is introduced here.
;
; Composition scope.  The host (host/store-node-host.lisp) drives this kernel
; only through the fn-sn composition in store-node.lisp and
; store-node-resolution.lisp.  Two phases are transient in that composition:
; :aborting exists only inside fn-sn-known-abort and :completed only inside
; fn-sn-finish, so no host call can leave the kernel in either; each is marked
; unreachable-in-composition where it appears.  Result values that the host
; never reports (an uncertain refusal, a lost or rejected core completion
; reply) are not transitions here: the host fences on its own side and reopens
; through fn-sn-open-observed instead of reporting them.
;
; Crash points.  A crash choice is live from the moment the corresponding
; namespace syscall may have been issued, not from the moment its result was
; reported: the host issues os.replace before it reports :frontier-replace and
; os.link before it reports :record-link, and process death between the syscall
; returning and the report is a real cut (tests/store_crash_child.py, points
; frontier-replace and final-link).  fn-sf-frontier-new-visiblep and
; fn-sf-record-present-visiblep therefore include the data-durable phases.

(in-package "ACL2")
(include-book "replay")
; The codecs cluster withdraws the record and codec definitions at export
; (2026-09-19); the proofs here open fn-store-event-p and the record accessors.
(local (in-theory (enable fn-record-record-vocabulary fn-record-codec-vocabulary)))

(defconst *fn-sf-max-uint* 4294967295)
(defconst *fn-sf-recovery-barrier-count* 5)

; -----------------------------------------------------------------------------
; The kernel state record (opaque below its lemmas, docs/proof-style.md s1).
; Layout: (:store-files phase frontier frontier-candidate records
;          record-candidate completion-pair successes recovery-barriers)
(defun fn-sf-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 9) (equal (car x) :store-files)))

(defun fn-sf-phase (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr s)) :exec (fn-ag-car (fn-ag-cdr s))))
(defun fn-sf-frontier (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr s)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr s)))))
(defun fn-sf-frontier-candidate (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr s))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s))))))
(defun fn-sf-records (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr s)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s)))))))
(defun fn-sf-record-candidate (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr s))))))
       :exec (fn-ag-car
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                      (fn-ag-cdr (fn-ag-cdr s))))))))
(defun fn-sf-completion (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr s)))))))
       :exec (fn-ag-car
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                         (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s)))))))))
(defun fn-sf-successes (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr s))))))))
       :exec (fn-ag-car
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                         (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s))))))))))
(defun fn-sf-barriers (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr (cdr (cdr (cdr s)))))))))
       :exec (fn-ag-car
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                         (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s)))))))))))

(defun fn-sf-make (phase frontier frontier-candidate records record-candidate
                         completion successes barriers)
  (declare (xargs :guard t))
  (list :store-files phase frontier frontier-candidate records record-candidate
        completion successes barriers))

(verify-guards fn-sf-phase)
(verify-guards fn-sf-frontier)
(verify-guards fn-sf-frontier-candidate)
(verify-guards fn-sf-records)
(verify-guards fn-sf-record-candidate)
(verify-guards fn-sf-completion)
(verify-guards fn-sf-successes)
(verify-guards fn-sf-barriers)

(defthm fn-sf-shapep-of-fn-sf-make
  (fn-sf-shapep (fn-sf-make phase frontier frontier-candidate records
                            record-candidate completion successes barriers)))
(defthm fn-sf-phase-of-fn-sf-make
  (equal (fn-sf-phase (fn-sf-make phase frontier frontier-candidate records
                                  record-candidate completion successes barriers))
         phase))
(defthm fn-sf-frontier-of-fn-sf-make
  (equal (fn-sf-frontier (fn-sf-make phase frontier frontier-candidate records
                                     record-candidate completion successes barriers))
         frontier))
(defthm fn-sf-frontier-candidate-of-fn-sf-make
  (equal (fn-sf-frontier-candidate
          (fn-sf-make phase frontier frontier-candidate records
                      record-candidate completion successes barriers))
         frontier-candidate))
(defthm fn-sf-records-of-fn-sf-make
  (equal (fn-sf-records (fn-sf-make phase frontier frontier-candidate records
                                    record-candidate completion successes barriers))
         records))
(defthm fn-sf-record-candidate-of-fn-sf-make
  (equal (fn-sf-record-candidate
          (fn-sf-make phase frontier frontier-candidate records
                      record-candidate completion successes barriers))
         record-candidate))
(defthm fn-sf-completion-of-fn-sf-make
  (equal (fn-sf-completion (fn-sf-make phase frontier frontier-candidate records
                                       record-candidate completion successes barriers))
         completion))
(defthm fn-sf-successes-of-fn-sf-make
  (equal (fn-sf-successes (fn-sf-make phase frontier frontier-candidate records
                                      record-candidate completion successes barriers))
         successes))
(defthm fn-sf-barriers-of-fn-sf-make
  (equal (fn-sf-barriers (fn-sf-make phase frontier frontier-candidate records
                                     record-candidate completion successes barriers))
         barriers))

; Nothing below opens the record: goals stay in accessor vocabulary.
(in-theory (disable (:d fn-sf-shapep) (:d fn-sf-phase) (:d fn-sf-frontier)
                    (:d fn-sf-frontier-candidate) (:d fn-sf-records)
                    (:d fn-sf-record-candidate) (:d fn-sf-completion)
                    (:d fn-sf-successes) (:d fn-sf-barriers) (:d fn-sf-make)))

; Shape facts type reasoning used to supply while the record opened
; (docs/proof-style.md s1), exported as forward-chaining rules only.
(defthm fn-sf-shapep-forward-shape
  (implies (fn-sf-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-sf-shapep))))
(defthm fn-sf-accessors-forward-consp
  (and (implies (fn-sf-phase x) (consp x))
       (implies (fn-sf-frontier x) (consp x))
       (implies (fn-sf-frontier-candidate x) (consp x))
       (implies (fn-sf-records x) (consp x))
       (implies (fn-sf-record-candidate x) (consp x))
       (implies (fn-sf-completion x) (consp x))
       (implies (fn-sf-successes x) (consp x))
       (implies (fn-sf-barriers x) (consp x)))
  :rule-classes ((:forward-chaining :corollary (implies (fn-sf-phase x) (consp x))
                                    :trigger-terms ((fn-sf-phase x)))
                 (:forward-chaining :corollary (implies (fn-sf-frontier x) (consp x))
                                    :trigger-terms ((fn-sf-frontier x)))
                 (:forward-chaining :corollary (implies (fn-sf-frontier-candidate x) (consp x))
                                    :trigger-terms ((fn-sf-frontier-candidate x)))
                 (:forward-chaining :corollary (implies (fn-sf-records x) (consp x))
                                    :trigger-terms ((fn-sf-records x)))
                 (:forward-chaining :corollary (implies (fn-sf-record-candidate x) (consp x))
                                    :trigger-terms ((fn-sf-record-candidate x)))
                 (:forward-chaining :corollary (implies (fn-sf-completion x) (consp x))
                                    :trigger-terms ((fn-sf-completion x)))
                 (:forward-chaining :corollary (implies (fn-sf-successes x) (consp x))
                                    :trigger-terms ((fn-sf-successes x)))
                 (:forward-chaining :corollary (implies (fn-sf-barriers x) (consp x))
                                    :trigger-terms ((fn-sf-barriers x))))
  :hints (("Goal" :in-theory (enable fn-sf-phase fn-sf-frontier fn-sf-frontier-candidate fn-sf-records fn-sf-record-candidate fn-sf-completion fn-sf-successes fn-sf-barriers))))

; Every phase below is either observable between host calls or transient
; inside one composed host call (:aborting, :completed).  The kernel has no
; fenced phase for an uncertain refusal, an uncertain known abort, or a lost
; core completion reply: the host never reports those results.
(defun fn-sf-phasep (x)
  (declare (xargs :guard t :verify-guards nil))
  (member-equal x
                '(:ready :reserved
                  :frontier-staged :frontier-data-durable :frontier-attempted
                  :record-staged :record-data-durable :aborting
                  :record-attempted :completing :completed
                  :replaying :recovering :fault
                  :fenced-frontier :fenced-record :fenced-recovery)))

(defun fn-sf-fencedp (s)
  (declare (xargs :guard t :verify-guards nil))
  (member-equal (fn-sf-phase s)
                '(:fenced-frontier :fenced-record :fenced-recovery)))

(defun fn-sf-pairp (x)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp x) (natp (car x)) (natp (cdr x))))

(defun fn-sf-record-pair (record)
  (declare (xargs :guard t :verify-guards nil))
  (cons (fn-store-event-sequence record) (fn-store-event-txid record)))

; Internal guard domain for the txid fold.  It adds no semantic validity rule;
; the stronger ordered record-list predicate remains the storage invariant.
(defun fn-sf-record-valuesp (records)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (and (fn-store-event-p (car records))
           (fn-sf-record-valuesp (cdr records)))
    (null records)))

(defun fn-sf-next-lower (records lower)
  (declare (xargs :guard (and (fn-sf-record-valuesp records)
                              (natp lower))
                  :verify-guards nil))
  (if (consp records)
      (fn-sf-next-lower (cdr records) (1+ (fn-store-event-txid (car records))))
    lower))

; Sequence numbers are contiguous.  Acceptance txids are strictly increasing,
; may have gaps, and are all below the durable allocator frontier.
(defun fn-sf-record-listp (records sequence lower frontier)
  (declare (xargs :guard (and (natp sequence) (natp lower) (natp frontier))
                  :verify-guards nil))
  (if (consp records)
      (let ((record (car records)))
        (and (fn-store-event-p record)
             (equal (fn-store-event-sequence record) sequence)
             (<= lower (fn-store-event-txid record))
             (< (fn-store-event-txid record) frontier)
             (equal (fn-store-event-generation record) (fn-store-event-txid record))
             (fn-sf-record-listp (cdr records) (1+ sequence)
                                 (1+ (fn-store-event-txid record)) frontier)))
    (null records)))

(defun fn-sf-candidatep (record records frontier)
  (declare (xargs :guard (and (fn-sf-record-valuesp records)
                              (natp frontier))
                  :verify-guards nil))
  (and (fn-store-event-p record)
       (equal (fn-store-event-sequence record) (len records))
       (equal (1+ (fn-store-event-txid record)) frontier)
       (<= (fn-sf-next-lower records 0) (fn-store-event-txid record))
       (equal (fn-store-event-generation record) (fn-store-event-txid record))))

(defun fn-sf-record-has-pairp (pair records)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (or (equal pair (fn-sf-record-pair (car records)))
          (fn-sf-record-has-pairp pair (cdr records)))
    nil))

(defun fn-sf-success-listp (successes records)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp successes)
      (and (fn-sf-pairp (car successes))
           (fn-sf-record-has-pairp (car successes) records)
           (fn-sf-success-listp (cdr successes) records))
    (null successes)))

(defun fn-sf-frontier-phasep (phase)
  (declare (xargs :guard t :verify-guards nil))
  (member-equal phase
                '(:frontier-staged :frontier-data-durable
                  :frontier-attempted :fenced-frontier)))

(defun fn-sf-record-phasep (phase)
  (declare (xargs :guard t :verify-guards nil))
  (member-equal phase
                '(:record-staged :record-data-durable :aborting
                  :record-attempted :fenced-record)))

(defun fn-sf-completion-phasep (phase)
  (declare (xargs :guard t :verify-guards nil))
  (member-equal phase '(:completing :completed)))

(defun fn-sf-phase-shapep (s)
  (declare
   (xargs :guard
          (and (fn-sf-phasep (fn-sf-phase s))
               (fn-record-uint32p (fn-sf-frontier s))
               (fn-sf-record-listp (fn-sf-records s) 0 0
                                   (fn-sf-frontier s))
               (natp (fn-sf-barriers s)))
          :verify-guards nil))
  (let ((phase (fn-sf-phase s))
        (fc (fn-sf-frontier-candidate s))
        (rc (fn-sf-record-candidate s))
        (completion (fn-sf-completion s))
        (barriers (fn-sf-barriers s)))
    (cond
     ((equal phase :ready)
      (and (null fc) (null rc) (null completion)
           (equal barriers *fn-sf-recovery-barrier-count*)))
     ((equal phase :reserved)
      (and (null fc) (null rc) (null completion)
           (posp (fn-sf-frontier s))
           (equal barriers *fn-sf-recovery-barrier-count*)))
     ((fn-sf-frontier-phasep phase)
      (and (fn-record-uint32p fc)
           (equal fc (1+ (fn-sf-frontier s)))
           (null rc) (null completion)
           (equal barriers *fn-sf-recovery-barrier-count*)))
     ((fn-sf-record-phasep phase)
      (and (null fc) (fn-sf-candidatep rc (fn-sf-records s)
                                         (fn-sf-frontier s))
           (null completion)
           (equal barriers *fn-sf-recovery-barrier-count*)))
     ((fn-sf-completion-phasep phase)
      (and (null fc) (null rc) (fn-sf-pairp completion)
           (fn-sf-record-has-pairp completion (fn-sf-records s))
           (equal barriers *fn-sf-recovery-barrier-count*)))
     ((equal phase :replaying)
      (and (null fc) (null rc) (null completion) (equal barriers 0)))
     ((equal phase :recovering)
      (and (null fc) (null rc) (null completion)
           (< barriers *fn-sf-recovery-barrier-count*)))
     ((equal phase :fenced-recovery)
      (and (null fc) (null rc) (null completion)
           (< barriers *fn-sf-recovery-barrier-count*)))
     ((equal phase :fault)
      (and (null fc) (null rc) (null completion)))
     (t nil))))

(defun fn-sf-statep (s)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-sf-shapep s)
       (fn-sf-phasep (fn-sf-phase s))
       (fn-record-uint32p (fn-sf-frontier s))
       (fn-sf-record-listp (fn-sf-records s) 0 0 (fn-sf-frontier s))
       (fn-sf-success-listp (fn-sf-successes s) (fn-sf-records s))
       (natp (fn-sf-barriers s))
       (<= (fn-sf-barriers s) *fn-sf-recovery-barrier-count*)
       (fn-sf-phase-shapep s)))

(defun fn-sf-initial-state ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-sf-make :ready 0 nil nil nil nil nil
              *fn-sf-recovery-barrier-count*))

; -----------------------------------------------------------------------------
; Durable allocator replacement.

(defun fn-sf-start-frontier (s)
  (declare (xargs :guard (fn-sf-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sf-statep s) :exec t) (equal (fn-sf-phase s) :ready)
           (< (fn-sf-frontier s) *fn-sf-max-uint*))
      (fn-sf-make :frontier-staged (fn-sf-frontier s)
                  (1+ (fn-sf-frontier s)) (fn-sf-records s) nil nil
                  (fn-sf-successes s) (fn-sf-barriers s))
    s))

; :known-fail is reported by the host for a staging failure before any
; replacement attempt (tools/run_store.py advance_frontier, OSError branch).
(defun fn-sf-frontier-file-result (s result)
  (declare (xargs :guard (fn-sf-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sf-statep s) :exec t) (equal (fn-sf-phase s) :frontier-staged))
      (cond
       ((equal result :ok)
        (fn-sf-make :frontier-data-durable (fn-sf-frontier s)
                    (fn-sf-frontier-candidate s) (fn-sf-records s) nil nil
                    (fn-sf-successes s) (fn-sf-barriers s)))
       ((equal result :known-fail)
        (fn-sf-make :ready (fn-sf-frontier s) nil (fn-sf-records s) nil nil
                    (fn-sf-successes s) (fn-sf-barriers s)))
       (t s))
    s))

(defun fn-sf-frontier-replace-result (s result)
  (declare (xargs :guard (fn-sf-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sf-statep s) :exec t)
           (equal (fn-sf-phase s) :frontier-data-durable))
      (cond
       ((equal result :ok)
        (fn-sf-make :frontier-attempted (fn-sf-frontier s)
                    (fn-sf-frontier-candidate s) (fn-sf-records s) nil nil
                    (fn-sf-successes s) (fn-sf-barriers s)))
       ((equal result :error)
        (fn-sf-make :fenced-frontier (fn-sf-frontier s)
                    (fn-sf-frontier-candidate s) (fn-sf-records s) nil nil
                    (fn-sf-successes s) (fn-sf-barriers s)))
       (t s))
    s))

(defun fn-sf-frontier-dir-result (s result)
  (declare (xargs :guard (fn-sf-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sf-statep s) :exec t) (equal (fn-sf-phase s) :frontier-attempted))
      (cond
       ((equal result :ok)
        (fn-sf-make :reserved (fn-sf-frontier-candidate s) nil
                    (fn-sf-records s) nil nil (fn-sf-successes s)
                    (fn-sf-barriers s)))
       ((equal result :error)
        (fn-sf-make :fenced-frontier (fn-sf-frontier s)
                    (fn-sf-frontier-candidate s) (fn-sf-records s) nil nil
                    (fn-sf-successes s) (fn-sf-barriers s)))
       (t s))
    s))

; -----------------------------------------------------------------------------
; Whole-record publication.  Replay is the semantic admission check.

(defun fn-sf-replay-node (groups capacity records frontier)
  (declare (xargs :guard t :verify-guards nil))
  (let ((answer (fn-replay groups capacity records)))
    (if (and (fn-replay-okp answer)
             (fn-replay-advance-okp (fn-replay-result-node answer) frontier))
        (fn-replay-advance-txid (fn-replay-result-node answer) frontier)
      nil)))

(defun fn-sf-history-recoverablep (groups capacity records frontier)
  (declare (xargs :guard t :verify-guards nil))
  (let ((node (fn-sf-replay-node groups capacity records frontier)))
    (and (consp node) (fn-node-statep node)
         (equal (fn-state-next-txid (fn-node-acceptance node)) frontier))))

; A synchronous semantic refusal consumes the already durable reservation but
; publishes no record.  Invalid or mismatched requests are no-ops.  The host
; reports only a refusal (fn-sn-refuse-reservation); a lost reply is a
; host-side fence followed by crash/recovery, which uses the durable frontier
; without restoring a reservation token.
(defun fn-sf-refuse-reservation (s txid)
  (declare (xargs :guard (fn-sf-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sf-statep s) :exec t) (equal (fn-sf-phase s) :reserved)
           (natp txid) (equal (1+ txid) (fn-sf-frontier s)))
      (fn-sf-make :ready (fn-sf-frontier s) nil (fn-sf-records s) nil nil
                  (fn-sf-successes s) (fn-sf-barriers s))
    s))

(defun fn-sf-prepare-record (s record groups capacity)
  (declare (xargs :guard (fn-sf-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sf-statep s) :exec t) (equal (fn-sf-phase s) :reserved)
           (fn-sf-candidatep record (fn-sf-records s) (fn-sf-frontier s))
           (fn-sf-history-recoverablep
            groups capacity (append (fn-sf-records s) (list record))
            (fn-sf-frontier s)))
      (fn-sf-make :record-staged (fn-sf-frontier s) nil (fn-sf-records s)
                  record nil (fn-sf-successes s) (fn-sf-barriers s))
    s))

; :known-fail here is reached only inside fn-sn-known-abort
; (store-node-resolution.lisp); the host reports a staging failure by calling
; that composed operation, never as a bare file observation.
(defun fn-sf-record-file-result (s result)
  (declare (xargs :guard (fn-sf-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sf-statep s) :exec t) (equal (fn-sf-phase s) :record-staged))
      (cond
       ((equal result :ok)
        (fn-sf-make :record-data-durable (fn-sf-frontier s) nil
                    (fn-sf-records s) (fn-sf-record-candidate s) nil
                    (fn-sf-successes s) (fn-sf-barriers s)))
       ((equal result :known-fail)
        (fn-sf-make :aborting (fn-sf-frontier s) nil (fn-sf-records s)
                    (fn-sf-record-candidate s) nil (fn-sf-successes s)
                    (fn-sf-barriers s)))
       (t s))
    s))

; :aborting is unreachable-in-composition as an observable phase: it is the
; intermediate state inside the single host call fn-sn-known-abort, which
; continues with fn-sf-abort-completion before returning.
(defun fn-sf-prepublish-abort (s)
  (declare (xargs :guard (fn-sf-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sf-statep s) :exec t)
           (equal (fn-sf-phase s) :record-data-durable))
      (fn-sf-make :aborting (fn-sf-frontier s) nil (fn-sf-records s)
                  (fn-sf-record-candidate s) nil (fn-sf-successes s)
                  (fn-sf-barriers s))
    s))

; The composed known abort derives sequence and txid from the bound candidate
; and calls the actual aborted node completion; the kernel step only checks
; that the pair names the staged candidate.
(defun fn-sf-abort-completion (s sequence txid)
  (declare (xargs :guard (fn-sf-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sf-statep s) :exec t) (equal (fn-sf-phase s) :aborting)
           (equal (cons sequence txid)
                  (fn-sf-record-pair (fn-sf-record-candidate s))))
      (fn-sf-make :ready (fn-sf-frontier s) nil (fn-sf-records s) nil nil
                  (fn-sf-successes s) (fn-sf-barriers s))
    s))

(defun fn-sf-record-link-result (s result)
  (declare (xargs :guard (fn-sf-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sf-statep s) :exec t)
           (equal (fn-sf-phase s) :record-data-durable))
      (cond
       ((equal result :ok)
        (fn-sf-make :record-attempted (fn-sf-frontier s) nil
                    (fn-sf-records s) (fn-sf-record-candidate s) nil
                    (fn-sf-successes s) (fn-sf-barriers s)))
       ((equal result :error)
        (fn-sf-make :fenced-record (fn-sf-frontier s) nil
                    (fn-sf-records s) (fn-sf-record-candidate s) nil
                    (fn-sf-successes s) (fn-sf-barriers s)))
       (t s))
    s))

(defun fn-sf-record-dir-result (s result)
  (declare (xargs :guard (fn-sf-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sf-statep s) :exec t) (equal (fn-sf-phase s) :record-attempted))
      (cond
       ((equal result :ok)
        (let ((record (fn-sf-record-candidate s)))
          (fn-sf-make :completing (fn-sf-frontier s) nil
                      (append (fn-sf-records s) (list record)) nil
                      (fn-sf-record-pair record) (fn-sf-successes s)
                      (fn-sf-barriers s))))
       ((equal result :error)
        (fn-sf-make :fenced-record (fn-sf-frontier s) nil
                    (fn-sf-records s) (fn-sf-record-candidate s) nil
                    (fn-sf-successes s) (fn-sf-barriers s)))
       (t s))
    s))

; The adapter's mutation gate is already closed in :completing.  The only
; kernel step out of it is the exact matching completion performed by
; fn-sn-finish; a lost or rejected reply to that call is a host-side fence with
; the kernel left in :completing, resolved by crash/recovery.
; :completed is unreachable-in-composition as an observable phase: fn-sn-finish
; continues with fn-sf-emit-success in the same host call.
(defun fn-sf-core-completion (s sequence txid)
  (declare (xargs :guard (fn-sf-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sf-statep s) :exec t) (equal (fn-sf-phase s) :completing)
           (equal (cons sequence txid) (fn-sf-completion s)))
      (fn-sf-make :completed (fn-sf-frontier s) nil (fn-sf-records s) nil
                  (fn-sf-completion s) (fn-sf-successes s)
                  (fn-sf-barriers s))
    s))

(defun fn-sf-emit-success (s sequence txid)
  (declare (xargs :guard (fn-sf-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sf-statep s) :exec t) (equal (fn-sf-phase s) :completed)
           (equal (cons sequence txid) (fn-sf-completion s)))
      (fn-sf-make :ready (fn-sf-frontier s) nil (fn-sf-records s) nil nil
                  (append (fn-sf-successes s) (list (cons sequence txid)))
                  (fn-sf-barriers s))
    s))

; unreachable-in-composition: fn-sn-finish performs fn-sf-core-completion and
; fn-sf-emit-success in one host call, so no host path reaches :completed and
; then drops the success.  A reply lost after fn-sn-finish returns is a crash
; from :ready with the pair already in the ghost history (the core-durable cut
; in tests/store_crash_child.py).  The definition is retained because other
; books name it in theory lists; it is not evidence for any host claim.
(defun fn-sf-lose-success (s sequence txid)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sf-statep s) (equal (fn-sf-phase s) :completed)
           (equal (cons sequence txid) (fn-sf-completion s)))
      (fn-sf-make :ready (fn-sf-frontier s) nil (fn-sf-records s) nil nil
                  (fn-sf-successes s) (fn-sf-barriers s))
    s))

; -----------------------------------------------------------------------------
; Crash selection and recovery.  Choices describe namespace observations under
; the assumed atomic old/new replacement and absent/exact-link publication.

(defun fn-sf-crash-choicep (frontier-choice record-choice)
  (declare (xargs :guard t :verify-guards nil))
  (and (or (equal frontier-choice :old) (equal frontier-choice :new))
       (or (equal record-choice :absent) (equal record-choice :present))))

; The new frontier may be visible from :frontier-data-durable onward: the
; host issues os.replace after the file barrier and before it reports the
; replacement result, so a crash in that window (crash point frontier-replace)
; can leave either whole value.  Before :frontier-data-durable no replacement
; can have been issued.
(defun fn-sf-frontier-new-visiblep (s)
  (declare (xargs :guard t :verify-guards nil))
  (member-equal (fn-sf-phase s)
                '(:frontier-data-durable :frontier-attempted :fenced-frontier)))

; The candidate record may be present from :record-data-durable onward: the
; host issues os.link after the file barrier and before it reports the link
; result (crash point final-link).  Before :record-data-durable no final name
; can have been created.
(defun fn-sf-record-present-visiblep (s)
  (declare (xargs :guard t :verify-guards nil))
  (member-equal (fn-sf-phase s)
                '(:record-data-durable :record-attempted :fenced-record)))

; The recovery window (decision D14-b, 2026-09-20).  Process death is not
; power loss: an entry operation issued by the dead process stays pending in
; the kernel's page cache, so the next process's scan of the VIEW reads a
; record whose directory entry is not yet durable, and replays it
; (tools/run_store.py:1100 scans, :1164 replays, host/store-node-host.lisp:39
; builds the :replaying image).  Between that replay and the five recovery
; fences -- fsync_dir(self.transactions) at run_store.py:1187 is the one that
; drains :transactions -- the last record of this state may still be the one
; the previous process left un-fenced, and a crash here drops it.  These are
; the three phases of that window; the five barriers end it at :ready.
(defun fn-sf-recovery-visiblep (s)
  (declare (xargs :guard t :verify-guards nil))
  (member-equal (fn-sf-phase s)
                '(:replaying :recovering :fenced-recovery)))

; The freedom's named premise, decidable from the kernel state alone: a
; recovery-window state that carries no acknowledged outcome.  Store.recover
; runs exactly once per process, at open (run_store.py:1674, run_owner.py:660,
; fn9p.py:428, run_reader.py:313, run_bp_ingress.py:132) and fn-sn-initial
; starts with no success, so on every reachable state of the window the
; success history is empty -- but the predicate must SAY so, because
; fn-sf-crash carries the ghost history across a crash and a :replaying state
; reached that way may hold one.  Without this conjunct the freedom would let
; an image drop a record some earlier process acknowledged, which is exactly
; the D5 guarantee fn-sn-acknowledged-record-survives-observed-reopen states.
; (consp (fn-sf-records s)) keeps the arm off the empty list, where it would
; be the first disjunct restated.
(defun fn-sf-record-rollback-visiblep (s)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-sf-recovery-visiblep s)
       (null (fn-sf-successes s))
       (consp (fn-sf-records s))))

; The frontier half of the recovery freedom (K2f, specs/crash-model-v2.md
; s3.3).  The window is entered with a pending :root rename as well as with a
; pending :transactions link: Store.advance_frontier issues os.replace
; (run_store.py:1305) and the next process's _load_frontier reads the VIEW, so
; the kernel it builds holds old+1 while the durable name still holds old.
; Recovery drains :root at its FOURTH barrier, fsync_dir(self.root)
; (run_store.py:1216), so at recover-replayed and the first three
; recover-barrier cuts a crash rolls the frontier back to old -- a value the
; kernel does not hold anywhere, fn-sf-frontier-candidate being nil in this
; window.
;
; The record-list gate is what makes the rolled-back value a kernel STATE and
; not merely a smaller number, and it is also exactly the reachable window.
; fn-sf-statep requires every record's txid to be below the frontier, and
; advance_frontier reserves txid = old for the record published AFTER the
; rename is durable (fn-sf-candidatep: the candidate's txid is frontier-1).
; So while the rename is pending no record holds txid old, which is
; (fn-sf-record-listp (fn-sf-records s) 0 0 (1- (fn-sf-frontier s))); once
; that record is published the same predicate is FALSE and the frontier can no
; longer roll back.  The gate carries its weight three times: it is what keeps
; fn-sf-recovery-admissible-image-facts true of the rolled-back image, what
; makes fn-sf-crash-frontier-rollback preserve fn-sf-statep, and what makes
; the image replayable at its own frontier
; (fn-snt-recovery-admissible-crash-image-is-recoverable).
;
; The empty success history is here for D14-b's reason in its frontier
; spelling, and it is NOT about losing a record -- rolling the frontier back
; loses none.  It is the only kernel-visible mark that separates a :replaying
; state built by fn-sn-open-observed from THIS PROCESS'S SCAN, where the
; rename may still be pending, from one reached by fn-sf-crash, where the
; model already knows it is not: a crash from :reserved has observed
; (:frontier-directory :ok), so fsync_dir(self.root) returned and the rename
; is durable, and a crash from :frontier-attempted is already covered by
; fn-sf-crash's :old choice (fn-sf-frontier-new-visiblep holds there).
; Without this conjunct the predicate would admit, on a crashed :reserved
; state, an image the same model refutes.  fn-sn-open-observed keeps no ghost
; (fn-sn-open-observed-success-exact-history) and Store.recover runs once per
; process, so the conjunct costs nothing reachable; and
; fn-bs-replay-matches-scan already carries (equal (fn-sf-successes ks) nil),
; so it costs K2 nothing either.  Like D14-b's, it is necessary and not
; sufficient: an empty-success crashed state still satisfies it, and the
; predicate stays an over-approximation, which is why it is a conclusion and
; never a premise.
(defun fn-sf-frontier-rollback-visiblep (s)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-sf-recovery-visiblep s)
       (null (fn-sf-successes s))
       (posp (fn-sf-frontier s))
       (fn-sf-record-listp (fn-sf-records s) 0 0 (1- (fn-sf-frontier s)))))

; The record list with its last element dropped.  Written as its own
; recursion rather than as butlast/take so that the inductions below stay in
; the vocabulary the record-list predicate is written in.
(defun fn-sf-but-last (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (consp (cdr xs)))
      (cons (car xs) (fn-sf-but-last (cdr xs)))
    nil))

; The prefix of a state's record list that NO admissible image can lose: the
; whole list outside the recovery window, and the list without its possibly
; un-fenced tail inside it.  Outside the window this is fn-sf-records itself
; (fn-sf-stable-records-outside-the-window below), so a theorem restated over
; it is not weaker anywhere the old statement was true.
(defun fn-sf-stable-records (s)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-sf-record-rollback-visiblep s)
      (fn-sf-but-last (fn-sf-records s))
    (fn-sf-records s)))

; A-DURABILITY and A-WRITE-ISOLATION as a hypothesis, not a constructor.  An
; observed post-crash image (frontier, records) is admissible for kernel state
; s when the frontier is the stable value or, only while a replacement may
; have been issued, the candidate; and the records are the stable list or,
; only while a link may have been issued, that list extended by the exact
; data-durable candidate.  Theorems about the host's reopen path
; (store-observed.lisp) take this predicate as their premise, and the host's
; own reopen gate is this predicate (fn-own-reopen, owner.lisp:911), so it is
; the RELIANCE predicate: what a consumer of this state may count on.
; fn-sf-crash below is one constructor that satisfies it and shows the premise
; is inhabited; the guarantee comes from the predicate, not from the
; constructor.
;
; D14-b DID NOT WIDEN THIS PREDICATE, and the reason is a counterexample, not
; caution.  Widening it with the recovery freedom below falsifies
; fn-own-reopen-preserves-relation (owner-invariants.lisp): fn-own-relation
; carries fn-own-ledger-durablep, so an owner whose store is a recovery-window
; state with three records and an empty success list may hold a LEDGER naming
; the third -- a pair an EARLIER process completed and acknowledged, which
; this state does not list as its own success.  The widened premise then lets
; fn-own-reopen take the rollback image, and the reopened owner's ledger names
; a record the store no longer holds.  The same shape falsifies
; fn-bprv-crash-image-extends-history.  The kernel's record list is opaque
; about WHICH of its records are fenced; that bit lives in the byte store
; (fn-bs-store-relation's pending list), so no gate on kernel state alone can
; separate "the tail this process replayed" from "a record an earlier process
; made durable".  tests/acl2/store-observed-traces-tests.lisp carries the
; witness.  The freedom is therefore a separate recognizer used as a
; CONCLUSION (specs/crash-model-v2.md K2), never as a reopen premise.
(defun fn-sf-crash-imagep (s frontier records)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-sf-statep s)
       (or (equal frontier (fn-sf-frontier s))
           (and (fn-sf-frontier-new-visiblep s)
                (equal frontier (fn-sf-frontier-candidate s))))
       (or (equal records (fn-sf-records s))
           (and (fn-sf-record-present-visiblep s)
                (equal records (append (fn-sf-records s)
                                       (list (fn-sf-record-candidate s))))))))

; What the PLATFORM may leave behind, which in the recovery window is strictly
; more than what a consumer may rely on (D14-b).  The third arm is the record
; recovery replayed from the view and has not re-fenced.  Every theorem whose
; conclusion is "the image the byte model produces is one the kernel admits"
; -- specs/crash-model-v2.md K2 -- names THIS predicate, and K2 then needs no
; (not (fn-bs-replay-visiblep ks)) hypothesis and K2r no open row: the
; emptiness of the success history is a conjunct of the arm rather than a
; separate obligation, and fn-sf-recovery-admissible-image-facts below proves
; that nothing acknowledged is at risk under it.
(defun fn-sf-recovery-crash-imagep (s frontier records)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-sf-statep s)
       (or (equal frontier (fn-sf-frontier s))
           (and (fn-sf-frontier-new-visiblep s)
                (equal frontier (fn-sf-frontier-candidate s)))
           ; K2f.  The (equal records (fn-sf-records s)) conjunct is the
           ; EXCLUSIVITY of the two rollbacks, not decoration: a recovery
           ; window holds at most one pending authority entry operation, so
           ; the image that loses both the rename and the link is one no
           ; platform can produce.  Outside the window the two phase
           ; predicates fn-sf-frontier-new-visiblep and
           ; fn-sf-record-present-visiblep are disjoint and say the same
           ; thing; inside it the phase no longer does, so the arm says it.
           (and (fn-sf-frontier-rollback-visiblep s)
                (equal frontier (1- (fn-sf-frontier s)))
                (equal records (fn-sf-records s))))
       (or (equal records (fn-sf-records s))
           (and (fn-sf-record-present-visiblep s)
                (equal records (append (fn-sf-records s)
                                       (list (fn-sf-record-candidate s)))))
           (and (fn-sf-record-rollback-visiblep s)
                (equal records (fn-sf-but-last (fn-sf-records s)))))))

(defun fn-sf-crash (s frontier-choice record-choice)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sf-statep s)
           (fn-sf-crash-choicep frontier-choice record-choice))
      (let* ((frontier
              (if (and (fn-sf-frontier-new-visiblep s)
                       (equal frontier-choice :new))
                  (fn-sf-frontier-candidate s)
                (fn-sf-frontier s)))
             (records
              (if (and (fn-sf-record-present-visiblep s)
                       (equal record-choice :present))
                  (append (fn-sf-records s)
                          (list (fn-sf-record-candidate s)))
                (fn-sf-records s))))
        (fn-sf-make :replaying frontier nil records nil nil
                    (fn-sf-successes s) 0))
    s))

; The second constructor, the one that inhabits the recovery arm.  It is a
; SEPARATE function and fn-sf-crash-choicep gains no third choice, which is a
; decision and not an omission: fn-sn-crash (store-node.lisp) is the trace
; language's crash EVENT, and giving it a rollback choice would let a trace
; drop a record an EARLIER process acknowledged.  A reopened state carries no
; success of its own (fn-sn-open-observed-success-exact-history) while its
; record list still holds those records, so the arm's own emptiness conjunct
; does not protect them there, and
; fn-snrt-acknowledged-record-retained-across-observed-reopen -- reopen, then
; any further trace -- would be false.  Physically no such loss exists: an
; acknowledged record is fenced and is never the un-fenced tail; the kernel
; simply cannot see which is which.
(defun fn-sf-crash-rollback (s)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-sf-record-rollback-visiblep s)
      (fn-sf-make :replaying (fn-sf-frontier s) nil
                  (fn-sf-but-last (fn-sf-records s)) nil nil
                  (fn-sf-successes s) 0)
    s))

; The third constructor, the one that inhabits the frontier arm.  Like
; fn-sf-crash-rollback it is a separate function and fn-sf-crash-choicep gains
; no choice: fn-sn-crash is the trace language's crash EVENT, and a trace that
; could roll the frontier back would let a later trace re-issue a txid an
; earlier process had already reserved and published under.  Physically the
; two cannot overlap -- the record that consumes the reservation is published
; only after the rename is durable -- but the record-list gate is what SAYS
; so, and a trace event carries no gate.
(defun fn-sf-crash-frontier-rollback (s)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-sf-frontier-rollback-visiblep s)
      (fn-sf-make :replaying (1- (fn-sf-frontier s)) nil
                  (fn-sf-records s) nil nil
                  (fn-sf-successes s) 0)
    s))

; Recovery uses the observed frontier in the crash image.  No process-cached
; pre-error frontier is an argument to replay.
(defun fn-sf-recover (s groups capacity)
  (declare (xargs :guard (fn-sf-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sf-statep s) :exec t) (equal (fn-sf-phase s) :replaying))
      (if (fn-sf-history-recoverablep groups capacity (fn-sf-records s)
                                      (fn-sf-frontier s))
          (fn-sf-make :recovering (fn-sf-frontier s) nil (fn-sf-records s)
                      nil nil (fn-sf-successes s) 0)
        (fn-sf-make :fault (fn-sf-frontier s) nil (fn-sf-records s)
                    nil nil (fn-sf-successes s) 0))
    s))

(defun fn-sf-recovery-barrier (s result)
  (declare (xargs :guard (fn-sf-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sf-statep s) :exec t) (equal (fn-sf-phase s) :recovering))
      (cond
       ((equal result :ok)
        (let ((next (1+ (fn-sf-barriers s))))
          (fn-sf-make
           (if (equal next *fn-sf-recovery-barrier-count*) :ready :recovering)
           (fn-sf-frontier s) nil (fn-sf-records s) nil nil
           (fn-sf-successes s) next)))
       ((equal result :uncertain)
        (fn-sf-make :fenced-recovery (fn-sf-frontier s) nil
                    (fn-sf-records s) nil nil (fn-sf-successes s)
                    (fn-sf-barriers s)))
       (t s))
    s))

; Guard-only list facts expose the domains already established by the storage
; recognizer.  They add no transition precondition or executable filter.
(local
 (defthm fn-sfg-record-values-are-a-true-list
   (implies (fn-sf-record-valuesp records)
            (true-listp records))))

; The record fields the kernel arithmetic touches, typed once so the guard
; proofs below never open fn-store-event-p -- and neither do these four.
; books/replay states the same facts over the five event kinds one kind at a
; time and exports them; proving them here instead means opening the
; recognizer, which the splitter turns into 28572 and then 15018 subgoals and
; the book misses its per-book limit (measured 2026-09-22, hbox
; certify-20260922T034701Z-2641627).
(local
 (defthm fn-sfg-record-is-a-true-list
   (implies (fn-store-event-p record) (true-listp record))
   :hints (("Goal" :in-theory (disable fn-store-event-p)))))
(local
 (defthm fn-sfg-record-sequence-is-natural
   (implies (fn-store-event-p record) (natp (fn-store-event-sequence record)))
   :rule-classes (:rewrite :forward-chaining :type-prescription)
   :hints (("Goal" :in-theory (disable fn-store-event-p)))))
(local
 (defthm fn-sfg-record-txid-is-natural
   (implies (fn-store-event-p record) (natp (fn-store-event-txid record)))
   :rule-classes (:rewrite :forward-chaining :type-prescription)
   :hints (("Goal" :in-theory (disable fn-store-event-p)))))
(local
 (defthm fn-sfg-record-generation-is-natural
   (implies (fn-store-event-p record) (natp (fn-store-event-generation record)))
   :rule-classes (:rewrite :forward-chaining :type-prescription)
   :hints (("Goal" :in-theory (disable fn-store-event-p)))))
(local
 (defthm fn-sfg-next-lower-is-natural
   (implies (and (fn-sf-record-valuesp records) (natp lower))
            (natp (fn-sf-next-lower records lower)))
   :hints (("Goal" :induct (fn-sf-next-lower records lower)
            :in-theory (disable fn-store-event-p fn-store-event-txid)))))

(local
 (defthm fn-sfg-record-list-implies-values
   (implies (fn-sf-record-listp records sequence lower frontier)
            (fn-sf-record-valuesp records))
   :hints (("Goal" :induct (fn-sf-record-listp
                             records sequence lower frontier)))))

(local
 (defthm fn-sfg-success-list-is-a-true-list
   (implies (fn-sf-success-listp successes records)
            (true-listp successes))))

(local
 (defthm fn-sfg-state-records-have-guard-domain
   (implies (fn-sf-statep s)
            (and (fn-sf-record-valuesp (fn-sf-records s))
                 (true-listp (fn-sf-records s))
                 (true-listp (fn-sf-successes s))))
   :hints (("Goal" :in-theory (enable fn-sf-statep)))))

; The complete executable file kernel is guard verified.  Selectors preserve
; their original total ACL2 semantics through the guarded acceptance helpers.
(verify-guards fn-sf-phasep)
(verify-guards fn-sf-fencedp)
(verify-guards fn-sf-pairp)
(verify-guards fn-sf-record-pair)
(verify-guards fn-sf-record-valuesp)
(verify-guards fn-sf-next-lower)
(verify-guards fn-sf-record-listp)
(verify-guards fn-sf-candidatep
 :hints (("Goal" :in-theory (disable fn-store-event-p fn-store-event-sequence
                                     fn-store-event-txid fn-store-event-generation))))
(verify-guards fn-sf-record-has-pairp)
(verify-guards fn-sf-success-listp)
(verify-guards fn-sf-frontier-phasep)
(verify-guards fn-sf-record-phasep)
(verify-guards fn-sf-completion-phasep)
(verify-guards fn-sf-phase-shapep
 :hints (("Goal" :use fn-sfg-record-list-implies-values)))
(verify-guards fn-sf-statep
 :hints (("Goal" :use fn-sfg-record-list-implies-values)))
(defthm fn-sf-statep-forward-shape
  (implies (fn-sf-statep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-sf-statep fn-sf-shapep))))
(verify-guards fn-sf-initial-state)
(verify-guards fn-sf-start-frontier)
(verify-guards fn-sf-frontier-file-result)
(verify-guards fn-sf-frontier-replace-result)
(verify-guards fn-sf-frontier-dir-result)
(verify-guards fn-sf-replay-node
 :hints (("Goal" :in-theory (enable fn-replay-advance-okp))))
(verify-guards fn-sf-history-recoverablep)
(verify-guards fn-sf-refuse-reservation)
(verify-guards fn-sf-prepare-record
 :hints (("Goal" :use fn-sfg-state-records-have-guard-domain)))
(verify-guards fn-sf-record-file-result)
(verify-guards fn-sf-prepublish-abort)
(verify-guards fn-sf-abort-completion)
(verify-guards fn-sf-record-link-result)
(verify-guards fn-sf-record-dir-result
 :hints (("Goal" :use fn-sfg-state-records-have-guard-domain)))
(verify-guards fn-sf-core-completion)
(verify-guards fn-sf-emit-success
 :hints (("Goal" :use fn-sfg-state-records-have-guard-domain)))
(verify-guards fn-sf-lose-success)
(verify-guards fn-sf-crash-choicep)
(verify-guards fn-sf-frontier-new-visiblep)
(verify-guards fn-sf-record-present-visiblep)
(verify-guards fn-sf-recovery-visiblep)
(verify-guards fn-sf-record-rollback-visiblep)
(verify-guards fn-sf-frontier-rollback-visiblep)
(verify-guards fn-sf-stable-records)
(verify-guards fn-sf-crash-imagep
 :hints (("Goal" :use fn-sfg-state-records-have-guard-domain)))
(verify-guards fn-sf-recovery-crash-imagep
 :hints (("Goal" :use fn-sfg-state-records-have-guard-domain)))
(verify-guards fn-sf-crash
 :hints (("Goal" :use fn-sfg-state-records-have-guard-domain)))
(verify-guards fn-sf-crash-rollback
 :hints (("Goal" :use fn-sfg-state-records-have-guard-domain)))
(verify-guards fn-sf-crash-frontier-rollback
 :hints (("Goal" :use fn-sfg-state-records-have-guard-domain)))
(verify-guards fn-sf-recover)
(verify-guards fn-sf-recovery-barrier)

; -----------------------------------------------------------------------------
; Initial general facts for the kernel.

(defthm fn-sf-initial-state-is-state
  (fn-sf-statep (fn-sf-initial-state)))

(defthm fn-sf-start-frontier-preserves-state
  (implies (fn-sf-statep s)
           (fn-sf-statep (fn-sf-start-frontier s))))

(defthm fn-sf-fenced-rejects-frontier-start
  (implies (and (fn-sf-statep s) (fn-sf-fencedp s))
           (equal (fn-sf-start-frontier s) s)))

(defthm fn-sf-fenced-rejects-record-prepare
  (implies (and (fn-sf-statep s) (fn-sf-fencedp s))
           (equal (fn-sf-prepare-record s record groups capacity) s)))

(defthm fn-sf-success-requires-matching-completion
  (implies (not (and (equal (fn-sf-phase s) :completed)
                     (equal (cons sequence txid) (fn-sf-completion s))))
           (equal (fn-sf-emit-success s sequence txid) s)))

(defthm fn-sf-incomplete-recovery-barrier-is-not-ready
  (implies (and (fn-sf-statep s)
                (equal (fn-sf-phase s) :recovering)
                (< (fn-sf-barriers s) 4))
           (not (equal (fn-sf-phase (fn-sf-recovery-barrier s :ok))
                       :ready))))

(defthm fn-sf-fenced-rejects-success
  (implies (and (fn-sf-statep s) (fn-sf-fencedp s))
           (equal (fn-sf-emit-success s sequence txid) s)))

(defthm fn-sf-frontier-replace-error-fences
  (implies (and (fn-sf-statep s)
                (equal (fn-sf-phase s) :frontier-data-durable))
           (fn-sf-fencedp (fn-sf-frontier-replace-result s :error))))

; A mutation cannot leave :completing except through the exact matching
; completion pair.  This is the kernel half of the completion gate; the
; composed half is fn-sn-new-success-requires-actual-matching-durable-node-completion.
(defthm fn-sf-completing-admits-only-matching-completion
  (implies (and (fn-sf-statep s)
                (equal (fn-sf-phase s) :completing))
           (and (equal (fn-sf-start-frontier s) s)
                (equal (fn-sf-prepare-record s record groups capacity) s)
                (equal (fn-sf-emit-success s sequence txid) s)
                (implies (not (equal (cons sequence txid) (fn-sf-completion s)))
                         (equal (fn-sf-core-completion s sequence txid) s)))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md s2).  Enabled on include: the record
; lemmas, the list-recursive vocabulary (fn-sf-record-listp,
; fn-sf-success-listp, fn-sf-record-has-pairp, fn-sf-record-valuesp,
; fn-sf-next-lower), the small phase predicates and the theorems above.
; Withdrawn: the recognizers, the initial state, replay admission and every
; transition; books/store-files-invariants.lisp opens them locally.
(in-theory (disable fn-sf-statep fn-sf-phase-shapep fn-sf-initial-state
                    fn-sf-start-frontier fn-sf-frontier-file-result
                    fn-sf-frontier-replace-result fn-sf-frontier-dir-result
                    fn-sf-replay-node fn-sf-history-recoverablep
                    fn-sf-refuse-reservation fn-sf-prepare-record
                    fn-sf-record-file-result fn-sf-prepublish-abort
                    fn-sf-abort-completion fn-sf-record-link-result
                    fn-sf-record-dir-result fn-sf-core-completion
                    fn-sf-emit-success fn-sf-lose-success
                    fn-sf-crash-imagep fn-sf-recovery-crash-imagep
                    ; fn-sf-frontier-rollback-visiblep is withdrawn although
                    ; its two siblings (fn-sf-recovery-visiblep,
                    ; fn-sf-record-rollback-visiblep) are not: it carries a
                    ; fn-sf-record-listp recursion over the whole record
                    ; list, and an enabled whole-list recognizer in a
                    ; wholesale vocabulary is the fan this cluster pays for.
                    fn-sf-frontier-rollback-visiblep
                    fn-sf-crash fn-sf-crash-rollback
                    fn-sf-crash-frontier-rollback
                    fn-sf-stable-records fn-sf-recover
                    fn-sf-recovery-barrier))
